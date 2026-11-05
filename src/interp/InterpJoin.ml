open Types
open Values
open ValuesUtils
open TypesUtils
open Cps
open Contexts
open InterpUtils
open InterpBorrows
open InterpAbs
open InterpJoinCore
open InterpReduceCollapse
open InterpMatchCtxs

(** The local logger *)
let log = Logging.join_log

(** Auxiliary helper for [reborrow_ashared_loans_symbolic_borrows] *)
let reborrow_ashared_loans (span : Meta.span) (loop_id : LoopId.id option)
    ~(with_abs_conts : bool) : cm_fun =
 fun ctx0 ->
  let ctx = ctx0 in
  [%ldebug "ctx0:\n" ^ eval_ctx_to_string ctx];

  (* Compute the set of borrows which appear in the abstractions, so that
     we can filter the borrows that we reborrow.
  *)
  let absl =
    List.filter_map
      (function
        | EBinding _ | EFrame -> None
        | EAbs abs -> Some abs)
      ctx.env
  in
  let _, absl_id_maps = compute_absl_ids absl in

  (* Map from the fresh sids to the original symbolic values *)
  let sid_subst = ref [] in

  (* Copy a shared value (see {!InterpBorrowsCore.copy_shared_value}).

     The symbolic values containing (shared) borrows are kept as they are: the
     loan projectors of the owners of their borrows also cover the copy, so
     that ending those owners ends the reborrow. The other symbolic values are
     replaced with fresh symbolic values, in which the region ids belonging to
     the set [rids] are substituted with [nrid]. *)
  let mk_value_with_fresh_sids_no_shared_loans (rids : region_set)
      (nrid : RegionId.id) (v : tvalue) : tvalue =
    let copy_symbolic (sv : symbolic_value) : symbolic_value =
      if ty_has_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty then sv
      else
        let nid = ctx.fresh_symbolic_value_id () in
        let sv0 =
          SymbolicValueId.Map.find sv.sv_id absl_id_maps.sids_to_values
        in
        sid_subst := (nid, sv0) :: !sid_subst;
        let sv_ty =
          Substitute.ty_subst_rids span
            (fun r -> if RegionSet.mem (RVar (Free r)) rids then nrid else r)
            sv.sv_ty
        in
        { sv_id = nid; sv_ty }
    in
    InterpBorrowsCore.copy_shared_value span ctx copy_symbolic v
  in

  let fresh_absl = ref [] in

  (* Auxiliary function to create a new abstraction for a shared value.

     Example:
     ========
     When exploring:
     {[
       abs'0 { SL l s0 }
       x0 -> SB l
       x1 -> SB l
     ]}

     we find the shared borrow [SB l] in x0 and x1, which maps to a loan in a region
     abstraction. We introduce reborrows the following way:
     {[
       abs'0 { SL l s0 }
       abs'2 { SB l, SL {l1} s1 }
       abs'3 { SB l, SL {l2} s2 }
       x0 -> SB l1
       x1 -> SB l2
     ]}

     [rty] is the type with region of the shared value, if it comes from a region
     abstraction.
  *)
  let push_abs_for_shared_value (abs : abs) (sv : tvalue) (rty : ty option)
      (lid : BorrowId.id) (sid : SharedBorrowId.id) :
      BorrowId.id * SharedBorrowId.id =
    (* Create fresh borrows (for the reborrow) *)
    let nlid = ctx.fresh_borrow_id () in
    let nsid = ctx.fresh_shared_borrow_id () in

    (* We need a fresh region for the new abstraction *)
    let nrid = ctx.fresh_region_id () in

    (* Prepare the shared value *)
    let nsv =
      mk_value_with_fresh_sids_no_shared_loans abs.regions.owned nrid sv
    in

    (* Introduce the new abstraction for the shared values.

       If the shared value comes from a region abstraction, we reuse this type
       directly for the projection. Otherwise, we the one that comes from the
       symbolic value. We refresh the regions to make sure in particular that
       erased regions disappear. *)
    let rty =
      let rty =
        match rty with
        | Some rty -> rty
        | None -> sv.ty
      in
      let _, rty = ty_refresh_regions (Some span) ctx.fresh_region_id rty in
      rty
    in

    (* Create the shared loan child *)
    let child_rty = rty in
    let child_av = mk_aignored span child_rty None in

    (* Create the shared loan *)
    let loan_rty = TRef (RVar (Free nrid), rty, RShared) in
    let loan_value = ALoan (ASharedLoan (PNone, nlid, nsv, child_av)) in
    let loan_value = mk_tavalue span loan_rty loan_value in

    (* Create the shared borrow *)
    let borrow_rty = loan_rty in
    let borrow_value = ABorrow (ASharedBorrow (PNone, lid, sid)) in
    let borrow_value = mk_tavalue span borrow_rty borrow_value in

    (* Create the abstraction *)
    let avalues = [ borrow_value; loan_value ] in
    let kind : abs_kind =
      match loop_id with
      | Some loop_id -> Loop loop_id
      | None -> Identity
    in
    let can_end = true in
    let regions : abs_regions =
      { owned = RegionSet.singleton (RVar (Free nrid)) }
    in
    let cont : abs_cont option =
      if with_abs_conts then
        Some
          {
            output = Some (mk_etuple ~borrow_proj:true []);
            input = Some (mk_etuple ~borrow_proj:false []);
          }
      else None
    in
    let fresh_abs =
      {
        abs_id = ctx.fresh_abs_id ();
        kind;
        can_end;
        parents = AbsId.Set.empty;
        ended_subabs = AbsLevelSet.empty;
        regions;
        avalues;
        cont;
      }
    in
    fresh_absl := fresh_abs :: !fresh_absl;
    (nlid, nsid)
  in

  (* Compute the map from borrow id to shared value appearing in a region abstraction -
     we only visit the region abstractions.
     We also store the region type of the shared value when we know it (i.e., for
     abstract shared loans): this is needed to reborrow shared values which
     themselves contain borrows (nested borrows below a shared borrow). *)
  let loan_to_shared_value = ref BorrowId.Map.empty in
  let visitor =
    object
      inherit [_] iter_abs as super

      method! visit_VSharedLoan abs bid sv =
        loan_to_shared_value :=
          BorrowId.Map.add bid (abs, sv, None) !loan_to_shared_value;
        super#visit_VSharedLoan abs bid sv

      method! visit_ASharedLoan abs pm bid sv child =
        (* [child] is the (ignored) region-typed projection of the shared value:
           its type is the region type corresponding to [sv]'s erased type. *)
        loan_to_shared_value :=
          BorrowId.Map.add bid (abs, sv, Some child.ty) !loan_to_shared_value;
        super#visit_ASharedLoan abs pm bid sv child
    end
  in
  List.iter (fun abs -> visitor#visit_abs abs abs) absl;

  (* Explore the shared borrows in the environment, and introduce
     fresh abstractions with reborrows.

     We simply explore the context and call {!push_abs_for_shared_value}
     when necessary.
  *)
  let visitor =
    object
      inherit [_] map_eval_ctx_regular_order as super
      method! visit_abs _ abs = (* Do not explore region abstractions *) abs

      method! visit_VSharedBorrow env bid sid =
        (* Check if the corresponding loan is in a region abstraction *)
        match BorrowId.Map.find_opt bid !loan_to_shared_value with
        | None ->
            (* Do nothing *)
            super#visit_VSharedBorrow env bid sid
        | Some (abs, sv, rty) ->
            (* Check if the region abstraction is frozen *)
            if not abs.can_end then
              let bid, sid = push_abs_for_shared_value abs sv rty bid sid in
              VSharedBorrow (bid, sid)
            else super#visit_VSharedBorrow env bid sid
    end
  in
  let ctx = visitor#visit_eval_ctx () ctx in

  (* Add the abstractions *)
  let fresh_absl = List.map (fun abs -> EAbs abs) !fresh_absl in
  let ctx = { ctx with env = List.append fresh_absl ctx.env } in

  let _, new_ctx_ids_map = compute_ctx_ids ctx in

  (* Synthesize *)
  let cf e =
    (* Add the let-bindings which introduce the fresh symbolic values *)
    List.fold_left
      (fun e (sid, v) ->
        let v = mk_tvalue_from_symbolic_value v in
        let sv = SymbolicValueId.Map.find sid new_ctx_ids_map.sids_to_values in
        SymbolicAst.IntroSymbolic (ctx, None, sv, VaSingleValue v, e))
      e !sid_subst
  in
  Invariants.check_invariants span ctx;
  [%ldebug "resulting ctx:\n" ^ eval_ctx_to_string ctx];
  (ctx, cf)

(** Auxiliary helper for [reborrow_ashared_loans_symbolic_borrows] *)
let reborrow_symbolic_borrows (span : Meta.span) (loop_id : LoopId.id option)
    ~(with_abs_conts : bool) : cm_fun =
 fun ctx0 ->
  let ctx = ctx0 in
  [%ldebug "ctx0:\n" ^ eval_ctx_to_string ctx];

  (* Compute the set of symbolic loans which appear in the frozen abstractions
     (we call them the "frozen loans"), so that we can filter the borrows that
     we reborrow. *)
  let absl =
    List.filter_map
      (function
        | EBinding _ | EFrame -> None
        | EAbs abs when not abs.can_end -> Some abs
        | EAbs _ -> None)
      ctx.env
  in

  (* *)
  let frozen_loans = ref SymbolicValueId.Set.empty in
  let visitor =
    object
      inherit [_] iter_abs as super
      method! visit_tevalue _ _ = ()

      method! visit_AProjLoans abs proj =
        frozen_loans := SymbolicValueId.Set.add proj.proj.sv_id !frozen_loans;
        super#visit_AProjLoans abs proj
    end
  in
  List.iter (fun abs -> visitor#visit_abs abs abs) absl;

  (* Introduce the reborrows *)
  (* The fresh abstractions we introduce for the reborrows *)
  let fresh_absl = ref [] in
  (* The substitution from old symbolic values to fresh symbolic values *)
  let sid_subst = ref [] in

  (* Auxiliary function to create new abstractions for a symbolic borrow *)
  let push_abs_for_symbolic_borrow (sv : symbolic_value) : value =
    (* Create a fresh symbolic value *)
    let nsid = ctx.fresh_symbolic_value_id () in

    (* Refresh the regions appearing in the symbolic value *)
    let region_is_live rid = not (RegionId.Set.mem rid ctx.ended_regions) in
    let region_is_live = Some region_is_live in
    let fresh_regions, ty =
      ty_refresh_regions (Some span) ~region_is_live ctx.fresh_region_id
        sv.sv_ty
    in

    (* Introduce the fresh regions *)
    let push_abs (nr : region) =
      let rty = ty in

      (* Create the symbolic borrow *)
      let borrow : tavalue =
        let proj =
          AProjBorrows
            { proj = { sv_id = sv.sv_id; proj_ty = rty }; loans = [] }
        in
        let value = ASymbolic (PNone, proj) in
        { value; ty = rty }
      in

      (* Create the symbolic loan *)
      let loan : tavalue =
        let value =
          AProjLoans
            {
              proj = { sv_id = nsid; proj_ty = rty };
              consumed = [];
              borrows = [];
            }
        in
        { value = ASymbolic (PNone, value); ty = rty }
      in

      (* Create the abstraction *)
      let avalues = [ borrow; loan ] in
      let kind : abs_kind =
        match loop_id with
        | Some loop_id -> Loop loop_id
        | None -> WithCont
      in
      let can_end = true in
      let regions : abs_regions = { owned = RegionSet.singleton nr } in
      let cont : abs_cont option =
        if with_abs_conts then
          (* Create the symbolic borrow. We introduce borrows/loans only if the
             region projects *mutable* borrows/loans. *)
          if
            ty_has_mut_borrow_for_region_in_set ctx.type_ctx.type_infos
              (RegionSet.singleton nr) rty
          then
            let borrow : tevalue =
              let value =
                EProjBorrows
                  { proj = { sv_id = sv.sv_id; proj_ty = rty }; loans = [] }
              in
              { value = ESymbolic (PNone, value); ty = rty }
            in

            (* Create the symbolic loan *)
            let value =
              EProjLoans
                {
                  proj = { sv_id = nsid; proj_ty = rty };
                  consumed = [];
                  borrows = [];
                }
            in
            let loan : tevalue =
              { value = ESymbolic (PNone, value); ty = rty }
            in
            Some { output = Some borrow; input = Some loan }
          else
            Some
              {
                output = Some (mk_etuple ~borrow_proj:true []);
                input = Some (mk_etuple ~borrow_proj:false []);
              }
        else None
      in
      let fresh_abs =
        {
          abs_id = ctx.fresh_abs_id ();
          kind;
          can_end;
          parents = AbsId.Set.empty;
          ended_subabs = AbsLevelSet.empty;
          regions;
          avalues;
          cont;
        }
      in
      fresh_absl := fresh_abs :: !fresh_absl
    in

    List.iter (fun rid -> push_abs (RVar (Free rid))) fresh_regions;
    (* The static region is not refreshed: if the type contains it (note that it
       may be hidden in ADTs, see {!TypesUtils.adt_has_hidden_static}) we also
       need to introduce an abstraction which reborrows the static part of the
       symbolic value. *)
    if
      ty_has_regions_in_set ctx.type_ctx.type_infos
        (RegionSet.singleton RStatic)
        ty
    then push_abs RStatic;

    let nsv : symbolic_value = { sv_id = nsid; sv_ty = ty } in
    sid_subst := (sv, nsv) :: !sid_subst;
    VSymbolic nsv
  in

  (* Explore the mutable borrows in the environment, and introduce
     fresh abstractions with reborrows.

     We simply explore the context and call {!push_abs_for_symbolic_mut_borrow}
     when necessary.
  *)
  let visitor =
    object
      inherit [_] map_eval_ctx_regular_order as super
      method! visit_abs _ abs = (* Do not explore region abstractions *) abs

      method! visit_VSymbolic env sv =
        (* Check if the corresponding borrows appear in a frozen region abstraction *)
        if SymbolicValueId.Set.mem sv.sv_id !frozen_loans then
          (* Introduce a reborrow *)
          push_abs_for_symbolic_borrow sv
        else super#visit_VSymbolic env sv
    end
  in
  let ctx = visitor#visit_eval_ctx () ctx in

  (* Add the abstractions *)
  let fresh_absl = List.map (fun abs -> EAbs abs) !fresh_absl in
  let ctx = { ctx with env = List.append fresh_absl ctx.env } in

  (* Synthesize *)
  let cf e =
    (* Add the let-bindings which introduce the fresh symbolic values *)
    List.fold_left
      (fun e (sv, nsv) ->
        let sv = mk_tvalue_from_symbolic_value sv in
        SymbolicAst.IntroSymbolic (ctx, None, nsv, VaSingleValue sv, e))
      e !sid_subst
  in
  Invariants.check_invariants span ctx;
  [%ldebug "resulting ctx:\n" ^ eval_ctx_to_string ctx];
  (ctx, cf)

let reborrow_ashared_loans_symbolic_borrows (span : Meta.span)
    (loop_id : LoopId.id option) ~(with_abs_conts : bool) : cm_fun =
 fun ctx0 ->
  let ctx = ctx0 in
  [%ldebug "ctx0:\n" ^ eval_ctx_to_string ctx];
  let ctx, cc = reborrow_ashared_loans span loop_id ~with_abs_conts ctx in

  comp cc (reborrow_symbolic_borrows span loop_id ~with_abs_conts ctx)

let reborrow_ashared_loans_symbolic_borrows_no_synth (span : Meta.span)
    (loop_id : LoopId.id) ~(with_abs_conts : bool) (ctx : eval_ctx) : eval_ctx =
  fst
    (reborrow_ashared_loans_symbolic_borrows span (Some loop_id) ~with_abs_conts
       ctx)

(* TODO: this could be drastically simplified. *)
let compute_ctx_fresh_ordered_symbolic_values (span : Meta.span)
    ~(only_modified_svalues : bool) (ctx : eval_ctx) (fp_ctx : eval_ctx) :
    symbolic_value list =
  let old_ids, _ = compute_ctx_ids ctx in
  let fp_ids, fp_ids_maps = compute_ctx_ids fp_ctx in
  let fresh_sids = SymbolicValueId.Set.diff fp_ids.sids old_ids.sids in

  (* Compute the set of symbolic values which appear inside *frozen* abstractions.
     There are two kinds of values:
     - shared symbolic values (appearing in shared loans): because we introduce
       fresh abstractions and reborrows with {!prepare_ashared_loans}, those
       values are never accessed directly inside the loop iterations: we can
       ignore them (and should, because otherwise it leads to a very ugly
       translation with duplicated, unused values)
     - projections over symbolic values.
       TODO: actually it may happen that a projector inside a fixed abstraction
       gets expanded. We need to update the way we compute joins and check
       whether two contexts are equivalent to make it more general.
  *)
  let sids_in_fixed_abs =
    let fixed_absl =
      List.filter
        (fun (ee : env_elem) ->
          match ee with
          | EBinding _ | EFrame -> false
          | EAbs abs -> not abs.can_end)
        ctx.env
    in

    (* Rem.: as we greedily expand the symbolic values containing borrows, and
       in particular the (mutable/shared) borrows, we could simply list the
       symbolic values appearing in the abstractions: those are necessarily
       shared values. We prefer to be more general, in prevision of later
       changes.
    *)
    let sids = ref SymbolicValueId.Set.empty in
    let visitor =
      object (self)
        inherit [_] iter_env

        method! visit_ASharedLoan register _ _ sv child_av =
          self#visit_tvalue true sv;
          self#visit_tavalue register child_av

        method! visit_AProjLoans register proj =
          let { proj = { sv_id; proj_ty }; consumed; borrows } : aproj_loans =
            proj
          in
          self#visit_symbolic_value_id true sv_id;
          self#visit_ty register proj_ty;
          [%sanity_check] span (consumed = []);
          [%sanity_check] span (borrows = [])
        (*self#visit_list
            (fun register ((s, p) : mconsumed_symb * _) ->
              self#visit_msymbolic_value_id register s.sv_id;
              self#visit_aproj register p)
            register consumed;
          self#visit_list
            (fun register ((s, p) : mconsumed_symb * _) ->
              self#visit_msymbolic_value_id register s.sv_id;
              self#visit_aproj register p)
            register borrows*)

        method! visit_symbolic_value_id register sid =
          if register then sids := SymbolicValueId.Set.add sid !sids
      end
    in
    visitor#visit_env false fixed_absl;
    !sids
  in

  (* Remove the shared symbolic values present in the fixed abstractions -
     see comments for [shared_sids_in_fixed_abs]. *)
  let sids_to_values = fp_ids_maps.sids_to_values in

  (* Also remove the symbolic values which appear inside of projectors in
     fixed abstractions - those are "fixed" and not modified between iterations
     of the loop *)
  [%ltrace
    "- sids_in_fixed_abs:"
    ^ SymbolicValueId.Set.show sids_in_fixed_abs
    ^ "\n- all_sids_to_values: "
    ^ SymbolicValueId.Map.show (symbolic_value_to_string ctx) sids_to_values];

  let sids_to_values =
    SymbolicValueId.Map.filter
      (fun sid _ -> not (SymbolicValueId.Set.mem sid sids_in_fixed_abs))
      sids_to_values
  in

  (* Remove the symbolic values which are not modified, if the option
     [only_modified_input_svalues] is [true] *)
  let sids_to_values =
    if only_modified_svalues then
      SymbolicValueId.Map.filter
        (fun sid _ -> SymbolicValueId.Set.mem sid fresh_sids)
        sids_to_values
    else sids_to_values
  in

  (* List the input symbolic values in proper order.

     We explore the environment, and order the symbolic values in the order
     in which they are found - this way, the symbolic values found in a
     variable [x] which appears before [y] are listed first, for instance.
  *)
  let input_svalues =
    let found_sids = ref SymbolicValueId.Set.empty in
    let ordered_sids = ref [] in

    let visitor =
      object (self)
        inherit [_] iter_env

        (** We lookup the shared values *)
        method! visit_VSharedBorrow env bid _ =
          let open InterpBorrowsCore in
          let v =
            match snd (ctx_lookup_loan span ek_all bid fp_ctx) with
            | Concrete (VSharedLoan (_, v)) -> v
            | Abstract (ASharedLoan (pm, _, v, _)) ->
                [%sanity_check] span (pm = PNone);
                v
            | _ -> [%craise] span "Unreachable"
          in
          self#visit_tvalue env v

        method! visit_VFrozenMutBorrow env bid sid =
          self#visit_VSharedBorrow env bid sid

        method! visit_symbolic_value_id _ id =
          if not (SymbolicValueId.Set.mem id !found_sids) then (
            found_sids := SymbolicValueId.Set.add id !found_sids;
            ordered_sids := id :: !ordered_sids)
      end
    in

    List.iter (visitor#visit_env_elem ()) (List.rev fp_ctx.env);

    List.filter_map
      (fun id -> SymbolicValueId.Map.find_opt id sids_to_values)
      (List.rev !ordered_sids)
  in

  [%ltrace
    "- src context:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false ctx
    ^ "\n- fixed point:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false fp_ctx
    ^ "\n- fresh_sids: "
    ^ SymbolicValueId.Set.show fresh_sids
    ^ "\n- input_svalues: "
    ^ Print.list_to_string (symbolic_value_to_string ctx) input_svalues
    ^ "\n"];

  input_svalues

(** Find a symbolic value in a context, from its id *)
let ctx_find_symbolic_value (ctx : eval_ctx) (sid : SymbolicValueId.id) :
    symbolic_value option =
  let found = ref None in
  let visitor =
    object
      inherit [_] iter_eval_ctx

      method! visit_symbolic_value _ sv =
        if sv.sv_id = sid then found := Some sv
    end
  in
  visitor#visit_eval_ctx () ctx;
  !found

let refresh_non_fixed_abs_ids (_span : Meta.span) (fixed_aids : AbsId.Set.t)
    (ctx : eval_ctx) : eval_ctx * abs_id AbsId.Map.t =
  (* Note that abstraction ids appear both inside of region abstractions
     but also inside of evalues (some evalues refer to region abstractions).
     We have to make sure that we keep things consistent: whenever we refresh
     an id, we remember it. *)
  let fresh_map = ref AbsId.Map.empty in

  let visitor =
    object
      inherit [_] map_eval_ctx

      method! visit_abs_id _ id =
        if AbsId.Set.mem id fixed_aids then id
        else
          match AbsId.Map.find_opt id !fresh_map with
          | Some id -> id
          | None ->
              let nid = ctx.fresh_abs_id () in
              fresh_map := AbsId.Map.add id nid !fresh_map;
              nid
    end
  in
  let ctx = visitor#visit_eval_ctx () ctx in
  (ctx, !fresh_map)

(** A region may be ended in [other] while it is live in [ctx], owned by an
    abstraction (for instance, the region of a function call whose output holds
    borrows in one branch only: the abstraction ends early in the other
    branch). The joined context keeps the abstraction, but the region must
    remain ended for the values coming from [other]: we rename it in [ctx].

    The symbolic values whose types (or projections) mention such a region get
    fresh ids, renamed consistently everywhere in [ctx] (including the
    meta-values): their types change. When we match a branch with the joined
    context, the renamed values of the joined context are fresh, and map to the
    values of the branch.

    In a loop join (with [fresh_abs_kind = Loop _]), the fixed point must be
    computed modulo such a renaming, which we don't support: we only rename the
    regions which no symbolic value mentions. *)
let freshen_regions_ended_in_other (span : Meta.span) (fresh_abs_kind : abs_kind)
    ~(recoverable : bool) (ctx : eval_ctx) (other : eval_ctx) : eval_ctx =
  let owned =
    List.fold_left
      (fun owned (e : env_elem) ->
        match e with
        | EAbs abs ->
            RegionSet.fold
              (fun r owned ->
                match r with
                | RVar (Free rid) -> RegionId.Set.add rid owned
                | _ -> owned)
              abs.regions.owned owned
        | EBinding _ | EFrame -> owned)
      RegionId.Set.empty ctx.env
  in
  let rids =
    RegionId.Set.filter
      (fun rid ->
        RegionId.Set.mem rid other.ended_regions
        && not (RegionId.Set.mem rid ctx.ended_regions))
      owned
  in
  if RegionId.Set.is_empty rids then ctx
  else
    let regions =
      RegionSet.of_list
        (List.map (fun rid -> RVar (Free rid)) (RegionId.Set.elements rids))
    in
    let mentions_rids (ty : ty) : bool =
      ty_has_regions_in_set ctx.type_ctx.type_infos regions ty
    in
    (* The symbolic values whose types mention the regions. A value projected
       at the regions doesn't depend on them (the renaming of the regions
       updates the projection): we use the type of a projection only for the
       values which appear in projections only.
       [~in_ignored]: whether we include the meta-values of the ignored values
       ([AIgnored], and [EIgnored] in the continuations), whose synthesis doesn't
       depend on the regions: they are translated as values, whose types the
       translation erases. *)
    let mentioning_svs ~(in_ignored : bool) =
      let svs = ref SymbolicValueId.Set.empty in
      let typed = ref SymbolicValueId.Set.empty in
      let proj_svs = ref SymbolicValueId.Set.empty in
      let add_proj sv_id proj_ty =
        if mentions_rids proj_ty then
          proj_svs := SymbolicValueId.Set.add sv_id !proj_svs
      in
      let visitor =
        object (self)
          inherit [_] iter_eval_ctx as super

          method! visit_symbolic_value _ sv =
            typed := SymbolicValueId.Set.add sv.sv_id !typed;
            if mentions_rids sv.sv_ty then
              svs := SymbolicValueId.Set.add sv.sv_id !svs

          method! visit_symbolic_proj _ proj = add_proj proj.sv_id proj.proj_ty
          method! visit_esymbolic_proj _ proj = add_proj proj.sv_id proj.proj_ty

          method! visit_mvalue env v = self#visit_tvalue env v
          method! visit_msymbolic_value env sv = self#visit_symbolic_value env sv

          method! visit_AIgnored env mv =
            if in_ignored then super#visit_AIgnored env mv

          method! visit_EIgnored env mv =
            if in_ignored then super#visit_EIgnored env mv
        end
      in
      visitor#visit_eval_ctx () ctx;
      SymbolicValueId.Set.union !svs
        (SymbolicValueId.Set.diff !proj_svs !typed)
    in
    let svs =
      if SymbolicValueId.Set.is_empty (mentioning_svs ~in_ignored:false) then
        SymbolicValueId.Set.empty
      else (
        [%cassert_recover] recoverable span
          (match fresh_abs_kind with
          | Loop _ -> false
          | _ -> true)
          "Unimplemented";
        mentioning_svs ~in_ignored:true)
    in
    let rsubst =
      RegionId.Set.fold
        (fun rid m -> RegionId.Map.add rid (ctx.fresh_region_id ()) m)
        rids RegionId.Map.empty
    in
    let ssubst =
      SymbolicValueId.Set.fold
        (fun sid m ->
          SymbolicValueId.Map.add sid (ctx.fresh_symbolic_value_id ()) m)
        svs SymbolicValueId.Map.empty
    in
    [%ldebug
      "- renamed regions: "
      ^ RegionId.Map.to_string None RegionId.to_string rsubst
      ^ "\n- renamed symbolic values: "
      ^ SymbolicValueId.Map.to_string None SymbolicValueId.to_string ssubst];
    let env =
      Substitute.env_subst_ids
        {
          Substitute.empty_id_subst with
          r_subst =
            (fun rid ->
              Option.value (RegionId.Map.find_opt rid rsubst) ~default:rid);
          ssubst =
            (fun sid ->
              Option.value (SymbolicValueId.Map.find_opt sid ssubst) ~default:sid);
        }
        ctx.env
    in
    { ctx with env }

let join_ctxs (span : Meta.span) (fresh_abs_kind : abs_kind)
    ~(recoverable : bool) ~(with_abs_conts : bool) (ctx0 : eval_ctx)
    (ctx1 : eval_ctx) : join_info_or_update =
  let ctx0 =
    freshen_regions_ended_in_other span fresh_abs_kind ~recoverable ctx0 ctx1
  in
  let ctx1 =
    freshen_regions_ended_in_other span fresh_abs_kind ~recoverable ctx1 ctx0
  in
  (* Debug *)
  [%ltrace
    "- ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx0
    ^ "\n\n- ctx1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx1
    ^ "\n"];

  (* Split the environments in two:
     - we preserve the dummy variables and abstractions which appear in both
       environments: we will match those pairwise. However, for the abstractions:
       we only preserve those which are the same in both abstractions.
     - for the others:
       - we mark the region abstractions with left/right markers
       - we lift the dummy values into region abstractions and mark them as well
  *)
  let dummy_ids0 = ctx_get_dummy_var_ids ctx0 in
  let dummy_ids1 = ctx_get_dummy_var_ids ctx1 in
  let dummy_ids = DummyVarId.Set.inter dummy_ids0 dummy_ids1 in
  let abs_ids = compute_fixed_abs_ids ctx0 ctx1 in

  (* Refresh the non fixed abstraction ids.

     We need to refresh the non-fixed abstraction ids (the ones which do appear,
     while being equal, in both environments) in one of the two contexts,
     because otherwise the join might have twice an abstraction with the same id,
     which is a problem.

     TODO: make the join more general.
  *)
  let ctx0, _ = refresh_non_fixed_abs_ids span abs_ids ctx0 in
  [%ltrace
    "After refreshing the non-fixed abstraction ids of ctx0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:true ctx0];

  let partition (env : env) : env * env =
    List.partition
      (fun (e : env_elem) ->
        match e with
        | EBinding (BVar _, _) ->
            (* All the locals should appear on both sides *) true
        | EBinding (BDummy id, _) -> DummyVarId.Set.mem id dummy_ids
        | EAbs abs -> AbsId.Set.mem abs.abs_id abs_ids
        | EFrame -> true)
      env
  in
  let env0, env0_suffix = partition (List.rev ctx0.env) in
  let env1, env1_suffix = partition (List.rev ctx1.env) in
  [%ldebug
    "\n\n- env0:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false
        { ctx0 with env = List.rev env0 }
    ^ "\n\n- env0_suffix:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false
        { ctx0 with env = List.rev env0_suffix }
    ^ "\n\n- env1:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false
        { ctx1 with env = List.rev env1 }
    ^ "\n\n- env1_suffix:\n"
    ^ eval_ctx_to_string ~span:(Some span) ~filter:false
        { ctx1 with env = List.rev env1_suffix }
    ^ "\n"];

  let nabs = ref [] in

  let symbolic_to_value = ref SymbolicValueId.Map.empty in
  let module S : MatchJoinState = struct
    let fresh_abs_kind = fresh_abs_kind
    let span = span
    let nabs = nabs
    let with_abs_conts = with_abs_conts
    let symbolic_to_value = symbolic_to_value
    let recover = recoverable
  end in
  let module JM = MakeJoinMatcher (S) in
  let module M = MakeMatcher (JM) in
  let pop_var = env_pop_var (fun _ -> [%internal_error] span) in
  let pop_dummy = env_pop_dummy (fun _ -> [%internal_error] span) in
  let pop_abs = env_pop_abs (fun _ -> [%internal_error] span) in

  (* Rem.: this function raises exceptions.

     We match on the first environment, then pop the corresponding binding
     from the second environment.
  *)
  let rec join_prefixes (env0 : env) (env1 : env) : env =
    match env0 with
    | (EBinding (BDummy b0, v0) as var0) :: env0' ->
        let v1, env1' = pop_dummy b0 env1 in
        let var1 = EBinding (BDummy b0, v1) in

        (* Debug *)
        [%ldebug
          "join_prefixes: BDummys:\n- value0:\n"
          ^ env_elem_to_string span ctx0 var0
          ^ "\n\n- value1:\n"
          ^ env_elem_to_string span ctx1 var1
          ^ "\n"];

        (* Match the values *)
        let b = b0 in
        let v = M.match_tvalues ctx0 ctx1 v0 v1 in
        let var = EBinding (BDummy b, v) in
        (* Continue *)
        var :: join_prefixes env0' env1'
    | (EBinding (BVar b0, v0) as var0) :: env0' ->
        let v1, env1' = pop_var b0 env1 in
        let var1 = EBinding (BVar b0, v1) in

        (* Debug *)
        [%ldebug
          "join_prefixes: BVars:\n- value0:\n"
          ^ env_elem_to_string span ctx0 var0
          ^ "\n\n- value1:\n"
          ^ env_elem_to_string span ctx1 var1
          ^ "\n"];

        (* Variable bindings *must* be in the prefix and consequently their
           ids must be the same *)
        (* Match the values *)
        let b = b0 in
        let v = M.match_tvalues ctx0 ctx1 v0 v1 in
        let var = EBinding (BVar b, v) in
        (* Continue *)
        var :: join_prefixes env0' env1'
    | EAbs abs0 :: env0' ->
        let abs1, env1' = pop_abs abs0.abs_id env1 in

        (* Debug *)
        [%ldebug
          "join_prefixes:\n- abs0:\n"
          ^ abs_to_string span ctx0 abs0
          ^ "\n\n- abs1:\n"
          ^ abs_to_string span ctx1 abs1
          ^ "\n"];

        (* Fixed abstractions should be equal.

           Note that the presence of the field [abs.original_parents] used to make
           this test fail when some abstraction ids was refreshed by
           [refresh_non_fixed_abs_ids] (we since remove the field).

           Note that we ignore the continuation expressions: when computing fixed
           points we might remove/add continuations while the presence/absence
           shouldn't have an impact on the way we match/unify contexts.

           The parents may differ: a parent which is not fixed got a fresh id in
           [ctx0]. The joined abstraction has the parents of both (the
           collapse merges them). *)
        [%sanity_check] span
          (equal_abs
             { abs0 with cont = None; parents = AbsId.Set.empty }
             { abs1 with cont = None; parents = AbsId.Set.empty });
        let abs =
          EAbs { abs0 with parents = AbsId.Set.union abs0.parents abs1.parents }
        in
        (* Continue *)
        abs :: join_prefixes env0' env1'
    | [] ->
        if env1 = [] then []
        else
          [%craise] span
            ("Internal error: please file an issue.\n\
              Could not match:\n\
              - env0:\n"
            ^ eval_ctx_to_string ~span:(Some span) ~filter:false
                { ctx0 with env = List.rev env0 }
            ^ "\n\n- env1:\n"
            ^ eval_ctx_to_string ~span:(Some span) ~filter:false
                { ctx1 with env = List.rev env1 })
    | _ -> [%internal_error] span
  in

  try
    (* Remove the frame delimiter (the first element of an environment is a frame delimiter) *)
    let env0, env1 =
      match (env0, env1) with
      | EFrame :: env0, EFrame :: env1 -> (env0, env1)
      | _ -> [%craise] span "Unreachable"
    in

    (* Match the prefixes *)
    let prefix = join_prefixes env0 env1 in

    (* We do not match the suffixes: we transform the dummy values into
       region abstractions and add projection markers. *)
    let suffix =
      let env0 = env0_suffix in
      let env1 = env1_suffix in
      (* Debug *)
      [%ldebug
        "join_suffixes:" ^ "\n\n- ctx0:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false
            { ctx0 with env = List.rev env0 }
        ^ "\n\n- ctx1:\n"
        ^ eval_ctx_to_string ~span:(Some span) ~filter:false
            { ctx1 with env = List.rev env1 }
        ^ "\n"];

      (* Add projection marker to all abstractions in the left and right environments.
         Note that we destructure the fresh abstractions - TODO: make the merge more
         general *)
      let destructure_abs ctx =
        destructure_abs span fresh_abs_kind ~can_end:true
          ~destructure_shared_values:true ctx
      in
      let add_marker ctx (pm : proj_marker) (ee : env_elem) : env_elem list =
        match ee with
        | EAbs abs ->
            [
              (let abs = destructure_abs ctx abs in
               EAbs (abs_add_marker span ctx pm abs));
            ]
        | EBinding (BDummy _, v) ->
            (* Transform into a region abstraction and project *)
            let absl =
              convert_value_to_abstractions span fresh_abs_kind ~can_end:true
                ctx v
            in
            let absl = List.map (destructure_abs ctx) absl in
            List.map (fun abs -> EAbs (abs_add_marker span ctx pm abs)) absl
        | EBinding (BVar _, _) | EFrame -> [%internal_error] span
      in

      let env0 = List.flatten (List.map (add_marker ctx0 PLeft) env0) in
      let env1 = List.flatten (List.map (add_marker ctx1 PRight) env1) in

      (* Concatenate the suffixes and append the abstractions introduced while
       joining the prefixes *)
      let absl = List.map (fun abs -> EAbs abs) (List.rev !nabs) in
      List.concat [ env0; env1; absl ]
    in

    let env = List.rev (EFrame :: (prefix @ suffix)) in

    (* Construct the joined context - of course, the type, fun, etc. contexts
     * should be the same in the two contexts *)
    let {
      type_ctx;
      crate;
      fun_ctx;
      region_groups;
      type_vars;
      const_generic_vars;
      const_generic_vars_map;
      env = _;
      ended_regions = ended_regions0;
      _;
    } =
      ctx0
    in
    let {
      type_ctx = _;
      crate = _;
      fun_ctx = _;
      region_groups = _;
      type_vars = _;
      const_generic_vars = _;
      const_generic_vars_map = _;
      env = _;
      ended_regions = ended_regions1;
      _;
    } =
      ctx1
    in
    let ended_regions = RegionId.Set.union ended_regions0 ended_regions1 in
    let ctx : eval_ctx =
      {
        ctx0 with
        crate;
        type_ctx;
        fun_ctx;
        region_groups;
        type_vars;
        const_generic_vars;
        const_generic_vars_map;
        env;
        ended_regions;
      }
    in
    (* A shared loan of one side only disappears from the join, while the
       values it contains may be below a shared loan of both sides: we freeze
       them again *)
    let ctx = InterpBorrowsCore.ctx_freeze_mut_borrows_in_shared_values ctx in
    let join_info : join_info =
      { joined_ctx = ctx; symbolic_to_value = !symbolic_to_value }
    in

    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_unique_abs_ids span ctx;

    Ok join_info
  with ValueMatchFailure e -> Error e

(** The abstraction of a context containing the projected shared borrow of id
    [sid] (see {!InterpReduceCollapse.MarkedObservation}) *)
let observing_abs (sid : shared_borrow_id) (ctx : eval_ctx) : abs option =
  let observes (abs : abs) =
    let visitor =
      object
        inherit [_] iter_abs
        method! visit_AsbBorrow _ _ sid' = if sid' = sid then raise Utils.Found
      end
    in
    try
      visitor#visit_abs () abs;
      false
    with Utils.Found -> true
  in
  List.find_map
    (fun (e : env_elem) ->
      match e with
      | EAbs abs when observes abs -> Some abs
      | _ -> None)
    ctx.env

(** End the abstraction of a context containing the projected shared borrow of
    id [sid], with [end_abs]. The failure to do so is recoverable. *)
let end_observing_abs (span : Meta.span) ~(recoverable : bool)
    (sid : shared_borrow_id) (end_abs : AbsId.id -> eval_ctx -> eval_ctx * 'a)
    (ctx : eval_ctx) : eval_ctx * 'a =
  match observing_abs sid ctx with
  | Some abs when abs.can_end ->
      let ctx0 = ctx in
      let ctx, x = end_abs abs.abs_id ctx in
      (* Make sure we made progress *)
      [%cassert_recover] recoverable span
        (observing_abs sid ctx = None)
        "Could not end the abstraction of an observation";
      (* Ending the abstraction must not invalidate the values of the local
         variables (they may be used after the join) *)
      let locals (ctx : eval_ctx) =
        List.filter_map
          (fun (e : env_elem) ->
            match e with
            | EBinding (BVar var, v) -> Some (var.index, v)
            | _ -> None)
          ctx.env
      in
      [%cassert_recover] recoverable span
        (List.for_all
           (fun (lid, (v : tvalue)) ->
             bottom_in_value ctx0.ended_regions v
             || match List.assoc_opt lid (locals ctx) with
                | Some v' -> not (bottom_in_value ctx.ended_regions v')
                | None -> true)
           (locals ctx0))
        "Could not end the abstraction of an observation without invalidating \
         a local variable";
      (ctx, x)
  | _ ->
      [%craise_recover] recoverable span
        "Could not end the abstraction of an observation"

(** A local which isn't initialized ([⊥]) in one of the contexts reaching a
    join can't be read after the join: Rust only reads the locals which are
    initialized on every path. If it has no drop glue either (it only contains
    scalars and shared borrows), nothing uses its value after the join: in the
    other contexts, we move its value to a dummy variable, so that the
    abstractions which only its borrows keep alive can end before we join (see
    {!InterpBorrows.simplify_dummy_values_useless_abs}). *)
let drop_locals_uninit_in_some_ctx (ctxl : eval_ctx list) : eval_ctx list =
  let rec drop_trivial (ty : ty) : bool =
    match ty with
    | TScalar _ | TRef (_, _, RShared) -> true
    | TAdt { builtin = Some TTuple; generics; _ } ->
        List.for_all drop_trivial generics.types
    | _ -> false
  in
  let frame_locals (ctx : eval_ctx) : (real_var_binder * tvalue) list =
    let rec collect env =
      match env with
      | [] | EFrame :: _ -> []
      | EBinding (BVar var, v) :: env -> (var, v) :: collect env
      | (EBinding (BDummy _, _) | EAbs _) :: env -> collect env
    in
    collect ctx.env
  in
  let uninit =
    List.fold_left
      (fun uninit ctx ->
        List.fold_left
          (fun uninit ((var : real_var_binder), (v : tvalue)) ->
            if v.value = VBottom && drop_trivial v.ty then
              Expressions.LocalId.Set.add var.index uninit
            else uninit)
          uninit (frame_locals ctx))
      Expressions.LocalId.Set.empty ctxl
  in
  let drop (ctx : eval_ctx) : eval_ctx =
    let dropped = ref [] in
    let rec update env =
      match env with
      | [] -> []
      | EFrame :: _ -> env
      | EBinding (BVar var, v) :: env
        when Expressions.LocalId.Set.mem var.index uninit && v.value <> VBottom ->
          dropped := v :: !dropped;
          EBinding (BVar var, { v with value = VBottom }) :: update env
      | e :: env -> e :: update env
    in
    let ctx = { ctx with env = update ctx.env } in
    ctx_push_fresh_dummy_vars ctx (List.rev !dropped)
  in
  if Expressions.LocalId.Set.is_empty uninit then ctxl else List.map drop ctxl

(** In the contexts reaching a join, align the abstractions which exist before
    the branching ([fixed_aids]): a branch may have expanded a struct (or tuple)
    value shared by one of them, which another branch left symbolic. We expand
    it identically in the other branch, reusing the symbolic values of the
    fields when they are still symbolic. Values under shared loans are
    immutable: the fields are the ones the expansion introduced, possibly
    expanded further (which a later round aligns). We only align values without
    borrows. Similarly, a branch may have shared a part of such a value: we
    introduce the shared loan, without borrows, in the other branches.

    Returns the updated contexts, with the expansions to synthesize at the end
    of their branches. *)
let align_fixed_abs_expansions (span : Meta.span) (fixed_aids : AbsId.Set.t)
    (ctxl : eval_ctx list) : (eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)) list =
  (* The shared values of an abstraction *)
  let shared_values (abs : abs) : tvalue list =
    let values = ref [] in
    let visitor =
      object
        inherit [_] iter_abs as super

        method! visit_ASharedLoan env pm lid sv child =
          values := sv :: !values;
          super#visit_tavalue env child
      end
    in
    visitor#visit_abs () abs;
    List.rev !values
  in
  let expandable (ctx : eval_ctx) (sv : symbolic_value) : bool =
    (match sv.sv_ty with
    | TAdt { id; builtin = None; _ } -> (
        match (ctx_lookup_type_decl span ctx id).kind with
        | Struct _ -> true
        | _ -> false)
    | TAdt { builtin = Some TTuple; _ } -> true
    | _ -> false)
    && not (ty_has_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty)
  in
  (* Find a value symbolic in [a] and expanded in [b] *)
  let rec find (ctx_a : eval_ctx) (a : tvalue) (b : tvalue) :
      (symbolic_value * tvalue list) option =
    match (a.value, b.value) with
    | VSymbolic sv, VAdt { variant_id = None; fields } when expandable ctx_a sv
      ->
        Some (sv, fields)
    | VAdt fa, VAdt fb
      when fa.variant_id = fb.variant_id
           && List.length fa.fields = List.length fb.fields ->
        List.find_map
          (fun (a, b) -> find ctx_a a b)
          (List.combine fa.fields fb.fields)
    | VLoan (VSharedLoan (_, a)), VLoan (VSharedLoan (_, b)) -> find ctx_a a b
    | VLoan (VSharedLoan (_, a)), _ -> find ctx_a a b
    | _, VLoan (VSharedLoan (_, b)) -> find ctx_a a b
    | VBorrow (VMutBorrow (_, a)), VBorrow (VMutBorrow (_, b)) -> find ctx_a a b
    | _ -> None
  in
  let find_in_abs (ctx_a : eval_ctx) (ctx_b : eval_ctx) (aid : abs_id) =
    match (ctx_lookup_abs_opt ctx_a aid, ctx_lookup_abs_opt ctx_b aid) with
    | Some abs_a, Some abs_b ->
        let va = shared_values abs_a and vb = shared_values abs_b in
        if List.length va = List.length vb then
          List.find_map (fun (a, b) -> find ctx_a a b) (List.combine va vb)
        else None
    | _ -> None
  in
  (* The expansion of [sv] in [ctx_a] matching the fields of [ctx_b] *)
  let expansion (ctx_a : eval_ctx) (fields : tvalue list) : symbolic_expansion
      =
    let rec strip (v : tvalue) : tvalue =
      match v.value with
      | VLoan (VSharedLoan (_, v)) -> strip v
      | _ -> v
    in
    let field_value (v : tvalue) : symbolic_value =
      let v = strip v in
      match v.value with
      | VSymbolic sv when not (symbolic_value_id_in_ctx sv.sv_id ctx_a) -> sv
      | _ -> mk_fresh_symbolic_value span ctx_a v.ty
    in
    SeAdt (None, List.map field_value fields)
  in
  (* Wrap a value of [a] in a shared loan of [b] which [ctx_a] doesn't have *)
  let rec wrap (ctx_a : eval_ctx) (a : tvalue) (b : tvalue) : tvalue option =
    let rewrap f a' = Option.map (fun a' -> { a with value = f a' }) a' in
    match (a.value, b.value) with
    | VLoan (VSharedLoan (la, a')), VLoan (VSharedLoan (lb, b')) ->
        if la = lb then
          rewrap (fun a' -> VLoan (VSharedLoan (la, a'))) (wrap ctx_a a' b')
        else None
    | _, VLoan (VSharedLoan (lb, _))
      when InterpBorrowsCore.lookup_loan_opt span InterpBorrowsCore.ek_all lb ctx_a.env
           = None ->
        Some { a with value = VLoan (VSharedLoan (lb, a)) }
    | VLoan (VSharedLoan (la, a')), _ ->
        rewrap (fun a' -> VLoan (VSharedLoan (la, a'))) (wrap ctx_a a' b)
    | VAdt fa, VAdt fb
      when fa.variant_id = fb.variant_id
           && List.length fa.fields = List.length fb.fields ->
        let rec fields fa fb =
          match (fa, fb) with
          | a :: fa, b :: fb -> (
              match wrap ctx_a a b with
              | Some a -> Some (a :: fa)
              | None -> Option.map (fun fa -> a :: fa) (fields fa fb))
          | _ -> None
        in
        rewrap
          (fun fields -> VAdt { fa with fields })
          (fields fa.fields fb.fields)
    | VBorrow (VMutBorrow (ba, a')), VBorrow (VMutBorrow (bb, b')) when ba = bb
      ->
        rewrap (fun a' -> VBorrow (VMutBorrow (ba, a'))) (wrap ctx_a a' b')
    | _ -> None
  in
  (* Replace the [i]th shared value of an abstraction *)
  let replace_shared_value (abs : abs) (i : int) (v : tvalue) : abs =
    let count = ref 0 in
    let visitor =
      object
        inherit [_] map_abs as super

        method! visit_ASharedLoan env pm lid sv child =
          let sv = if !count = i then v else sv in
          incr count;
          ASharedLoan (pm, lid, sv, super#visit_tavalue env child)
      end
    in
    visitor#visit_abs () abs
  in
  let find_wrap (ctx_a : eval_ctx) (ctx_b : eval_ctx) (aid : abs_id) =
    match (ctx_lookup_abs_opt ctx_a aid, ctx_lookup_abs_opt ctx_b aid) with
    | Some abs_a, Some abs_b ->
        let va = shared_values abs_a and vb = shared_values abs_b in
        if List.length va = List.length vb then
          List.find_map
            (fun (i, (a, b)) ->
              Option.map
                (fun v -> replace_shared_value abs_a i v)
                (wrap ctx_a a b))
            (List.mapi (fun i x -> (i, x)) (List.combine va vb))
        else None
    | _ -> None
  in
  let rec align (ctxl : (eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)) list) =
    let refinement =
      List.find_map
        (fun (i, (ctx_a, _)) ->
          List.find_map
            (fun (ctx_b, _) ->
              Option.map
                (fun (sv, fields) -> (i, sv, expansion ctx_a fields))
                (List.find_map (find_in_abs ctx_a ctx_b)
                   (AbsId.Set.elements fixed_aids)))
            ctxl)
        (List.mapi (fun i x -> (i, x)) ctxl)
    in
    let wrapping () =
      List.find_map
        (fun (i, (ctx_a, _)) ->
          List.find_map
            (fun (ctx_b, _) ->
              Option.map
                (fun abs -> (i, abs))
                (List.find_map (find_wrap ctx_a ctx_b)
                   (AbsId.Set.elements fixed_aids)))
            ctxl)
        (List.mapi (fun i x -> (i, x)) ctxl)
    in
    match refinement with
    | None -> (
        match wrapping () with
        | None -> ctxl
        | Some (i, abs) ->
            align
              (List.mapi
                 (fun j (ctx, wrap) ->
                   if j <> i then (ctx, wrap)
                   else (fst (ctx_subst_abs span ctx abs.abs_id abs), wrap))
                 ctxl))
    | Some (i, sv, see) ->
        align
          (List.mapi
             (fun j (ctx, wrap) ->
               if j <> i then (ctx, wrap)
               else
                 let ctx, cc =
                   InterpExpansion.expand_symbolic_value_into span sv see ctx
                 in
                 (ctx, fun e -> wrap (cc e)))
             ctxl)
  in
  align (List.map (fun ctx -> (ctx, fun e -> e)) ctxl)

(** In the contexts reaching a join, fold the expansions of the values shared
    by the frozen abstractions which exist before the branching: branches which
    match on such a value (e.g., on the variant of a shared enumeration) expand
    it differently, while the frozen abstractions must be the same in all the
    contexts we join. Values under shared loans are immutable: the expansions
    are branch refinements of the values of [ctx0]. Comparing the frozen
    abstractions of a branch with the ones of [ctx0] gives a witness of the
    expansions: the expanded symbolic values with the values they were expanded
    to, and the projectors over them with their expansions. We put back the
    symbolic values and the projectors everywhere in the branch (the frozen
    abstractions, but also the copies of the shared values in the abstractions
    introduced since [ctx0]).

    This folds the borrow graph of the expansions with the values: we require
    the borrows, loans and symbolic values the expansions introduced not to
    appear anywhere else in the folded context (a branch may for instance
    return a borrow of a field of the expanded variant). Each branch keeps its
    synthesis: the folded symbolic values are bound before the branching. *)
let fold_frozen_abs_expansions (config : config) (span : Meta.span)
    ~(recoverable : bool) (ctx0 : eval_ctx)
    (ctxl : (eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)) list) :
    (eval_ctx * (SymbolicAst.expr -> SymbolicAst.expr)) list =
  let strip (abs : abs) = { abs with cont = None; parents = AbsId.Set.empty } in
  let frozen =
    List.filter
      (fun (abs : abs) -> not abs.can_end)
      (List.map snd (AbsId.Map.bindings (ctx_get_abs ctx0)))
  in
  let fail () =
    [%craise_recover] recoverable span
      "Could not fold the expansion of a value shared by a frozen abstraction"
  in
  (* Collect the expansions of the symbolic values of [x0] in [x1] *)
  let rec walk_value values (x0 : tvalue) (x1 : tvalue) : unit =
    if x0 <> x1 then (
      if x0.ty <> x1.ty then fail ();
      match (x0.value, x1.value) with
      | VSymbolic _, _ -> values := (x0, x1) :: !values
      | VAdt a0, VAdt a1
        when a0.variant_id = a1.variant_id
             && List.length a0.fields = List.length a1.fields ->
          List.iter2 (walk_value values) a0.fields a1.fields
      | VBorrow (VMutBorrow (b0, y0)), VBorrow (VMutBorrow (b1, y1)) when b0 = b1
        ->
          walk_value values y0 y1
      | VLoan (VSharedLoan (l0, y0)), VLoan (VSharedLoan (l1, y1)) when l0 = l1
        ->
          walk_value values y0 y1
      | _ -> fail ())
  in
  let rec walk_avalue values projs (x0 : tavalue) (x1 : tavalue) : unit =
    let walk = walk_avalue values projs in
    if x0 <> x1 then (
      if x0.ty <> x1.ty then fail ();
      match (x0.value, x1.value) with
      | ( ASymbolic
            ( _,
              ( AProjLoans { consumed = []; borrows = []; _ }
              | AProjBorrows { loans = []; _ } ) ),
          _ ) ->
          projs := (x0, x1) :: !projs
      | AAdt a0, AAdt a1
        when a0.variant_id = a1.variant_id
             && List.length a0.fields = List.length a1.fields ->
          List.iter2 walk a0.fields a1.fields
      | ( ALoan (ASharedLoan (pm0, l0, v0, c0)),
          ALoan (ASharedLoan (pm1, l1, v1, c1)) )
        when pm0 = pm1 && l0 = l1 ->
          walk_value values v0 v1;
          walk c0 c1
      | ALoan (AMutLoan (pm0, l0, c0)), ALoan (AMutLoan (pm1, l1, c1))
        when pm0 = pm1 && l0 = l1 ->
          walk c0 c1
      | ALoan (AIgnoredSharedLoan c0), ALoan (AIgnoredSharedLoan c1) ->
          walk c0 c1
      | ALoan (AIgnoredMutLoan (l0, c0)), ALoan (AIgnoredMutLoan (l1, c1))
        when l0 = l1 ->
          walk c0 c1
      | ABorrow (AMutBorrow (pm0, b0, c0)), ABorrow (AMutBorrow (pm1, b1, c1))
        when pm0 = pm1 && b0 = b1 ->
          walk c0 c1
      | ( ABorrow (AIgnoredMutBorrow (b0, c0)),
          ABorrow (AIgnoredMutBorrow (b1, c1)) )
        when b0 = b1 ->
          walk c0 c1
      | AIgnored (Some (_, m0)), AIgnored (Some (_, m1)) ->
          walk_value values m0 m1
      | _ -> fail ())
  in
  let fold (ctx : eval_ctx) : eval_ctx =
    let values = ref [] and projs = ref [] in
    List.iter
      (fun (abs0 : abs) ->
        match ctx_lookup_abs_opt ctx abs0.abs_id with
        | Some abs when not (equal_abs (strip abs) (strip abs0)) ->
            if
              not
                (equal_abs
                   { (strip abs) with avalues = [] }
                   { (strip abs0) with avalues = [] }
                && List.length abs.avalues = List.length abs0.avalues)
            then fail ();
            List.iter2 (walk_avalue values projs) abs0.avalues abs.avalues
        | _ -> ())
      frozen;
    if !values = [] && !projs = [] then ctx
    else
      let values =
        List.map (fun (v0, v) -> (v0, value_erase_shared_borrow_ids v)) !values
      in
      let projs = !projs in
      let visitor =
        object
          inherit [_] map_env as super

          method! visit_tvalue env v =
            match
              List.find_opt
                (fun ((v0 : tvalue), v') ->
                  v0.ty = v.ty && value_erase_shared_borrow_ids v = v')
                values
            with
            | Some (v0, _) -> v0
            | None -> super#visit_tvalue env v

          method! visit_tavalue env v =
            match List.find_opt (fun (_, p) -> p = v) projs with
            | Some (p0, _) -> p0
            | None -> super#visit_tavalue env v
        end
      in
      let env = visitor#visit_env () ctx.env in
      [%ltrace
        "- values:\n"
        ^ String.concat "\n"
            (List.map
               (fun (v0, v) ->
                 tvalue_to_string ctx v0 ^ " -> " ^ tvalue_to_string ctx v)
               values)
        ^ "\n- projs:\n"
        ^ String.concat "\n"
            (List.map
               (fun (p0, p1) ->
                 tavalue_to_string ctx p0 ^ " -> " ^ tavalue_to_string ctx p1)
               projs)
        ^ "\n- ctx:\n"
        ^ eval_ctx_to_string ~span:(Some span) ctx
        ^ "\n- folded ctx:\n"
        ^ eval_ctx_to_string ~span:(Some span) { ctx with env }];
      (* The borrows, loans and symbolic values with borrows the expansions
         introduced must not appear anymore. The other symbolic values are
         plain values the branch may have copied (they are bound by its
         synthesis). *)
      let obj, get_ids, get_ids_to_values = compute_ids () in
      List.iter (fun (_, v) -> obj#visit_tvalue () v) values;
      List.iter (fun (_, p) -> obj#visit_tavalue () p) projs;
      let ids = get_ids () in
      let ids0 = fst (compute_env_ids ctx0.env) in
      let fids = fst (compute_env_ids env) in
      let fresh_blids = BorrowId.Set.diff ids.blids ids0.blids in
      let fresh_sids =
        SymbolicValueId.Map.filter
          (fun sid (sv : symbolic_value) ->
            (not (SymbolicValueId.Set.mem sid ids0.sids))
            && ty_has_borrows (Some span) ctx.type_ctx.type_infos sv.sv_ty)
          (get_ids_to_values ()).sids_to_values
      in
      [%cassert_recover] recoverable span
        (BorrowId.Set.disjoint fresh_blids fids.blids
        && SymbolicValueId.Map.for_all
             (fun sid _ -> not (SymbolicValueId.Set.mem sid fids.sids))
             fresh_sids)
        "Could not fold the expansion of a value shared by a frozen \
         abstraction: a part of the expansion escapes";
      let ctx = { ctx with env } in
      [%cassert_recover] recoverable span
        (List.for_all
           (fun (abs0 : abs) ->
             match ctx_lookup_abs_opt ctx abs0.abs_id with
             | Some abs -> equal_abs (strip abs) (strip abs0)
             | None -> true)
           frozen)
        "Could not fold the expansion of a value shared by a frozen \
         abstraction";
      ctx
  in
  (* We only fold if the frozen abstractions differ between the contexts *)
  let differ =
    List.exists
      (fun (abs0 : abs) ->
        let versions =
          List.filter_map
            (fun ctx ->
              Option.map strip (ctx_lookup_abs_opt (fst ctx) abs0.abs_id))
            ctxl
        in
        List.exists (fun abs -> not (equal_abs abs (List.hd versions))) versions)
      frozen
  in
  (* The dead values may borrow parts of the expansions: we first eliminate
     them (as {!join_ctxs_list} does) *)
  let simplify_fold (ctx, wrap) =
    let ctx, cc = simplify_dummy_values_useless_abs config span ctx in
    (fold ctx, fun e -> wrap (cc e))
  in
  if differ then List.map simplify_fold ctxl else ctxl

let join_ctxs_list (config : config) (span : Meta.span)
    (fresh_abs_kind : abs_kind) ?(preprocess_first_ctx : bool = true)
    ~(recoverable : bool) ~(with_abs_conts : bool) (ctxl : eval_ctx list) :
    eval_ctx list * eval_ctx =
  (* The list of contexts should be non empty *)
  let ctx0, ctxl =
    match ctxl with
    | [] -> [%internal_error] span
    | ctx0 :: ctxl -> (ctx0, ctxl)
  in

  (* Small helper - TODO: probably not necessary anymore as we now preprocess
     the contexts depending on the situation *)
  let preprocess_ctx (ctx : eval_ctx) : eval_ctx =
    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation *)
    let ctx, _ = simplify_dummy_values_useless_abs config span ctx in
    [%ltrace
      "after simplify_dummy_values_useless_abs:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];
    ctx
  in

  let ctx0 = if preprocess_first_ctx then preprocess_ctx ctx0 else ctx0 in

  (* # Join with the new contexts, one by one

     For every context, we repeteadly attempt to join it with the current
     result of the join: if we fail (because we need to end loans for instance),
     we update the context and retry.
  *)
  let joined_ctx = ref ctx0 in
  let rec join_one_aux (ctx : eval_ctx) : eval_ctx =
    match
      join_ctxs span fresh_abs_kind ~recoverable ~with_abs_conts !joined_ctx ctx
    with
    | Ok { joined_ctx = nctx; _ } ->
        joined_ctx := nctx;
        ctx
    | Error err ->
        let ctx =
          (* TODO: simplify *)
          match err with
          | LoanInRight bid ->
              InterpBorrows.end_loan_no_synth config span bid ctx
          | LoansInRight bids ->
              InterpBorrows.end_loans_no_synth config span bids ctx
          | LoanInLeft bid ->
              joined_ctx :=
                InterpBorrows.end_loan_no_synth config span bid !joined_ctx;
              ctx
          | LoansInLeft bids ->
              joined_ctx :=
                InterpBorrows.end_loans_no_synth config span bids !joined_ctx;
              ctx
          | AbsInRight _ | AbsInLeft _ -> [%craise] span "Unexpected"
        in
        join_one_aux ctx
  in
  let rec join_one (ctx : eval_ctx) : eval_ctx =
    [%ltrace
      "join_one: initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Simplify the dummy values *)
    let ctx = preprocess_ctx ctx in

    (* Join the two contexts  *)
    let joined_ctx0 = !joined_ctx in
    let ctx1 = join_one_aux ctx in
    [%ltrace
      "join_one: after join:\n"
      ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];

    (* Collapse to eliminate the markers. If an abstraction of one of the
       contexts observes a loan in a way the other context can't share, we end
       it and join again. *)
    match
      collapse_ctx config span fresh_abs_kind ~recoverable ~with_abs_conts
        !joined_ctx
    with
    | exception InterpReduceCollapse.MarkedObservation (pm, sid) ->
        joined_ctx := joined_ctx0;
        let end_abs abs_id ctx =
          (InterpBorrows.end_abs_no_synth config span abs_id 0 ctx, ())
        in
        if pm = PLeft then (
          joined_ctx :=
            fst (end_observing_abs span ~recoverable sid end_abs !joined_ctx);
          join_one ctx1)
        else join_one (fst (end_observing_abs span ~recoverable sid end_abs ctx1))
    | collapsed ->
    joined_ctx := collapsed;
    [%ltrace
      "join_one: after join-collapse:\n"
      ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span !joined_ctx;

    (* Return *)
    ctx1
  in

  let ctxl = List.map join_one ctxl in

  (* # Return *)
  (ctx0 :: ctxl, !joined_ctx)

(** Destructure all the new abstractions *)
let destructure_new_abs (span : Meta.span) (old_abs_ids : AbsId.Set.t)
    (ctx : eval_ctx) : eval_ctx =
  [%ltrace "ctx:\n\n" ^ eval_ctx_to_string ctx];
  let is_fresh_abs_id (id : AbsId.id) : bool =
    not (AbsId.Set.mem id old_abs_ids)
  in
  let env =
    env_map_abs
      (fun abs ->
        if is_fresh_abs_id abs.abs_id then
          let abs =
            destructure_abs span abs.kind ~can_end:true
              ~destructure_shared_values:true ctx abs
          in
          abs
        else abs)
      ctx.env
  in
  let ctx = { ctx with env } in
  [%ltrace "resulting ctx:\n\n" ^ eval_ctx_to_string ctx];
  Invariants.check_invariants span ctx;
  ctx

let loop_join_origin_with_continue_ctxs (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (ctx0 : eval_ctx) (ctxl : eval_ctx list) :
    (eval_ctx * eval_ctx list) * eval_ctx =
  (* Simplify the contexts we want to join *)
  let simplify (ctx : eval_ctx) : eval_ctx =
    let fixed_aids = compute_fixed_abs_ids ctx0 ctx in
    let fixed_dids = ctx_get_dummy_var_ids ctx0 in
    [%ldebug "- fixed_aids: " ^ AbsId.Set.to_string None fixed_aids];

    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation, as we are only computing a fixed point *)
    let ctx, _ = simplify_dummy_values_useless_abs config span ctx in
    [%ltrace
      "simplify: after simplify_dummy_values_useless_abs:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs span fixed_aids ctx in
    [%ltrace
      "simplify: after destructure:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Reduce the context we want to add to the join *)
    let ctx =
      reduce_ctx config span ~with_abs_conts:false (Loop loop_id) fixed_aids
        fixed_dids ctx
    in
    [%ltrace
      "simplify: after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    ctx
  in

  let ctxl = List.map simplify ctxl in

  let ctxl', joined_ctx =
    join_ctxs_list config span (Loop loop_id) ~preprocess_first_ctx:false
      ~recoverable:false ~with_abs_conts:false (ctx0 :: ctxl)
  in
  [%sanity_check] span (List.length ctxl' = List.length ctxl + 1);
  ((List.hd ctxl', List.tl ctxl'), joined_ctx)

let loop_join_break_ctxs (config : config) (span : Meta.span)
    (loop_id : LoopId.id) (fixed_aids : AbsId.Set.t)
    (fixed_dids : DummyVarId.Set.t) (ctxl : eval_ctx list) : eval_ctx =
  (* Simplify the contexts *)
  let with_abs_conts = false in
  let fresh_abs_kind : abs_kind = Loop loop_id in
  let prepare_ctx (ctx : eval_ctx) : eval_ctx =
    [%ltrace
      "prepate_ctx: initial ctx:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Simplify the dummy values, by removing as many as we can -
       we ignore the synthesis continuation *)
    let ctx, _ = simplify_dummy_values_useless_abs config span ctx in
    [%ltrace
      "prepare_ctx: after simplify_dummy_values_useless_abs:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Destructure the abstractions introduced in the new context *)
    let ctx = destructure_new_abs span fixed_aids ctx in
    [%ltrace
      "prepare_ctx: after destructure:\n"
      ^ eval_ctx_to_string ~span:(Some span) ctx];

    (* Reduce the context we want to add to the join *)
    let ctx =
      reduce_ctx config span ~with_abs_conts:false (Loop loop_id) fixed_aids
        fixed_dids ctx
    in
    [%ltrace
      "prepare_ctx: after reduce:\n" ^ eval_ctx_to_string ~span:(Some span) ctx];
    (* Sanity check *)
    if !Config.sanity_checks then Invariants.check_invariants span ctx;

    ctx
  in
  let ctxl = List.map prepare_ctx ctxl in

  match ctxl with
  | [] -> [%internal_error] span
  | [ ctx ] ->
      (* Special case: simply remove the continuation expressions from the fresh abs *)
      let update (e : env_elem) : env_elem =
        match (e : env_elem) with
        | EAbs abs ->
            if AbsId.Set.mem abs.abs_id fixed_aids then e
            else EAbs { abs with cont = None; kind = Loop loop_id }
        | EBinding _ | EFrame -> e
      in
      { ctx with env = List.map update ctx.env }
  | ctx :: ctxl ->
      let joined_ctx = ref ctx in

      (* # Join the contexts, one by one.

          For every context, we repeteadly attempt to join it with the current
          result of the join: if we fail (because we need to end loans for instance),
          we update the context and retry.
       *)
      let rec join_one_aux (ctx : eval_ctx) =
        match
          join_ctxs span fresh_abs_kind ~recoverable:false ~with_abs_conts
            !joined_ctx ctx
        with
        | Ok { joined_ctx = nctx; _ } ->
            joined_ctx := nctx;
            ctx
        | Error err ->
            let ctx =
              (* TODO: simplify *)
              match err with
              | LoanInRight bid ->
                  InterpBorrows.end_loan_no_synth config span bid ctx
              | LoansInRight bids ->
                  InterpBorrows.end_loans_no_synth config span bids ctx
              | LoanInLeft bid ->
                  joined_ctx :=
                    InterpBorrows.end_loan_no_synth config span bid !joined_ctx;
                  ctx
              | LoansInLeft bids ->
                  joined_ctx :=
                    InterpBorrows.end_loans_no_synth config span bids
                      !joined_ctx;
                  ctx
              | AbsInRight _ | AbsInLeft _ -> [%craise] span "Unexpected"
            in
            join_one_aux ctx
      in
      let rec join_one (ctx : eval_ctx) =
        (* Join the two contexts  *)
        let joined_ctx0 = !joined_ctx in
        let ctx1 = join_one_aux ctx in
        [%ltrace
          "join_one: after join:\n" ^ eval_ctx_to_string ~span:(Some span) ctx1];

        (* Collapse to eliminate the markers (see {!join_ctxs_list}) *)
        match
          collapse_ctx config span fresh_abs_kind ~recoverable:false
            ~with_abs_conts !joined_ctx
        with
        | exception InterpReduceCollapse.MarkedObservation (pm, sid) ->
            joined_ctx := joined_ctx0;
            let end_abs abs_id ctx =
              (InterpBorrows.end_abs_no_synth config span abs_id 0 ctx, ())
            in
            if pm = PLeft then (
              joined_ctx :=
                fst
                  (end_observing_abs span ~recoverable:false sid end_abs
                     !joined_ctx);
              join_one ctx1)
            else
              join_one
                (fst (end_observing_abs span ~recoverable:false sid end_abs ctx1))
        | collapsed ->
        joined_ctx := collapsed;
        [%ltrace
          "join_one: after join-collapse:\n"
          ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];
        (* Sanity check *)
        if !Config.sanity_checks then
          Invariants.check_invariants span !joined_ctx;

        (* Reduce (it helps matching afterwards) *)
        joined_ctx :=
          reduce_ctx config span ~with_abs_conts fresh_abs_kind fixed_aids
            fixed_dids !joined_ctx;
        [%ltrace
          "join_one: after last reduce:\n"
          ^ eval_ctx_to_string ~span:(Some span) !joined_ctx];

        (* Sanity check *)
        if !Config.sanity_checks then
          Invariants.check_invariants span !joined_ctx
      in
      List.iter join_one ctxl;

      (* Update the fresh region abstractions *)
      !joined_ctx

(** TODO: this is a bit of a hack: remove once the avalues are properly
    destructured. *)
let destructure_shared_loans (span : Meta.span) (fixed_aids : AbsId.Set.t) :
    cm_fun =
 fun ctx ->
  let bindings = ref [] in

  let copy_symbolic (sv : symbolic_value) : symbolic_value =
    [%cassert] span
      (not (symbolic_value_has_borrows (Some span) ctx sv))
      "Not implemented";
    let sv' =
      mk_fresh_symbolic_value_opt_span (Some span) ctx.fresh_symbolic_value_id
        sv.sv_ty
    in
    bindings := (sv', mk_tvalue_from_symbolic_value sv) :: !bindings;
    sv'
  in

  let rec destructure_value (abs : abs) (v : tvalue) : tvalue * tavalue list =
    let value, avl =
      match v.value with
      | VLiteral _ | VBottom | VSymbolic _ -> (v.value, [])
      | VAdt { variant_id; fields } ->
          let fields, avl =
            List.split (List.map (destructure_value abs) fields)
          in
          (VAdt { variant_id; fields }, List.flatten avl)
      | VBorrow bc -> (
          match bc with
          | VSharedBorrow _ | VFrozenMutBorrow _ -> (v.value, [])
          | VMutBorrow (lid, ({ value = VLoan (VSharedLoan (k, w)); _ } as bv))
            ->
              (* The shared loan freezes the borrowed value while the mutable
                 borrow is below a shared loan (see
                 {!InterpBorrowsCore.ctx_freeze_mut_borrows_in_shared_values}):
                 it stays there *)
              let w, avl = destructure_value abs w in
              let bv = { bv with value = VLoan (VSharedLoan (k, w)) } in
              (VBorrow (VMutBorrow (lid, bv)), avl)
          | VMutBorrow (lid, v) ->
              let v, avl = destructure_value abs v in
              (VBorrow (VMutBorrow (lid, v)), avl)
          | VReservedMutBorrow _ -> [%internal_error] span)
      | VLoan lc -> (
          match lc with
          | VSharedLoan (lid, sv) ->
              (* The loan moves to the abstraction, with a copy of the shared
                 value: we copy it before destructuring it *)
              let copy = InterpBorrowsCore.copy_shared_value span ctx copy_symbolic sv in
              let sv, avl = destructure_value abs sv in
              (* The references inside the shared value (nested borrows) don't
                 belong to the abstraction: they get fresh regions *)
              let _, ty =
                TypesUtils.ty_refresh_regions (Some span) ctx.fresh_region_id
                  sv.ty
              in
              let ref_ty = TRef (abs_pick_region span abs, ty, RShared) in
              let child = ValuesUtils.mk_aignored span ty None in
              let av = ALoan (ASharedLoan (PNone, lid, copy, child)) in
              let av : tavalue = { value = av; ty = ref_ty } in
              (sv.value, av :: avl)
          | VMutLoan _ -> (v.value, []))
    in
    ({ v with value }, avl)
  in

  let rec destructure_avalue (abs : abs) (av : tavalue) : tavalue * tavalue list
      =
    let value, avl =
      match av.value with
      | AAdt { borrow_proj; variant_id; fields } ->
          let fields, avl =
            List.split (List.map (destructure_avalue abs) fields)
          in
          (AAdt { borrow_proj; variant_id; fields }, List.flatten avl)
      | ALoan lc ->
          let lc, avl =
            match lc with
            | AMutLoan (pm, lid, child) ->
                let child, avl = destructure_avalue abs child in
                (AMutLoan (pm, lid, child), avl)
            | ASharedLoan (pm, lid, sv, child) ->
                let sv, avl0 = destructure_value abs sv in
                let child, avl1 = destructure_avalue abs child in
                (ASharedLoan (pm, lid, sv, child), avl0 @ avl1)
            | AEndedMutLoan { child; given_back; given_back_meta } ->
                let child, avl0 = destructure_avalue abs child in
                let given_back, avl1 = destructure_avalue abs given_back in
                ( AEndedMutLoan { child; given_back; given_back_meta },
                  avl0 @ avl1 )
            | AEndedSharedLoan (sv, child) ->
                let sv, avl0 = destructure_value abs sv in
                let child, avl1 = destructure_avalue abs child in
                (AEndedSharedLoan (sv, child), avl0 @ avl1)
            | AIgnoredMutLoan (lid, child) ->
                let child, avl = destructure_avalue abs child in
                (AIgnoredMutLoan (lid, child), avl)
            | AEndedIgnoredMutLoan { child; given_back; given_back_meta } ->
                let child, avl0 = destructure_avalue abs child in
                let given_back, avl1 = destructure_avalue abs given_back in
                ( AEndedIgnoredMutLoan { child; given_back; given_back_meta },
                  avl0 @ avl1 )
            | AIgnoredSharedLoan child ->
                let child, avl = destructure_avalue abs child in
                (AIgnoredSharedLoan child, avl)
          in
          (ALoan lc, avl)
      | ABorrow bc ->
          let bc, avl =
            match bc with
            | AMutBorrow (pm, lid, child) ->
                let child, avl = destructure_avalue abs child in
                (AMutBorrow (pm, lid, child), avl)
            | ASharedBorrow _ | AProjSharedBorrow _ ->
                (* No shared values below *)
                (bc, [])
            | AIgnoredMutBorrow (lid, child) ->
                let child, avl = destructure_avalue abs child in
                (AIgnoredMutBorrow (lid, child), avl)
            | AEndedMutBorrow _ | AEndedSharedBorrow ->
                (* Shouldn't find ended borrows in live abstractions *)
                [%internal_error] span
            | AEndedIgnoredMutBorrow _ -> (bc, [])
          in
          (ABorrow bc, avl)
      | ASymbolic _ | AIgnored _ -> (av.value, [])
    in
    ({ av with value }, avl)
  in
  let destructure_abs (abs : abs) : abs =
    if not (AbsId.Set.mem abs.abs_id fixed_aids) then
      let avalues = List.map (destructure_avalue abs) abs.avalues in
      let avalues =
        List.flatten (List.map (fun (av, avl) -> av :: avl) avalues)
      in
      { abs with avalues }
    else abs
  in
  let ctx = { ctx with env = env_map_abs destructure_abs ctx.env } in

  let cc e =
    List.fold_right
      (fun (nsv, v) e ->
        SymbolicAst.IntroSymbolic (ctx, None, nsv, VaSingleValue v, e))
      !bindings e
  in

  (ctx, cc)

let rec match_ctx_with_target (config : config) (span : Meta.span)
    (fresh_abs_kind : abs_kind) (fixed_aids : AbsId.Set.t)
    (fixed_dids : DummyVarId.Set.t) (input_abs : AbsId.id list)
    (input_svalues : SymbolicValueId.id list) ~(recoverable : bool)
    ~(preserve_common_abs : bool) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    (eval_ctx * eval_ctx * tvalue SymbolicValueId.Map.t * abs AbsId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* If an abstraction of the target observes a loan in a way the source can't
     share (see {!InterpReduceCollapse.MarkedObservation}), we end it and match
     again *)
  try
    match_ctx_with_target_aux config span fresh_abs_kind fixed_aids fixed_dids
      input_abs input_svalues ~recoverable ~preserve_common_abs src_ctx tgt_ctx
  with InterpReduceCollapse.MarkedObservation (pm, sid) ->
    [%cassert_recover] recoverable span (pm = PRight) "Unimplemented";
    let tgt_ctx, cc =
      end_observing_abs span ~recoverable sid
        (fun abs_id ctx -> InterpBorrows.end_abs config span abs_id 0 ctx)
        tgt_ctx
    in
    let res, cc' =
      match_ctx_with_target config span fresh_abs_kind fixed_aids fixed_dids
        input_abs input_svalues ~recoverable ~preserve_common_abs src_ctx
        tgt_ctx
    in
    (res, Cps.cc_comp cc cc')

and match_ctx_with_target_aux (config : config) (span : Meta.span)
    (fresh_abs_kind : abs_kind) (fixed_aids : AbsId.Set.t)
    (fixed_dids : DummyVarId.Set.t) (input_abs : AbsId.id list)
    (input_svalues : SymbolicValueId.id list) ~(recoverable : bool)
    ~(preserve_common_abs : bool) (src_ctx : eval_ctx) (tgt_ctx : eval_ctx) :
    (eval_ctx * eval_ctx * tvalue SymbolicValueId.Map.t * abs AbsId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "- src_ctx: " ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: "
    ^ eval_ctx_to_string tgt_ctx];

  (* End all the unnecessary borrows/loans.

     Note that in theory it's better to call [prepare_loop_match_ctx_with_target]
     *before* because it unlocks simplification possibilities for
     [simplify_dummy_values_useless_abs], but in practice it is also good to
     call [simplify_dummy_values_useless_abs config span tgt_ctx] before so
     that it prevents [prepare_match_ctx_with_target] from doing matches that
     are not supported yet. For this reason, we call simplify twice: before
     and after the call to prepare.
  *)
  let tgt_ctx, cc = simplify_dummy_values_useless_abs config span tgt_ctx in
  [%ltrace
    "- tgt_ctx after simplify_dummy_values_useless_abs (i):\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* We first reorganize [tgt_ctx] so that we can match [src_ctx] with it (by
     ending loans for instance - remember that the [src_ctx] is the fixed point
     context, which results from joins during which we ended the loans which
     were introduced during the loop iterations).

     This operation only ends loans/abstractions and moves some values to anonymous
     values.
  *)
  let tgt_ctx, cc =
    comp cc
      (prepare_match_ctx_with_target config span fresh_abs_kind ~recoverable
         src_ctx tgt_ctx)
  in
  [%ltrace
    "Finished preparing the match:" ^ "\n- src_ctx: "
    ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx: " ^ eval_ctx_to_string tgt_ctx];

  (* End all the unnecessary borrows/loans (note that it's better to call
     [prepare_loop_match_ctx_with_target] *before* because it unlocks simplification
     possibilities for [simplify_dummy_values_useless_abs]. *)
  let tgt_ctx, cc =
    comp cc (simplify_dummy_values_useless_abs config span tgt_ctx)
  in
  [%ltrace
    "- tgt_ctx after simplify_dummy_values_useless_abs (ii):\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* The join turns the function call abstractions it outputs into join
     abstractions (see {!InterpStatements.eval_switch_with_join}): we do the
     same with their counterparts in the target context, so that we identify
     them as common abstractions. *)
  let tgt_ctx =
    if preserve_common_abs then
      let src_abs = ctx_get_abs src_ctx in
      ctx_map_abs
        (fun abs ->
          match (abs.kind, AbsId.Map.find_opt abs.abs_id src_abs) with
          | FunCall _, Some { kind = Join; _ } -> { abs with kind = Join }
          | _ -> abs)
        tgt_ctx
    else tgt_ctx
  in
  (* The abstractions of the joined context which are fresh with respect to
     the context before the branching are destructured (see
     {!InterpAbs.add_abs_cont_to_abs}): when the destructured values of an
     abstraction of the target context are the values of its counterpart in
     the joined context, we use them. We keep the continuation of the target
     abstraction: it refers to its backward function, whose type is fixed. *)
  let tgt_ctx =
    if preserve_common_abs then
      let src_abs = ctx_get_abs src_ctx in
      ctx_map_abs
        (fun abs ->
          match AbsId.Map.find_opt abs.abs_id src_abs with
          | Some src_abs
            when not (AbsId.Set.mem abs.abs_id fixed_aids)
                 && src_abs.avalues <> abs.avalues ->
              let dabs =
                destructure_abs span abs.kind ~can_end:abs.can_end
                  ~destructure_shared_values:true tgt_ctx abs
              in
              if dabs.avalues = src_abs.avalues then
                { abs with avalues = dabs.avalues }
              else abs
          | _ -> abs)
        tgt_ctx
    else tgt_ctx
  in
  let preserved_aids =
    if preserve_common_abs then
      AbsId.Set.union fixed_aids (compute_fixed_abs_ids src_ctx tgt_ctx)
    else fixed_aids
  in

  (* Removed the ended shared loans and destructure the shared loans.
     We destructure the shared loans in the abstractions which appear in
     [tgt_ctx] but not [src_ctx]. TODO: generalize. *)
  let tgt_ctx, cc =
    comp cc (destructure_shared_loans span preserved_aids tgt_ctx)
  in
  [%ltrace
    "- tgt_ctx after simplify_ended_shared_loans:\n"
    ^ eval_ctx_to_string tgt_ctx];

  (* Reduce the context - TODO: generalize the join so that we don't need to do this *)
  let tgt_ctx =
    reduce_ctx config span ~with_abs_conts:true fresh_abs_kind preserved_aids
      fixed_dids tgt_ctx
  in
  [%ltrace "- tgt_ctx after reduce_ctx:\n" ^ eval_ctx_to_string tgt_ctx];

  (* Join the source context with the target context *)
  let join_info =
    match
      join_ctxs span fresh_abs_kind ~recoverable ~with_abs_conts:true src_ctx
        tgt_ctx
    with
    | Ok x -> x
    | Error _ -> [%craise] span "Could not join the contexts"
  in
  let joined_ctx = join_info.joined_ctx in
  [%ltrace
    "Result of the join:\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx
    ^ "\n- join_info.symbolic_to_value: "
    ^ SymbolicValueId.Map.to_string (Some "  ")
        (Print.pair_to_string (tvalue_to_string src_ctx)
           (tvalue_to_string src_ctx))
        join_info.symbolic_to_value];

  (* We need to collapse the context.

     We have to collapse the context because otherwise some abstractions might not
     get merged, leading to an issue when matching the source context with the
     joined context afterwards. We also do not want to collapse the context then
     project it, because the collapsed context uses elements from both the right
     and left context in its abstraction expressions, which are a bit annoying
     to project. What we do for now is merge the joined context, to register the
     sequence of merges which have to be performed, then project the context
     *before* the collapse, and apply the same sequence to this one.

     TODO: we need to make the match more general so that we do not have to do this.
  *)
  let merge_seq = ref [] in
  let add_borrows_seq = ref [] in
  let joined_ctx_not_projected =
    collapse_ctx config span ~sequence:(Some merge_seq)
      ~shared_borrows_seq:(Some add_borrows_seq) ~recoverable
      ~with_abs_conts:true fresh_abs_kind joined_ctx
  in
  let merge_seq = List.rev !merge_seq in
  (* Update the sequence of shared borrows to introduce: we only want to add
     borrows to the right *)
  let add_borrows_seq =
    List.filter_map
      (fun (abs_id, pm, bid, ty) ->
        if pm = PRight then Some (abs_id, PNone, bid, ty) else None)
      (List.rev !add_borrows_seq)
  in
  [%ltrace
    "After collapsing the (unprojected) context: joined_ctx_not_projected:\n"
    ^ eval_ctx_to_string joined_ctx_not_projected
    ^ "\n\n- merge_seq:\n"
    ^ String.concat "\n"
        (List.map
           (fun (a0, a1, a2) ->
             "(" ^ AbsId.to_string a0 ^ "," ^ AbsId.to_string a1 ^ ") -> "
             ^ AbsId.to_string a2)
           merge_seq)];

  (* Project the context to only preserve the right part, which corresponds to the
     target. The abstractions which receive shared borrows on the right may
     contain only left values. *)
  let receiving_aids =
    AbsId.Set.of_list (List.map (fun (aid, _, _, _) -> aid) add_borrows_seq)
  in
  let joined_ctx =
    project_context span preserved_aids ~receiving_aids PRight joined_ctx
  in
  let joined_symbolic_to_tgt_value =
    SymbolicValueId.Map.map (fun (_, x) -> x) join_info.symbolic_to_value
  in
  [%ltrace
    "After projection: joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx
    ^ "\n- joined_symbolic_to_tgt_value: "
    ^ SymbolicValueId.Map.to_string (Some "  ") (tvalue_to_string src_ctx)
        joined_symbolic_to_tgt_value];

  (* Compute the set of abstractions resulting from the merges which end up in
     an abstraction owning the static region (see
     [collapse_ctx_no_markers_following_sequence]) *)
  let static_aids =
    let final_static =
      AbsId.Set.of_list
        (List.filter_map
           (fun (abs : abs) ->
             if abs_owns_static abs then Some abs.abs_id else None)
           (AbsId.Map.values (ctx_get_abs joined_ctx_not_projected)))
    in
    (* Propagate backward: if the result of a merge ends up in an abstraction
       owning the static region, so do the merged abstractions *)
    List.fold_left
      (fun s (a0, a1, a2) ->
        if AbsId.Set.mem a2 s then AbsId.Set.add a0 (AbsId.Set.add a1 s) else s)
      final_static (List.rev merge_seq)
  in

  (* Apply the sequence of merges to the projected context *)
  let joined_ctx =
    collapse_ctx_no_markers_following_sequence span merge_seq static_aids
      add_borrows_seq ~with_abs_conts:true fresh_abs_kind joined_ctx
  in
  [%ltrace
    "After collapsing the context: joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  (* There may be empty abstractions in the projected context: end them.

     Remark: we forbid the introduction of (meta) snapshots, because they may
     refer to values which are introduced as, for instance, output of a loop
     and are not bound yet (this may lead to issues). *)
  let joined_ctx, cc =
    comp cc
      (simplify_dummy_values_useless_abs config span ~snapshots:false joined_ctx)
  in
  [%ltrace
    "After applying [simplify_dummy_values_useless_abs] to the joined context: \
     joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  (* Reorder the region abstractions in the target context -
     TODO: generalize the match so that we don't have to do this *)
  let joined_ctx = reorder_fresh_abs span true preserved_aids joined_ctx in
  [%ltrace
    "After reorder_fresh_abs (preserved_aids: "
    ^ AbsId.Set.to_string None preserved_aids
    ^ "): joined_ctx:\n"
    ^ eval_ctx_to_string ~span:(Some span) joined_ctx];

  [%ltrace
    "About to match:" ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx
    ^ "\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];

  (* Check that the source context (i.e., the fixed-point context) matches
     the resulting target context. *)
  let src_to_joined_maps =
    let open InterpBorrowsCore in
    let lookup_shared_loan lid ctx : tvalue =
      match snd (ctx_lookup_loan span ek_all lid ctx) with
      | Concrete (VSharedLoan (_, v)) -> v
      | Abstract (ASharedLoan (pm, _, v, _)) ->
          [%sanity_check] span (pm = PNone);
          v
      | _ -> [%craise] span "Unreachable"
    in
    let lookup_in_src id = lookup_shared_loan id src_ctx in
    let lookup_in_joined id = lookup_shared_loan id joined_ctx in
    (* Match *)
    let fixed_ids =
      { empty_ids_sets with aids = ctx_get_frozen_abs_set src_ctx }
    in
    match
      try_match_ctxs span ~check_equiv:false ~check_kind:false
        ~check_can_end:false fixed_ids lookup_in_src lookup_in_joined src_ctx
        joined_ctx
    with
    | Some ctx -> ctx
    | None -> [%craise] span "Could not match the contexts"
  in
  [%ltrace
    "The match was successful:" ^ "\n\n- src_ctx: "
    ^ eval_ctx_to_string ~span:(Some span) src_ctx
    ^ "\n\n- joined_ctx: "
    ^ eval_ctx_to_string ~span:(Some span) joined_ctx
    ^ "\n\n- src_to_joined_maps: "
    ^ ids_maps_to_string joined_ctx src_to_joined_maps];

  (* Sanity check *)
  if !Config.sanity_checks then
    Invariants.check_borrowed_values_invariant span joined_ctx;

  (* Compute the loop input values and abstractions *)
  [%ltrace
    "About to compute the input values and abstractions:"
    ^ "\n- fp_input_svalues: "
    ^ String.concat ", " (List.map SymbolicValueId.to_string input_svalues)
    ^ "\n- src_to_joined_maps:\n"
    ^ ids_maps_to_string joined_ctx src_to_joined_maps
    ^ "\n- joined_symbolic_to_tgt_value: "
    ^ SymbolicValueId.Map.to_string (Some "  ") (tvalue_to_string src_ctx)
        joined_symbolic_to_tgt_value
    ^ "\n- src_ctx:\n" ^ eval_ctx_to_string src_ctx ^ "\n- joined_ctx:\n"
    ^ eval_ctx_to_string joined_ctx];
  let input_values =
    SymbolicValueId.Map.of_list
      (List.map
         (fun sid ->
           (* We retrieve the value in two steps:
              - source to joined
              - joined to target
              Note that joined to target is a partial map: it only maps
              symbolic values appearing in the joined context, and in
              particular appearing in the joined values (not in the region
              abstractions). For all the missing symbolic values, the
              substitution should be the identity.
           *)
           let v =
             match
               SymbolicValueId.Map.find_opt sid
                 src_to_joined_maps.sid_to_value_map
             with
             | Some v -> v
             | None -> (
                 (* The symbolic values of the fixed abstractions (for instance
                    the shared values of the frozen input abstractions) are
                    not matched: they are the same in the joined context *)
                 match ctx_find_symbolic_value joined_ctx sid with
                 | Some sv -> mk_tvalue_from_symbolic_value sv
                 | None ->
                     [%craise] span
                       ("Could not find symbolic value @"
                       ^ SymbolicValueId.to_string sid
                       ^ " in src_to_joined_map"))
           in
           (* Update the symbolic values appearing in [v] *)
           let subst =
             object
               inherit [_] map_tvalue

               method! visit_VSymbolic _ sv =
                 match
                   SymbolicValueId.Map.find_opt sv.sv_id
                     joined_symbolic_to_tgt_value
                 with
                 | Some v -> v.value
                 | None -> VSymbolic sv
             end
           in
           let v = subst#visit_tvalue () v in
           (sid, v))
         input_svalues)
  in
  let input_abs =
    let aid_map =
      AbsId.Map.of_list (AbsId.InjSubst.bindings src_to_joined_maps.aid_map)
    in
    AbsId.Map.of_list
      (List.map
         (fun input_aid ->
           match AbsId.Map.find_opt input_aid aid_map with
           | None -> [%internal_error] span
           | Some joined_id ->
               (* The abstractions we preserved come from the target context,
                  with their own continuations *)
               let ctx =
                 if AbsId.Set.mem joined_id preserved_aids then tgt_ctx
                 else joined_ctx
               in
               (input_aid, ctx_lookup_abs ctx joined_id))
         input_abs)
  in

  [%ltrace
    "Input values:\n"
    ^ SymbolicValueId.Map.to_string (Some "  ")
        (tvalue_to_string ~span:(Some span) src_ctx)
        input_values
    ^ "\nInput abs:\n"
    ^ AbsId.Map.to_string (Some "  ") (abs_to_string span src_ctx) input_abs];

  (* *)
  Invariants.check_invariants span joined_ctx;

  (* We continue with the *fixed-point* context *)
  ((src_ctx, tgt_ctx, input_values, input_abs), cc)

let loop_match_break_ctx_with_target (config : config) (span : Meta.span)
    (_loop_id : LoopId.id) (fixed_aids : AbsId.Set.t)
    (fixed_dids : DummyVarId.Set.t) (fp_input_abs : abs_id list)
    (fp_input_svalues : SymbolicValueId.id list) (src_ctx : eval_ctx)
    (tgt_ctx : eval_ctx) :
    (eval_ctx * eval_ctx * tvalue SymbolicValueId.Map.t * abs AbsId.Map.t)
    * (SymbolicAst.expr -> SymbolicAst.expr) =
  (* Debug *)
  [%ltrace
    "- src_ctx:\n" ^ eval_ctx_to_string src_ctx ^ "\n- tgt_ctx:\n"
    ^ eval_ctx_to_string tgt_ctx];

  match_ctx_with_target config span WithCont fixed_aids fixed_dids fp_input_abs
    fp_input_svalues ~recoverable:false ~preserve_common_abs:false src_ctx
    tgt_ctx
