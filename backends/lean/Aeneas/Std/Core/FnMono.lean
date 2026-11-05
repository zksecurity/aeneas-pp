module
public import Lean
public import Aeneas.Std.Core.Ops
public section

/-!
# Monotonicity through closure dictionaries

Rust functions which are mutually recursive with closures (the closures call the
functions which create them, for instance through a generic helper taking an
`impl FnOnce`) are extracted as a `partial_fixpoint` block in which the closure
dictionaries are inline records, e.g. `helper ({ call_once := f } : FnOnce ..)`.
To prove those definitions monotone, `partial_fixpoint` needs:
- the projections of the closure dictionaries built from monotone methods to be
  monotone (the theorems below);
- the generic helpers taking closure dictionaries to be monotone in their
  dictionaries, as long as the methods of the dictionaries are monotone: the
  `derive_closure_mono` command proves this for a (non-recursive) helper.
-/

namespace Aeneas.Std

open Lean.Order

section
variable {α : Sort u} [PartialOrder α] {S : Type v} {A : Type w} {O : Type x}

@[partial_fixpoint_monotone]
theorem core.ops.function.FnOnce.mk_call_once_mono (g : α → S → A → Result O)
    (h : monotone g) : monotone fun a => (core.ops.function.FnOnce.mk (g a)).call_once := h

@[partial_fixpoint_monotone]
theorem core.ops.function.FnMut.mk_call_mut_mono (o : α → core.ops.function.FnOnce S A O)
    (g : α → S → A → Result (O × S)) (h : monotone g) :
    monotone fun a => (core.ops.function.FnMut.mk (o a) (g a)).call_mut := h

@[partial_fixpoint_monotone]
theorem core.ops.function.FnMut.mk_FnOnceInst_call_once_mono
    (o : α → core.ops.function.FnOnce S A O) (g : α → S → A → Result (O × S))
    (h : monotone fun a => (o a).call_once) :
    monotone fun a => (core.ops.function.FnMut.mk (o a) (g a)).FnOnceInst.call_once := h

@[partial_fixpoint_monotone]
theorem core.ops.function.Fn.mk_call_mono (m : α → core.ops.function.FnMut S A O)
    (g : α → S → A → Result O) (h : monotone g) :
    monotone fun a => (core.ops.function.Fn.mk (m a) (g a)).call := h

@[partial_fixpoint_monotone]
theorem core.ops.function.Fn.mk_FnMutInst_call_mut_mono (m : α → core.ops.function.FnMut S A O)
    (g : α → S → A → Result O) (h : monotone fun a => (m a).call_mut) :
    monotone fun a => (core.ops.function.Fn.mk (m a) (g a)).FnMutInst.call_mut := h

@[partial_fixpoint_monotone]
theorem core.ops.function.Fn.mk_FnMutInst_FnOnceInst_call_once_mono
    (m : α → core.ops.function.FnMut S A O) (g : α → S → A → Result O)
    (h : monotone fun a => (m a).FnOnceInst.call_once) :
    monotone fun a => (core.ops.function.Fn.mk (m a) (g a)).FnMutInst.FnOnceInst.call_once := h
end

open Lean Elab Command Term Meta

/-- The closure traits, with the paths to their methods through their parent
    clauses -/
meta def closureTraitMethodPaths : List (Name × List (List Name)) := [
  (``core.ops.function.FnOnce, [[`call_once]]),
  (``core.ops.function.FnMut, [[`call_mut], [`FnOnceInst, `call_once]]),
  (``core.ops.function.Fn,
    [[`call], [`FnMutInst, `call_mut], [`FnMutInst, `FnOnceInst, `call_once]])
]

/-- Introduce, for each closure dictionary among the parameters [xs], a function
    from [α] to the dictionary in place of the parameter. Return the new
    parameters and, for each dictionary, its position, the function and the
    paths to its methods. -/
meta partial def withClosureDictFuns {β} [Inhabited β] (α : Expr) (xs : Array Expr) (i : Nat)
    (params : Array Expr) (dicts : Array (Nat × Expr × List (List Name)))
    (k : Array Expr → Array (Nat × Expr × List (List Name)) → MetaM β) : MetaM β := do
  if h : i < xs.size then
    let x := xs[i]
    let ty ← inferType x
    match ty.getAppFn.constName? >>= fun n => closureTraitMethodPaths.lookup n with
    | some paths =>
      withLocalDeclD ((← x.fvarId!.getUserName).appendAfter "_fun") (← mkArrow α ty) fun g =>
        withClosureDictFuns α xs (i + 1) (params.push g) (dicts.push (i, g, paths)) k
    | none => withClosureDictFuns α xs (i + 1) (params.push x) dicts k
  else k params dicts

/-- Introduce the hypotheses stating that the methods of the dictionaries are
    monotone -/
meta partial def withMethodsMono {β} [Inhabited β] (α : Expr) (methods : List (Expr × List Name))
    (hs : Array Expr) (k : Array Expr → MetaM β) : MetaM β := do
  match methods with
  | [] => k hs
  | (g, path) :: methods =>
    let fn ← withLocalDeclD `a α fun a => do
      mkLambdaFVars #[a] (← path.foldlM (fun e f => mkProjection e f) (mkApp g a))
    withLocalDeclD `h (← mkAppM ``monotone #[fn]) fun h =>
      withMethodsMono α methods (hs.push h) k

/-- `derive_closure_mono f` proves that `f` is monotone in its closure
    dictionaries (`FnOnce`, `FnMut` and `Fn` instances) as long as their methods
    are monotone, and registers the theorem `f.closure_mono` for
    `partial_fixpoint`. -/
syntax (name := deriveClosureMono) "derive_closure_mono " ident : command

@[command_elab deriveClosureMono]
meta def elabDeriveClosureMono : CommandElab := fun stx => do
  let thmName ← liftTermElabM do
    let fName ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let info ← getConstInfo fName
    let uName ← mkFreshUserName `u
    let us := info.levelParams.map Level.param
    let type ← forallTelescope info.type fun xs _ =>
      withLocalDecl `α .implicit (mkSort (Level.param uName)) fun α => do
      withLocalDecl `inst .instImplicit (← mkAppM ``PartialOrder #[α]) fun inst =>
      withClosureDictFuns α xs 0 #[] #[] fun params dicts => do
        let methods := dicts.toList.flatMap fun (_, g, paths) => paths.map (g, ·)
        withMethodsMono α methods #[] fun hs => do
          let fn ← withLocalDeclD `a α fun a => do
            let args := (Array.range xs.size).map fun k =>
              match dicts.find? (fun (i, _, _) => i == k) with
              | some (_, g, _) => mkApp g a
              | none => xs[k]!
            mkLambdaFVars #[a] (mkAppN (mkConst fName us) args)
          mkForallFVars (#[α, inst] ++ params ++ hs) (← mkAppM ``monotone #[fn])
    let type ← instantiateMVars type
    let mvar ← mkFreshExprSyntheticOpaqueMVar type
    let tac ← `(tactic|
      (intros
       unfold $(mkIdent fName):ident
       repeat' first
         | (apply Lean.Order.monotone_apply; apply Lean.Order.monotone_apply; assumption)
         | monotonicity))
    Term.runTactic mvar.mvarId! tac .term
    let value ← instantiateMVars mvar
    let thmName := fName ++ `closure_mono
    addDecl <| Declaration.thmDecl
      { name := thmName, levelParams := uName :: info.levelParams, type, value }
    pure thmName
  elabCommand (← `(attribute [partial_fixpoint_monotone] $(mkIdent thmName)))

end Aeneas.Std
