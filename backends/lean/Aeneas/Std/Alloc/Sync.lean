/- `alloc::sync`: `Arc<T>` is `T` in the extracted code. -/
module
public import Aeneas.Std.Alloc.Vec
public import Aeneas.Std.Core.Cmp
public import Aeneas.Std.Core.Default
public import Aeneas.Std.Core.Convert
public section

namespace Aeneas.Std

open Result

/-- `Arc<T>` is a shared reference to an immutable value: we model it as the value
    itself. It is an `abbrev` so that recursive types can nest through it (e.g.,
    `Option<Arc<Self>>`). -/
@[expose, reducible, rust_type "alloc::sync::Arc"]
def alloc.sync.Arc (T : Type u) : Type u := T

@[expose, rust_fun "alloc::sync::{alloc::sync::Arc<@T>}::new" -canFail]
def alloc.sync.Arc.new {T : Type _} (x : T) : alloc.sync.Arc T := x

@[expose, rust_fun "alloc::sync::{core::clone::Clone<alloc::sync::Arc<@T>>}::clone" -canFail
    (keepParams := [true, false]) (keepTraitClauses := [false])]
def alloc.sync.Arc.clone {T : Type _} (x : alloc.sync.Arc T) : alloc.sync.Arc T := x

@[expose, rust_fun "alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref" -canFail
    (keepParams := [true, false])]
def alloc.sync.Arc.deref {T : Type _} (x : alloc.sync.Arc T) : T := x

@[expose, rust_fun "alloc::sync::{core::convert::AsRef<alloc::sync::Arc<@T>, @T>}::as_ref" -canFail
    (keepParams := [true, false])]
def alloc.sync.Arc.as_ref {T : Type _} (x : alloc.sync.Arc T) : T := x

@[expose, rust_fun "alloc::sync::{core::borrow::Borrow<alloc::sync::Arc<@T>, @T>}::borrow" -canFail
    (keepParams := [true, false])]
def alloc.sync.Arc.borrow {T : Type _} (x : alloc.sync.Arc T) : T := x

@[expose, rust_fun "alloc::sync::{core::cmp::PartialEq<alloc::sync::Arc<@T>, alloc::sync::Arc<@T>>}::eq"
    (keepParams := [true, false])]
def alloc.sync.Arc.eq {T : Type _} (PartialEqInst : core.cmp.PartialEq T T)
    (x y : alloc.sync.Arc T) : Result Bool :=
  PartialEqInst.eq x y

@[expose, rust_fun "alloc::sync::{core::cmp::PartialEq<alloc::sync::Arc<@T>, alloc::sync::Arc<@T>>}::ne"
    (keepParams := [true, false])]
def alloc.sync.Arc.ne {T : Type _} (PartialEqInst : core.cmp.PartialEq T T)
    (x y : alloc.sync.Arc T) : Result Bool :=
  PartialEqInst.ne x y

@[expose, rust_fun "alloc::sync::{core::default::Default<alloc::sync::Arc<@T>>}::default"]
def alloc.sync.Arc.default {T : Type _} (DefaultInst : core.default.Default T) :
    Result (alloc.sync.Arc T) :=
  DefaultInst.default

@[expose, rust_fun "alloc::sync::{core::convert::From<alloc::sync::Arc<[@T]>, alloc::vec::Vec<@T>>}::from" -canFail
    (keepParams := [true, false]) (keepTraitClauses := [false])]
def alloc.sync.Arc.from_vec {T : Type _} (v : alloc.vec.Vec T) : alloc.sync.Arc (Slice T) :=
  v.slice

@[expose, reducible, rust_trait_impl "core::clone::Clone<alloc::sync::Arc<@T>>"
    (keepParams := [true, false]) (keepTraitClauses := [false])]
def core.clone.CloneArc (T : Type _) : core.clone.Clone (alloc.sync.Arc T) := {
  clone x := ok (alloc.sync.Arc.clone x)
}

@[expose, reducible, rust_trait_impl "core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>"
    (keepParams := [true, false])]
def core.ops.deref.DerefArc (T : Type _) : core.ops.deref.Deref (alloc.sync.Arc T) T := {
  deref x := ok (alloc.sync.Arc.deref x)
}

@[expose, reducible, rust_trait_impl "core::convert::AsRef<alloc::sync::Arc<@T>, @T>"
    (keepParams := [true, false])]
def core.convert.AsRefArc (T : Type _) : core.convert.AsRef (alloc.sync.Arc T) T := {
  as_ref x := ok (alloc.sync.Arc.as_ref x)
}

@[expose, reducible, rust_trait_impl "core::cmp::PartialEq<alloc::sync::Arc<@T>, alloc::sync::Arc<@T>>"
    (keepParams := [true, false])]
def core.cmp.PartialEqArc {T : Type _} (PartialEqInst : core.cmp.PartialEq T T) :
    core.cmp.PartialEq (alloc.sync.Arc T) (alloc.sync.Arc T) := {
  eq := alloc.sync.Arc.eq PartialEqInst
  ne := alloc.sync.Arc.ne PartialEqInst
}

@[expose, reducible, rust_trait_impl "core::default::Default<alloc::sync::Arc<@T>>"]
def core.default.DefaultArc {T : Type _} (DefaultInst : core.default.Default T) :
    core.default.Default (alloc.sync.Arc T) := {
  default := alloc.sync.Arc.default DefaultInst
}

end Aeneas.Std
