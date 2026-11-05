module
public import Aeneas.Std.Scalar
public import Aeneas.Std.Slice
public import Aeneas.Std.StringDef
public section

namespace Aeneas.Std

instance : DecidableEq Str := inferInstanceAs (DecidableEq (Slice U8))

/-- `bs.toList` has the same length as `bs`. -/
theorem ByteArray.length_toList (bs : ByteArray) :
    bs.toList.length = bs.size := by
  have loop_length :
      ∀ (i : Nat) (r : List UInt8), i ≤ bs.size →
        (ByteArray.toList.loop bs i r).length = (bs.size - i) + r.length := by
    intro i r hi
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      have hi' : i + 1 ≤ bs.size := by scalar_tac
      rw [ih hi']
      simp; scalar_tac
    | case2 i r h =>
      simp; scalar_tac
  unfold ByteArray.toList
  rw [loop_length 0 [] (Nat.zero_le _)]
  simp

/-- The `str` made of the UTF-8 encoding of `s`. -/
@[expose]
def toStrOfLe (s : String) (h : s.toByteArray.size ≤ U32.max) : Str :=
  .from (s.toByteArray.toList.map
    (fun x => ⟨ x.toNat, by cases x; simp only [UInt8.toNat_ofBitVec, UScalarTy.U8_numBits_eq, Nat.reducePow]; omega  ⟩))
    (by
      simp only [UScalarTy.U8_numBits_eq, Nat.reducePow, Fin.mk_uInt8ToNat, BitVec.ofFin_uInt8ToFin,
        List.length_map]
      rw [ByteArray.length_toList]
      exact h.trans (by scalar_tac))

/-- Convert a Lean `String` literal to a Rust `str`. The bound on the length of
    the encoding is checked by the definition rather than proved where the
    literal is written: the proof (by evaluation in the kernel) costs time and
    recursion depth proportional to the length of the literal. The encoding of a
    Rust string literal always fits: the empty `str` in the other case is never
    reached. The definition is irreducible so that the elaboration of the
    literals does not evaluate the check either (use `toStr_eq`). -/
@[expose, irreducible]
def toStr (s : String) : Str :=
  if h : s.toByteArray.size ≤ U32.max then toStrOfLe s h else .from [] (by simp)

theorem toStr_eq (s : String) (h : s.toByteArray.size ≤ U32.max) :
    toStr s = toStrOfLe s h := by
  unfold toStr
  exact dite_eq_left h

example : Str := toStr "hello"
example : Str := toStr "héllo ∀"
example : Str := toStr ""
example : toStr "héllo" = toStrOfLe "héllo" (by rw [U32.max_eq]; decide +kernel) := toStr_eq _ _

end Aeneas.Std
