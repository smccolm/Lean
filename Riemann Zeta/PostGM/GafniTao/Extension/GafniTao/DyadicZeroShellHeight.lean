import GafniTao.DyadicZeroShellBounded

/-!
# Heights of members of the dyadic zero-shell cover

Every noncentral member has inner height a power of two indexed below the
base-two logarithm of `ceil T`.  This file records the exact comparison with
`ceil T`; the central member is handled separately.  The result is the scale
bridge needed when four independently selected source colours are assembled
back at the physical height `T`.
-/

namespace GafniTao

noncomputable section

/-- The literal inner height of every cover member is at most `ceil T` once
`T >= 1`. -/
theorem dyadicZeroShellInnerHeight_le_ceil
    {T : Real} (hT : 1 <= T)
    (i : Fin (dyadicZeroShellCount T)) :
    dyadicZeroShellInnerHeight i <= (Nat.ceil T : Real) := by
  have hCeilOne : 1 <= Nat.ceil T := by
    exact_mod_cast hT.trans (Nat.le_ceil T)
  by_cases hi : i.val = 0
  · simp only [dyadicZeroShellInnerHeight, hi, if_true]
    exact_mod_cast hCeilOne
  · simp only [dyadicZeroShellInnerHeight, hi, if_false]
    have hiIndex : i.val - 1 <= Nat.log 2 (Nat.ceil T) := by
      have hiLt : i.val < Nat.log 2 (Nat.ceil T) + 2 := by
        simpa only [dyadicZeroShellCount] using i.isLt
      omega
    have hPowIndex : 2 ^ (i.val - 1) <=
        2 ^ Nat.log 2 (Nat.ceil T) :=
      Nat.pow_le_pow_right (by omega) hiIndex
    have hPowLog : 2 ^ Nat.log 2 (Nat.ceil T) <= Nat.ceil T :=
      Nat.pow_log_le_self 2 (by omega)
    exact_mod_cast hPowIndex.trans hPowLog

/-- A slightly coarser comparison directly with the physical height. -/
theorem dyadicZeroShellInnerHeight_le_two_mul
    {T : Real} (hT : 1 <= T)
    (i : Fin (dyadicZeroShellCount T)) :
    dyadicZeroShellInnerHeight i <= 2 * T := by
  have hCeil : (Nat.ceil T : Real) <= 2 * T := by
    have hRaw := Nat.ceil_lt_add_one (show 0 <= T by linarith)
    linarith
  exact (dyadicZeroShellInnerHeight_le_ceil hT i).trans hCeil

#print axioms dyadicZeroShellInnerHeight_le_ceil
#print axioms dyadicZeroShellInnerHeight_le_two_mul

end

end GafniTao
