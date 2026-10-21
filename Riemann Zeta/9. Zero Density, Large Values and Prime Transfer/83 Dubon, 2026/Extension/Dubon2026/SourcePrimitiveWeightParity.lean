import Dubon2026.PrimitiveCuspForms
import Mathlib.NumberTheory.ModularForms.Basic

/-! Original primitive forms supply the parity needed by weight-two reduction.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction -> the original binary degree is even. Pinned Mathlib's
odd-weight vanishing theorem applies to the actual congruence group;
normalization of the original primitive form excludes the zero form.
-/

namespace Dubon2026
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

/-- Every actual primitive form for the original trivial-character congruence
group has even integral weight, derived from its nonzero modular form. -/
theorem sourcePrimitive_weight_even {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) : Even k := by
  by_contra hk
  have hminus : (-1 : Matrix.GeneralLinearGroup (Fin 2) ℝ) ∈
      (Gamma0 Q).map (mapGL ℝ) := by
    refine ⟨-1, ?_, ?_⟩
    · change (-1 : SL(2, ℤ)) ∈ Gamma0 Q
      rw [Gamma0_mem]
      simp
    · ext i j
      simp [mapGL]
  have hzero := ModularForm.eq_zero_of_neg_one_mem hminus (Int.not_even_iff_odd.mp hk)
    (ModularFormClass.modularForm f.toCuspForm)
  apply primitiveCuspForm_ne_zero f
  ext z
  exact congrArg (fun g => g z) hzero

/-- The actual original binary degree k-2 is even at every source weight
at least two; no parity hypothesis is added to the primitive-form consumer. -/
theorem sourcePrimitive_binaryDegree_even {Q : ℕ} [NeZero Q] {k : ℤ}
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) : Even (k - 2).toNat := by
  obtain ⟨a, ha⟩ := sourcePrimitive_weight_even f
  refine ⟨(a - 1).toNat, ?_⟩
  omega

end Dubon2026
