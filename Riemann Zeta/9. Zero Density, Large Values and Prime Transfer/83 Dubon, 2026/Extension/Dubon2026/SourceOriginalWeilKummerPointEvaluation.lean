import Dubon2026.SourceOriginalWeilKummerPointDifference

/-! DUB-17/18 -> finite Weil detection -> the nontrivial root multiplier.
The literal divisor product on the actual point difference equals the
Kummer eigenvalue. This is the evaluation used by the norm detecting class.
It does not assume or prove the needed division of that class. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve Polynomial
attribute [local instance] originalNormCharZero
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]
variable (n : ℕ) (f : modularFunctionFieldOver N L)
local notation "FF" => modularFunctionFieldOver N L
local notation "E" => Polynomial.SplittingField (X ^ n - C f)

theorem originalWeilKummerPointDifference_eval (σ : E ≃ₐ[FF] E) (w : Place L E)
    (h : E) (hh : h ≠ 0) (ζ : L) (hσ : σ h = algebraMap L E ζ * h)
    (ho : w.ord h = 0) :
    originalWeilKummerDivisorEval N L n f h
      (originalWeilKummerPointDifference N L n f σ w).val = ζ := by
  classical
  let hw := originalWeilKummerCover_residue_bijective N L n f
  let w' := w.comapEquiv (σ.restrictScalars L)
  have hm : h ∈ w.toValuationSubring := w.mem_of_ord_nonneg ho.ge
  have hn : w.rationalEval (hw w) h ≠ 0 := w.rationalEval_ne_zero_of_ord_eq_zero (hw w) hh ho
  have hζ : ζ ≠ 0 := by
    intro hz
    rw [hz, map_zero, zero_mul] at hσ
    exact hh ((map_eq_zero σ).mp hσ)
  have he : w'.rationalEval (hw w') h = ζ * w.rationalEval (hw w) h :=
    originalWeilKummerPoint_eval N L n f σ w h ζ hσ hm
  have hn' : w'.rationalEval (hw w') h ≠ 0 := by rw [he]; exact mul_ne_zero hζ hn
  have hsupport : ∀ v, v ∈ (Finsupp.single w' (1 : ℤ)).support ∨
      v ∈ (Finsupp.single w (-1 : ℤ)).support → v.rationalEval (hw v) h ≠ 0 := by
    intro v hv
    rcases hv with hv | hv
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hv)]
      exact hn'
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hv)]
      exact hn
  change rationalDivisorEval hw h (Finsupp.single w' 1 - Finsupp.single w 1) = ζ
  rw [sub_eq_add_neg (Finsupp.single w' (1 : ℤ)) (Finsupp.single w (1 : ℤ)),
    ← Finsupp.single_neg,
    rationalDivisorEval_add hw h _ _ hsupport,
    rationalDivisorEval_single, rationalDivisorEval_single, he,
    zpow_one, zpow_neg_one, mul_inv_cancel_right₀ hn]

end
end Dubon2026.SourceFunctionField
