import Dubon2026.SourceCurveSeparatingHurwitzCuspBound
import Dubon2026.SourceMarkedOriginalLocalDifferentials
import Dubon2026.SourceOriginalResidueCuspCount

/-! DUB-17/18 -> original all-weight association -> homogeneous Gamma1
realization -> original genus preservation -> reverse genus. Apply the proved
separating-coordinate Hurwitz bound to the actual original Gamma1 residue j.
Native degree preservation and cusp specialization remove the coordinate-degree
and residue-pole terms. No canonical degree, local generation, finite-field or
cusp-count certificate remains in the resulting original-field inequalities. -/
namespace Dubon2026.SourceFunctionField.MarkedChart
noncomputable section
open CongruenceSubgroup GammaOne SourceCurve KaehlerDifferential
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
  [CharP (IsLocalRing.ResidueField A) ℓ]
local notation "kk" => IsLocalRing.ResidueField A
local notation "F" => qExpFunctionFieldC kk (Gamma1 N)
private local instance : Algebra kk F := (F).toSubalgebra.algebra

private theorem original_pole_card_le (hℓN : ¬ ℓ ∣ N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk) :
    Nat.card {v : Place kk F // v.ord x < 0} ≤ Nat.card (CuspCounting.PolePlaces (Gamma1 N)) := by
  have he : x = ⟨jqModC kk, jqModC_mem_integralRatioField kk (Gamma1 N)⟩ := Subtype.ext hx
  rw [he]
  exact IntegralSlash.originalResidue_j_pole_card_le_complex A N ℓ hℓN

theorem original_hurwitz_differential_cusp_bound (hℓN : ¬ ℓ ∣ N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (S : Finset (Place kk F)) (hS : ∀ v ∈ S, 0 ≤ v.ord x) :
    (∑ v ∈ S, v.ordDifferential (D kk F x)) ≤
      2 * (genusFF kk F : ℤ) - 2 + ((plusMinus (Gamma1 N)).index : ℤ) +
        (Nat.card (CuspCounting.PolePlaces (Gamma1 N)) : ℤ) := by
  letI := valuation_residue_isAlgClosed A
  letI := original_coordinate_finite A N ℓ hℓN x hx
  letI := original_coordinate_isSeparable A N ℓ hℓN x hx
  have hxtr : Transcendental kk x := by
    intro h
    apply transcendental_jqModC kk
    rw [← hx]
    exact h.algHom (F).val
  have h := separating_hurwitz_differential_cusp_bound x hxtr
    (original_j_D_ne_zero A N x hx) S hS
  rw [original_coordinate_finrank_eq_index A N ℓ hℓN x hx] at h
  have hc : (Nat.card {v : Place kk F // v.ord x < 0} : ℤ) ≤
      (Nat.card (CuspCounting.PolePlaces (Gamma1 N)) : ℤ) := by
    exact_mod_cast original_pole_card_le A N ℓ hℓN x hx
  omega

theorem original_hurwitz_ramification_cusp_bound (hℓN : ¬ ℓ ∣ N)
    (x : F) (hx : (x : LaurentSeries kk) = jqModC kk)
    (S : Finset (Place kk F)) (a : Place kk F → kk)
    (hS : ∀ v ∈ S, 0 < v.ord (x - algebraMap kk F (a v))) :
    (∑ v ∈ S, (v.ord (x - algebraMap kk F (a v)) - 1)) ≤
      2 * (genusFF kk F : ℤ) - 2 + ((plusMinus (Gamma1 N)).index : ℤ) +
        (Nat.card (CuspCounting.PolePlaces (Gamma1 N)) : ℤ) := by
  letI := valuation_residue_isAlgClosed A
  letI := original_coordinate_finite A N ℓ hℓN x hx
  letI := original_coordinate_isSeparable A N ℓ hℓN x hx
  have hxtr : Transcendental kk x := by
    intro h
    apply transcendental_jqModC kk
    rw [← hx]
    exact h.algHom (F).val
  have h := separating_hurwitz_ramification_cusp_bound x hxtr
    (original_j_D_ne_zero A N x hx) S a hS
  rw [original_coordinate_finrank_eq_index A N ℓ hℓN x hx] at h
  have hc : (Nat.card {v : Place kk F // v.ord x < 0} : ℤ) ≤
      (Nat.card (CuspCounting.PolePlaces (Gamma1 N)) : ℤ) := by
    exact_mod_cast original_pole_card_le A N ℓ hℓN x hx
  omega

end
end Dubon2026.SourceFunctionField.MarkedChart
