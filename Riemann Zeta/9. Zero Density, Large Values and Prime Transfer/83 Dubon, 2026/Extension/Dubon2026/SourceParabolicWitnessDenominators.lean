import Dubon2026.SourceBinaryCocycleDenominators

/-! DUB17/18 -> original all-weight association -> one integral
parabolic denominator over the actual finite cusp-orbit representatives.
Reuse verbatim the existing finite-family polynomial denominator proof
from SourceBinaryCocycleDenominators. Only its finite-family statement
is exposed here; no new localization or polynomial-basis theory is added. -/
namespace Dubon2026
noncomputable section
open MvPolynomial

private def integralPolynomial (w : ℕ) (v : homogeneousSubmodule (Fin 2) ℚ w) : Prop :=
  ∃ z : homogeneousSubmodule (Fin 2) ℤ w,
    homogeneousCoefficientMap w (Int.castRingHom ℚ) z = v

theorem sourceParabolicWitness_family_integerMultiple {ι : Type} (w : ℕ)
    (s : Finset ι) (v : ι → homogeneousSubmodule (Fin 2) ℚ w) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ i ∈ s, integralPolynomial w ((d : ℚ) • v i) := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors ℤ)
    (s.biUnion fun i => (v i).val.support.image fun m => (v i).val.coeff m)
  choose! a ha using hb
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun i hi => ⟨⟨
    ∑ m ∈ (v i).val.support, monomial m (a ((v i).val.coeff m)), ?_⟩, ?_⟩⟩
  · rw [mem_homogeneousSubmodule]
    refine IsHomogeneous.sum _ _ _ fun m hm => ?_
    have hv := (mem_homogeneousSubmodule w _).mp (v i).property
    refine isHomogeneous_monomial _ ?_
    rw [Finsupp.degree_eq_weight_one]
    exact hv (mem_support_iff.mp hm)
  · apply Subtype.ext
    change map (Int.castRingHom ℚ)
      (∑ m ∈ (v i).val.support, monomial m (a ((v i).val.coeff m))) =
        (b.val : ℚ) • (v i).val
    simp only [map_sum, map_monomial]
    conv_rhs => rw [(v i).val.as_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    have h := ha _ (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image_of_mem _ hm⟩)
    rw [smul_monomial, eq_intCast]
    rw [eq_intCast] at h
    rw [h, zsmul_eq_mul, smul_eq_mul]


end
end Dubon2026
