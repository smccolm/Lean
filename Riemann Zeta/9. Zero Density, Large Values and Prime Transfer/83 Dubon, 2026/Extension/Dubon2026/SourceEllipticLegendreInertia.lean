import Dubon2026.SourceEllipticLegendreGoodModel
import Mathlib.RingTheory.Valuation.RamificationGroup

/-! The finite Galois Legendre good-model stage and its faithful inertia.
The generators are the actual two-torsion abscissae and square roots of
their nonzero differences. This realizes the model and action required by
the positive-characteristic exceptional-fiber census, reverse genus and
good reduction in DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, finite Legendre model proof.
Native valuation-ring inertia and the existing explicit good model are reused.
No characteristic-zero Hahn-series route is introduced. -/
namespace Dubon2026.SourceEllipticLegendreStage
open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing Polynomial
open Dubon2026.SourceEllipticLegendre
open scoped Pointwise
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
section Inertia

variable {M : Type*} [Field M] [Algebra F M] (A : ValuationSubring M)

lemma sub_mem_maximalIdeal_of_inertia {σ : M ≃ₐ[F] M} (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) (a : A) :
    A.valuation (σ a - a) < 1 := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A) ⟨σ, hσ⟩ = 1 := hσI
  have hσa : σ a ∈ A := by
    have h := ValuationSubring.smul_mem_pointwise_smul σ (a : M) A a.2
    rwa [MulAction.mem_stabilizer_iff.mp hσ] at h
  have hres : residue A ⟨σ a, hσa⟩ = residue A a := by
    have : residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup F) • a) = residue A a := by
      rw [IsLocalRing.ResidueField.residue_smul]
      show MulSemiringAction.toRingAut (A.decompositionSubgroup F) (ResidueField A) ⟨σ, hσ⟩
        (residue A a) = residue A a
      rw [h1]; rfl
    exact this
  have hmem : (⟨σ a, hσa⟩ : A) - a ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hres, sub_self]
  exact (A.valuation_lt_one_iff _).mp hmem

lemma eq_of_inertia_of_sq_eq (h2 : IsUnit (2 : A)) {σ : M ≃ₐ[F] M} (hσ : σ ∈ A.decompositionSubgroup F)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F) {x : M}
    (hx : A.valuation x = 1) (hsq : σ (x ^ 2) = x ^ 2) : σ x = x := by
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  have h := sub_mem_maximalIdeal_of_inertia A hσ hσI ⟨x, hxA⟩
  simp only at h

  have hpm : (σ x - x) * (σ x + x) = 0 := by
    have : σ x ^ 2 = x ^ 2 := by rw [← map_pow, hsq]
    linear_combination this
  rcases mul_eq_zero.mp hpm with h0 | h0
  · exact sub_eq_zero.mp h0
  · exfalso
    have hσx : σ x = -x := eq_neg_of_add_eq_zero_left h0
    rw [hσx, show -x - x = -(2 * x) by ring, Valuation.map_neg, Valuation.map_mul, hx, mul_one] at h
    have h2v : A.valuation ((2 : A) : M) = 1 := (A.valuation_eq_one_iff _).mp h2
    have : A.valuation (2 : M) = 1 := h2v
    rw [this] at h
    exact lt_irrefl _ h

lemma val_eq_one_of_sq {x : M} (h : A.valuation (x ^ 2) = 1) : A.valuation x = 1 := by
  rw [Valuation.map_pow] at h
  rcases lt_trichotomy (A.valuation x) 1 with h1 | h1 | h1
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' h1 (by norm_num)))
  · exact h1
  · exact absurd h (ne_of_gt (one_lt_pow₀ h1 (by norm_num)))

end Inertia


end
end Dubon2026.SourceEllipticLegendreStage
