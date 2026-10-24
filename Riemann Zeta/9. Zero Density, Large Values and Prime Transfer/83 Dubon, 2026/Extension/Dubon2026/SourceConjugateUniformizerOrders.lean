import Dubon2026.SourceConjugateUniformizerPolynomial
import Mathlib.FieldTheory.Galois.Basic

/-! The conjugate polynomial has integral fixed coefficients and its
constant coefficient has order equal to the inertia group cardinality.
These supply the actual polynomial inputs, rather than assumed polynomial
certificates, in the conditional local wild different estimate for DUB-17/18. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial IntermediateField
variable {K F G : Type*} [Field K] [Field F] [Algebra K F] [Group G] [Fintype G]

private theorem ord_product_nonzero (v : Place K F) {ι : Type*} (s : Finset ι)
    (f : ι → F) (h : ∀ i ∈ s, f i ≠ 0) :
    v.ord (∏ i ∈ s, f i) = ∑ i ∈ s, v.ord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (h a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

theorem conjugateUniformizerPolynomial_coeff_fixed (ρ : G →* (F ≃ₐ[K] F))
    (t : F) (k : ℕ) :
    (conjugateUniformizerPolynomial ρ t).coeff k ∈ fixedField ρ.range := by
  rw [mem_fixedField_iff]
  rintro _ ⟨σ, rfl⟩
  have h := congrArg (fun f : F[X] => f.coeff k)
    (conjugateUniformizerPolynomial_map ρ t σ)
  simpa only [coeff_map] using h

theorem conjugateUniformizerPolynomial_constant_order (v : Place K F)
    (ρ : G →* (F ≃ₐ[K] F)) (t : F) (ht : ∀ σ, v.ord (ρ σ t) = 1) :
    v.ord ((conjugateUniformizerPolynomial ρ t).coeff 0) = (Nat.card G : ℤ) := by
  have hne : ∀ σ, ρ σ t ≠ 0 := by
    intro σ h
    have := ht σ
    rw [h, v.ord_zero] at this
    exact zero_ne_one this
  rw [coeff_zero_eq_eval_zero, conjugateUniformizerPolynomial, eval_prod]
  simp only [eval_sub, eval_X, eval_C, zero_sub]
  rw [ord_product_nonzero v Finset.univ _ (fun σ _ => neg_ne_zero.mpr (hne σ))]
  have hneg : ∀ σ, v.ord (-(ρ σ t)) = 1 := by
    intro σ
    simpa only [Place.ord, Valuation.map_neg] using ht σ
  simp only [hneg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]

theorem conjugateUniformizerPolynomial_derivative_order (v : Place K F) [DecidableEq G]
    (ρ : G →* (F ≃ₐ[K] F)) (t : F)
    (h : (conjugateUniformizerPolynomial ρ t).derivative.eval t ≠ 0) :
    v.ord ((conjugateUniformizerPolynomial ρ t).derivative.eval t) =
      ∑ σ ∈ Finset.univ.erase (1 : G), v.ord (t - ρ σ t) := by
  rw [conjugateUniformizerPolynomial_derivative_eval] at h ⊢
  exact ord_product_nonzero v _ _ (Finset.prod_ne_zero_iff.mp h)

end
end Dubon2026.SourceCurve
