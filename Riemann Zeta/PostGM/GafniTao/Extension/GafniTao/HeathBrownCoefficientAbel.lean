import GafniTao.HeathBrownCoefficientVariation

/-!
# The second Abel summation in Heath-Brown Lemma 1

This file applies finite Abel summation to the literal coefficient-change
weight.  It compares the Weyl sum at a cell centre with Weyl sums at an
arbitrary point of that same cell, retaining every partial sum and the exact
variation coefficient `2π k²/H`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def heathBrownNaturalMonomial
    (k h : ℕ) (α : HeathBrownCoefficientTorus k) : ℂ :=
  UnitAddTorus.mFourier
    (fun j : Fin (k - 1) => (h ^ ((j : ℕ) + 1) : ℤ)) α

theorem heathBrownWeylSum_eq_natural_sum
    (k Q : ℕ) (α : HeathBrownCoefficientTorus k) :
    heathBrownWeylSum k Q α =
      ∑ h ∈ Finset.Icc 1 Q, heathBrownNaturalMonomial k h α := by
  unfold heathBrownWeylSum fordVinogradovWeylSum
  rw [ford_sum_Icc_one_eq_fin]
  apply Finset.sum_congr rfl
  intro h hh
  unfold heathBrownNaturalMonomial fordVinogradovMonomial
    fordVinogradovExponent
  congr 2

theorem heathBrownNaturalMonomial_eq_center_mul_displacementPhase
    {k h : ℕ} (c α : HeathBrownCoefficientTorus k) :
    heathBrownNaturalMonomial k h α =
      heathBrownNaturalMonomial k h c *
        heathBrownPhase (heathBrownDisplacementPolynomial c α h) := by
  have hcoord (j : Fin (k - 1)) :
      α j = c j +
        ((heathBrownCoefficientDisplacement c α j : ℝ) : UnitAddCircle) :=
    (coe_center_add_heathBrownCoefficientDisplacement c α j).symm
  unfold heathBrownNaturalMonomial UnitAddTorus.mFourier
  change (∏ j : Fin (k - 1),
      fourier (h ^ ((j : ℕ) + 1) : ℤ) (α j)) = _
  simp_rw [hcoord, fourier_add_point]
  change (∏ j : Fin (k - 1),
      fourier (h ^ ((j : ℕ) + 1) : ℤ) (c j) *
        fourier (h ^ ((j : ℕ) + 1) : ℤ)
          ((heathBrownCoefficientDisplacement c α j : ℝ) : UnitAddCircle)) =
    (∏ j : Fin (k - 1),
      fourier (h ^ ((j : ℕ) + 1) : ℤ) (c j)) * _
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [heathBrownPhase_eq_fordAdditiveCharacter]
  unfold heathBrownDisplacementPolynomial
  rw [fordAdditiveCharacter_sum Finset.univ]
  apply Finset.prod_congr rfl
  intro j hj
  rw [fourier_coe_apply]
  unfold fordAdditiveCharacter
  congr 1
  push_cast
  ring

theorem heathBrownCoefficientWeight_mul_naturalMonomial
    {k h : ℕ} (c α : HeathBrownCoefficientTorus k) :
    heathBrownCoefficientWeight c α h *
        heathBrownNaturalMonomial k h α =
      heathBrownNaturalMonomial k h c := by
  rw [heathBrownNaturalMonomial_eq_center_mul_displacementPhase c α]
  unfold heathBrownCoefficientWeight
  have hcancel :
      heathBrownPhase (-heathBrownDisplacementPolynomial c α h) *
          heathBrownPhase (heathBrownDisplacementPolynomial c α h) = 1 := by
    rw [← heathBrownPhase_add, neg_add_cancel,
      heathBrownPhase_eq_fordAdditiveCharacter]
    simp [fordAdditiveCharacter]
  calc
    heathBrownPhase (-heathBrownDisplacementPolynomial c α h) *
        (heathBrownNaturalMonomial k h c *
          heathBrownPhase (heathBrownDisplacementPolynomial c α h)) =
      heathBrownNaturalMonomial k h c *
        (heathBrownPhase (-heathBrownDisplacementPolynomial c α h) *
          heathBrownPhase (heathBrownDisplacementPolynomial c α h)) := by ring
    _ = heathBrownNaturalMonomial k h c := by rw [hcancel, mul_one]

theorem heathBrown_centerWeyl_eq_weighted_cellWeyl
    (k Q : ℕ) (c α : HeathBrownCoefficientTorus k) :
    heathBrownWeylSum k Q c =
      ∑ h ∈ Finset.Icc 1 Q,
        heathBrownCoefficientWeight c α h *
          heathBrownNaturalMonomial k h α := by
  rw [heathBrownWeylSum_eq_natural_sum]
  apply Finset.sum_congr rfl
  intro h hh
  exact (heathBrownCoefficientWeight_mul_naturalMonomial c α).symm

theorem heathBrown_centerWeyl_abel_identity
    {k Q : ℕ} (hQ : 1 ≤ Q) (c α : HeathBrownCoefficientTorus k) :
    heathBrownWeylSum k Q c =
      heathBrownCoefficientWeight c α Q * heathBrownWeylSum k Q α +
        ∑ j ∈ Finset.Ico 1 Q,
          (heathBrownCoefficientWeight c α j -
            heathBrownCoefficientWeight c α (j + 1)) *
              heathBrownWeylSum k j α := by
  rw [heathBrown_centerWeyl_eq_weighted_cellWeyl]
  rw [heathBrown_source_abel_identity
    (fun h => heathBrownCoefficientWeight c α h)
    (fun h => heathBrownNaturalMonomial k h α) hQ]
  rw [← heathBrownWeylSum_eq_natural_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [← heathBrownWeylSum_eq_natural_sum]

/-- Norm form of the exact second Abel summation. -/
theorem norm_heathBrown_centerWeyl_le
    {k H Q : ℕ} (hH : 2 ≤ H) (hQ : 1 ≤ Q) (hQH : Q ≤ H)
    {f : ℝ → ℝ} {n : ℝ} {α : HeathBrownCoefficientTorus k}
    (hα : α ∈ heathBrownCoefficientCell k H f n) :
    ‖heathBrownWeylSum k Q (heathBrownCoefficientCenter k f n)‖ ≤
      ‖heathBrownWeylSum k Q α‖ +
        (2 * Real.pi * ((k : ℝ) ^ 2 / H)) *
          ∑ j ∈ Finset.Ico 1 Q, ‖heathBrownWeylSum k j α‖ := by
  rw [heathBrown_centerWeyl_abel_identity hQ]
  calc
    ‖heathBrownCoefficientWeight (heathBrownCoefficientCenter k f n) α Q *
          heathBrownWeylSum k Q α +
        ∑ j ∈ Finset.Ico 1 Q,
          (heathBrownCoefficientWeight (heathBrownCoefficientCenter k f n) α j -
            heathBrownCoefficientWeight (heathBrownCoefficientCenter k f n) α (j + 1)) *
              heathBrownWeylSum k j α‖ ≤
      ‖heathBrownCoefficientWeight (heathBrownCoefficientCenter k f n) α Q *
          heathBrownWeylSum k Q α‖ +
        ‖∑ j ∈ Finset.Ico 1 Q,
          (heathBrownCoefficientWeight (heathBrownCoefficientCenter k f n) α j -
            heathBrownCoefficientWeight (heathBrownCoefficientCenter k f n) α (j + 1)) *
              heathBrownWeylSum k j α‖ := norm_add_le _ _
    _ ≤ ‖heathBrownWeylSum k Q α‖ +
        ∑ j ∈ Finset.Ico 1 Q,
          (2 * Real.pi * ((k : ℝ) ^ 2 / H)) *
            ‖heathBrownWeylSum k j α‖ := by
      apply add_le_add
      · rw [norm_mul, norm_heathBrownCoefficientWeight, one_mul]
      · calc
          ‖∑ j ∈ Finset.Ico 1 Q,
              (heathBrownCoefficientWeight
                  (heathBrownCoefficientCenter k f n) α j -
                heathBrownCoefficientWeight
                  (heathBrownCoefficientCenter k f n) α (j + 1)) *
                heathBrownWeylSum k j α‖ ≤
            ∑ j ∈ Finset.Ico 1 Q,
              ‖(heathBrownCoefficientWeight
                  (heathBrownCoefficientCenter k f n) α j -
                heathBrownCoefficientWeight
                  (heathBrownCoefficientCenter k f n) α (j + 1)) *
                heathBrownWeylSum k j α‖ := norm_sum_le _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_mul, norm_sub_rev]
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            exact norm_heathBrownCoefficientWeight_succ_sub_le hH hα
              ((Finset.mem_Ico.mp hj).2.trans_le hQH)
    _ = _ := by rw [← Finset.mul_sum]

#print axioms heathBrownWeylSum_eq_natural_sum
#print axioms heathBrownNaturalMonomial_eq_center_mul_displacementPhase
#print axioms heathBrownCoefficientWeight_mul_naturalMonomial
#print axioms heathBrown_centerWeyl_abel_identity
#print axioms norm_heathBrown_centerWeyl_le

end

end GafniTao
