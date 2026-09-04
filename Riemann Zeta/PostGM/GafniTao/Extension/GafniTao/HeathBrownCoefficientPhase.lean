import GafniTao.HeathBrownCellDisplacement

/-!
# The literal coefficient-change phase

For a coefficient vector `α` in a Heath-Brown cell, this file identifies the
exact real polynomial whose exponential changes the cell centre monomial into
the monomial at `α`.  This is the weight used in the second Abel summation.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

noncomputable def heathBrownDisplacementPolynomial
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (x : ℝ) : ℝ :=
  ∑ j : Fin (k - 1),
    heathBrownCoefficientDisplacement c α j * x ^ ((j : ℕ) + 1)

theorem fourier_add_point (m : ℤ) (x y : UnitAddCircle) :
    fourier m (x + y) = fourier m x * fourier m y := by
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
      induction y using QuotientAddGroup.induction_on with
      | _ y =>
          rw [← AddCircle.coe_add, fourier_coe_apply, fourier_coe_apply,
            fourier_coe_apply, ← Complex.exp_add]
          congr 1
          push_cast
          ring

theorem fordVinogradovMonomial_eq_center_mul_displacementPhase
    {k Q : ℕ} (c α : HeathBrownCoefficientTorus k) (h : Fin Q) :
    fordVinogradovMonomial h α =
      fordVinogradovMonomial h c *
        heathBrownPhase
          (heathBrownDisplacementPolynomial c α ((h : ℕ) + 1)) := by
  have hcoord (j : Fin (k - 1)) :
      α j = c j +
        ((heathBrownCoefficientDisplacement c α j : ℝ) : UnitAddCircle) := by
    exact (coe_center_add_heathBrownCoefficientDisplacement c α j).symm
  unfold fordVinogradovMonomial UnitAddTorus.mFourier fordVinogradovExponent
  change (∏ j : Fin (k - 1),
      fourier (((h : ℕ) + 1) ^ ((j : ℕ) + 1) : ℤ) (α j)) = _
  simp_rw [hcoord, fourier_add_point]
  change (∏ j : Fin (k - 1),
      fourier (((h : ℕ) + 1) ^ ((j : ℕ) + 1) : ℤ) (c j) *
        fourier (((h : ℕ) + 1) ^ ((j : ℕ) + 1) : ℤ)
          ((heathBrownCoefficientDisplacement c α j : ℝ) : UnitAddCircle)) =
    (∏ j : Fin (k - 1),
      fourier (((h : ℕ) + 1) ^ ((j : ℕ) + 1) : ℤ) (c j)) * _
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

noncomputable def heathBrownCoefficientWeight
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (q : ℕ) : ℂ :=
  heathBrownPhase (-heathBrownDisplacementPolynomial c α q)

theorem norm_heathBrownCoefficientWeight
    {k : ℕ} (c α : HeathBrownCoefficientTorus k) (q : ℕ) :
    ‖heathBrownCoefficientWeight c α q‖ = 1 := by
  exact norm_heathBrownPhase _

theorem heathBrownCoefficientWeight_mul_monomial
    {k Q : ℕ} (c α : HeathBrownCoefficientTorus k) (h : Fin Q) :
    heathBrownCoefficientWeight c α ((h : ℕ) + 1) *
        fordVinogradovMonomial h α =
      fordVinogradovMonomial h c := by
  rw [fordVinogradovMonomial_eq_center_mul_displacementPhase c α h]
  have hcancel :
      heathBrownPhase
          (-heathBrownDisplacementPolynomial c α ((h : ℕ) + 1)) *
        heathBrownPhase
          (heathBrownDisplacementPolynomial c α ((h : ℕ) + 1)) = 1 := by
    rw [← heathBrownPhase_add]
    rw [neg_add_cancel]
    rw [heathBrownPhase_eq_fordAdditiveCharacter]
    simp [fordAdditiveCharacter]
  unfold heathBrownCoefficientWeight
  simp only [Nat.cast_add, Nat.cast_one]
  calc
    heathBrownPhase
          (-heathBrownDisplacementPolynomial c α ((h : ℕ) + 1)) *
        (fordVinogradovMonomial h c *
          heathBrownPhase
            (heathBrownDisplacementPolynomial c α ((h : ℕ) + 1))) =
        fordVinogradovMonomial h c *
          (heathBrownPhase
              (-heathBrownDisplacementPolynomial c α ((h : ℕ) + 1)) *
            heathBrownPhase
              (heathBrownDisplacementPolynomial c α ((h : ℕ) + 1))) := by
      ring
    _ = fordVinogradovMonomial h c := by rw [hcancel, mul_one]

#print axioms fourier_add_point
#print axioms fordVinogradovMonomial_eq_center_mul_displacementPhase
#print axioms norm_heathBrownCoefficientWeight
#print axioms heathBrownCoefficientWeight_mul_monomial

end

end GafniTao
