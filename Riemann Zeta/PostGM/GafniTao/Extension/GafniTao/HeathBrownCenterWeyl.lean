import GafniTao.HeathBrownWeylMoment
import GafniTao.FordLemma51Fibers

/-!
# The Taylor-coefficient centre and the complete Weyl sum

At the centre of the coefficient cell, Ford's torus Weyl sum is exactly the
reduced Taylor-polynomial sum.  This records the convention bridge between
derivative order `j`, the `Fin (k-1)` coordinate `j-1`, and the source range
`1 <= h <= H`.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

theorem heathBrownReducedTaylorPolynomial_eq_fin_sum
    {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ) (n x : ℝ) :
    heathBrownReducedTaylorPolynomial k f n x =
      ∑ j : Fin (k - 1),
        heathBrownDerivativeCoordinate f ((j : ℕ) + 1) n *
          x ^ ((j : ℕ) + 1) := by
  unfold heathBrownReducedTaylorPolynomial heathBrownDerivativeCoordinate
  have hset : Finset.Ico 1 k = Finset.Icc 1 (k - 1) := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hset, ford_sum_Icc_one_eq_fin]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem fordVinogradovMonomial_center_eq_phase
    {k H : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ) (n : ℝ) (h : Fin H) :
    fordVinogradovMonomial h (heathBrownCoefficientCenter k f n) =
      heathBrownPhase
        (heathBrownReducedTaylorPolynomial k f n ((h : ℕ) + 1)) := by
  rw [heathBrownReducedTaylorPolynomial_eq_fin_sum hk]
  rw [heathBrownPhase_eq_fordAdditiveCharacter]
  rw [fordAdditiveCharacter_sum Finset.univ]
  unfold fordVinogradovMonomial UnitAddTorus.mFourier fordVinogradovExponent
  change
    (∏ j : Fin (k - 1),
      fourier (((h : ℕ) + 1) ^ ((j : ℕ) + 1) : ℤ)
        (heathBrownCoefficientCenter k f n j)) = _
  apply Finset.prod_congr rfl
  intro j hj
  unfold heathBrownCoefficientCenter
  rw [fourier_coe_apply]
  unfold fordAdditiveCharacter heathBrownDerivativeCoordinate
  congr 1
  push_cast
  ring

theorem heathBrownWeylSum_center_eq_reducedTaylorPolynomialSum
    {k : ℕ} (hk : 1 ≤ k) (H : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    heathBrownWeylSum k H (heathBrownCoefficientCenter k f n) =
      heathBrownReducedTaylorPolynomialSum k H f n := by
  unfold heathBrownWeylSum fordVinogradovWeylSum
    heathBrownReducedTaylorPolynomialSum
  rw [ford_sum_Icc_one_eq_fin]
  apply Finset.sum_congr rfl
  intro h hh
  simpa only [Nat.cast_add, Nat.cast_one] using
    fordVinogradovMonomial_center_eq_phase hk f n h

theorem norm_heathBrownWeylSum_center_eq_TaylorPolynomialSum
    {k : ℕ} (hk : 1 ≤ k) (H : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    ‖heathBrownWeylSum k H (heathBrownCoefficientCenter k f n)‖ =
      ‖heathBrownTaylorPolynomialSum k H f n‖ := by
  rw [heathBrownWeylSum_center_eq_reducedTaylorPolynomialSum hk]
  exact (norm_heathBrownTaylorPolynomialSum_eq_reduced hk H f n).symm

#print axioms heathBrownReducedTaylorPolynomial_eq_fin_sum
#print axioms fordVinogradovMonomial_center_eq_phase
#print axioms heathBrownWeylSum_center_eq_reducedTaylorPolynomialSum
#print axioms norm_heathBrownWeylSum_center_eq_TaylorPolynomialSum

end

end GafniTao
