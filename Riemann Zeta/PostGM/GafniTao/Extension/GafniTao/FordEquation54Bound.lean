import GafniTao.FordEquation54Interchange
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Ford Lemma 5.1: the nonnegative majorant in equation (5.4)

This file takes norms in the exact lattice/tent identity.  The unit phases
attached to the two source tuples are removed only after their norms have been
proved to be one.  The resulting right hand side is Ford's literal product of
periodic tents, with its full scalar retained.
-/

open Finset
open scoped BigOperators NNReal

namespace GafniTao

noncomputable section

/-- The literal nonnegative product attached to a tuple pair after taking
absolute values in Ford's equation (5.4). -/
def fordLemma51TuplePairTentMajorant
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) : ℝ :=
  ∏ j : Fin k, fordLemma51CoordinateTentFactor k r M j
    (fordLemma51DifferenceCoordinate k t z
      (fordLemma51DifferenceVector k s B x y))

/-- The product of the literal tents after the common scalar in (5.4) has
been factored out. -/
def fordLemma51TuplePairTentProduct
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) : ℝ :=
  ∏ j : Fin k,
    fordTent
      (fordLemma51DifferenceCoordinate k t z
        (fordLemma51DifferenceVector k s B x y) j)
      (1 / (2 * ((r * M ^ ((j : ℕ) + 1) : ℕ) : ℝ)))

theorem fordLemma51CoordinateTentFactor_nonneg
    (k r M : ℕ) (j : Fin k) (y : Fin k → ℝ) :
    0 ≤ fordLemma51CoordinateTentFactor k r M j y := by
  unfold fordLemma51CoordinateTentFactor
  apply mul_nonneg
  · apply div_nonneg
    · exact mul_nonneg (sq_nonneg Real.pi) (Nat.cast_nonneg _)
    · norm_num
  · exact fordTent_nonneg _ _

theorem norm_fordLemma51CoordinateTentValue
    (k r M : ℕ) (j : Fin k) (y : Fin k → ℝ) :
    ‖fordLemma51CoordinateTentValue k r M j y‖ =
      fordLemma51CoordinateTentFactor k r M j y := by
  unfold fordLemma51CoordinateTentValue
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (fordLemma51CoordinateTentFactor_nonneg k r M j y)]

theorem fordLemma51TuplePairTentMajorant_nonneg
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) :
    0 ≤ fordLemma51TuplePairTentMajorant k M r s B t z x y := by
  unfold fordLemma51TuplePairTentMajorant
  exact Finset.prod_nonneg fun j _hj =>
    fordLemma51CoordinateTentFactor_nonneg k r M j _

theorem norm_fordLemma51TuplePairTentTerm
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) :
    ‖fordLemma51TuplePairTentTerm k M r s B t z x y‖ =
      fordLemma51TuplePairTentMajorant k M r s B t z x y := by
  unfold fordLemma51TuplePairTentTerm fordLemma51TuplePairTentMajorant
  rw [norm_mul, norm_fordLemma51TupleCoefficient, one_mul, norm_prod]
  apply Finset.prod_congr rfl
  intro j _hj
  exact norm_fordLemma51CoordinateTentValue k r M j _

/-- Exact extraction of Ford's common scalar
`(pi^2 r / 2)^k M^kappa` from the tuple-pair product. -/
theorem fordLemma51TuplePairTentMajorant_eq_scalar_mul
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) :
    fordLemma51TuplePairTentMajorant k M r s B t z x y =
      (Real.pi ^ 2 * (r : ℝ) / 2) ^ k *
        (M : ℝ) ^ fordVinogradovKappa k *
          fordLemma51TuplePairTentProduct k M r s B t z x y := by
  unfold fordLemma51TuplePairTentMajorant fordLemma51TuplePairTentProduct
    fordLemma51CoordinateTentFactor fordVinogradovKappa
  rw [show (Real.pi ^ 2 * (r : ℝ) / 2) ^ k =
      ∏ _j : Fin k, (Real.pi ^ 2 * (r : ℝ) / 2) by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]]
  rw [show (M : ℝ) ^ (k * (k + 1) / 2) =
      ∏ j : Fin k, (M : ℝ) ^ ((j : ℕ) + 1) by
    rw [Finset.prod_pow_eq_pow_sum, sum_fin_degrees]]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _hj
  push_cast
  ring

theorem ford_pi_sq_div_two_le_five : Real.pi ^ 2 / 2 ≤ (5 : ℝ) := by
  have habs : |Real.pi| ≤ |(3.15 : ℝ)| := by
    rw [abs_of_pos Real.pi_pos, abs_of_pos (by norm_num)]
    exact Real.pi_lt_d2.le
  have hsq : Real.pi ^ 2 ≤ (3.15 : ℝ) ^ 2 := sq_le_sq.mpr habs
  norm_num at hsq ⊢
  linarith

theorem fordLemma51PiScalarPow_le
    (k r : ℕ) :
    (Real.pi ^ 2 * (r : ℝ) / 2) ^ k ≤ (5 * (r : ℝ)) ^ k := by
  apply pow_le_pow_left₀ (by positivity)
  calc
    Real.pi ^ 2 * (r : ℝ) / 2 =
        (Real.pi ^ 2 / 2) * (r : ℝ) := by ring
    _ ≤ 5 * (r : ℝ) :=
      mul_le_mul_of_nonneg_right ford_pi_sq_div_two_le_five (Nat.cast_nonneg r)

theorem fordLemma51TuplePairTentProduct_nonneg
    (k M r s : ℕ) (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) :
    0 ≤ fordLemma51TuplePairTentProduct k M r s B t z x y := by
  unfold fordLemma51TuplePairTentProduct
  exact Finset.prod_nonneg fun j _hj => fordTent_nonneg _ _

theorem fordLemma51TuplePairTentProduct_le_one
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ)
    (x y : FordLemma51BTuple s B) :
    fordLemma51TuplePairTentProduct k M r s B t z x y ≤ 1 := by
  unfold fordLemma51TuplePairTentProduct
  apply Finset.prod_le_one
  · intro j _hj
    exact fordTent_nonneg _ _
  · intro j _hj
    apply fordTent_le_one
    positivity

/-- Taking norms in the exact all-lattice identity produces Ford's
nonnegative tuple-pair tent majorant. -/
theorem fordLemma51WeightedLatticeTsum_le_tupleTentMajorantSum
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    (↑(∑' c : Fin k → ℤ,
        fordLemma51WeightProduct k r M c *
          ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^
            (2 * s)) : ℝ) ≤
      ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TuplePairTentMajorant k M r s B t z x y := by
  let L : ℝ≥0 := ∑' c : Fin k → ℤ,
    fordLemma51WeightProduct k r M c *
      ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s)
  have heq := fordLemma51WeightedLatticeTsum_eq_tupleTentSum
    (k := k) (s := s) hr hM B t z
  change (L : ℝ) ≤ _
  change ((L : ℝ) : ℂ) = _ at heq
  calc
    (L : ℝ) = ‖((L : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact NNReal.coe_nonneg L
    _ = ‖∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
          fordLemma51TuplePairTentTerm k M r s B t z x y‖ := by rw [heq]
    _ ≤ ∑ x : FordLemma51BTuple s B,
          ‖∑ y : FordLemma51BTuple s B,
            fordLemma51TuplePairTentTerm k M r s B t z x y‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x : FordLemma51BTuple s B,
          ∑ y : FordLemma51BTuple s B,
            ‖fordLemma51TuplePairTentTerm k M r s B t z x y‖ := by
      exact Finset.sum_le_sum fun x _hx => norm_sum_le _ _
    _ = ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
          fordLemma51TuplePairTentMajorant k M r s B t z x y := by
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro y _hy
      exact norm_fordLemma51TuplePairTentTerm k M r s B t z x y

/-- The exact finite moment `T` is bounded by the literal tent-product sum.
This is Ford's inequality before the resonant sets `D_j` are introduced. -/
theorem fordLemma51MomentT_le_tupleTentMajorantSum
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
      ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TuplePairTentMajorant k M r s B t z x y := by
  calc
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
        (↑(∑' c : Fin k → ℤ,
          fordLemma51WeightProduct k r M c *
            ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^
              (2 * s)) : ℝ) := by
      exact_mod_cast fordLemma51MomentT_le_weightedLatticeMoment hr hM B t z
    _ ≤ _ := fordLemma51WeightedLatticeTsum_le_tupleTentMajorantSum
      hr hM B t z

/-- Ford's tuple-tent inequality with the published elementary constant `5`.
The resonant support has not yet been counted here. -/
theorem fordLemma51MomentT_le_fiveScalar_tupleTentSum
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
      (5 * (r : ℝ)) ^ k * (M : ℝ) ^ fordVinogradovKappa k *
        (∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
          fordLemma51TuplePairTentProduct k M r s B t z x y) := by
  have hsumNonneg : 0 ≤
      ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
        fordLemma51TuplePairTentProduct k M r s B t z x y := by
    exact Finset.sum_nonneg fun x _hx => Finset.sum_nonneg fun y _hy =>
      fordLemma51TuplePairTentProduct_nonneg k M r s B t z x y
  calc
    (fordLemma51MomentT k M r s B t z : ℝ) ≤
        ∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
          fordLemma51TuplePairTentMajorant k M r s B t z x y :=
      fordLemma51MomentT_le_tupleTentMajorantSum hr hM B t z
    _ = ((Real.pi ^ 2 * (r : ℝ) / 2) ^ k *
          (M : ℝ) ^ fordVinogradovKappa k) *
        (∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
          fordLemma51TuplePairTentProduct k M r s B t z x y) := by
      simp_rw [fordLemma51TuplePairTentMajorant_eq_scalar_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Finset.mul_sum]
    _ ≤ ((5 * (r : ℝ)) ^ k *
          (M : ℝ) ^ fordVinogradovKappa k) *
        (∑ x : FordLemma51BTuple s B, ∑ y : FordLemma51BTuple s B,
          fordLemma51TuplePairTentProduct k M r s B t z x y) := by
      apply mul_le_mul_of_nonneg_right _ hsumNonneg
      exact mul_le_mul_of_nonneg_right (fordLemma51PiScalarPow_le k r)
        (by positivity)
    _ = _ := by ring

#print axioms fordLemma51CoordinateTentFactor_nonneg
#print axioms norm_fordLemma51CoordinateTentValue
#print axioms fordLemma51TuplePairTentMajorant_nonneg
#print axioms norm_fordLemma51TuplePairTentTerm
#print axioms fordLemma51TuplePairTentMajorant_eq_scalar_mul
#print axioms ford_pi_sq_div_two_le_five
#print axioms fordLemma51PiScalarPow_le
#print axioms fordLemma51TuplePairTentProduct_nonneg
#print axioms fordLemma51TuplePairTentProduct_le_one
#print axioms fordLemma51WeightedLatticeTsum_le_tupleTentMajorantSum
#print axioms fordLemma51MomentT_le_tupleTentMajorantSum
#print axioms fordLemma51MomentT_le_fiveScalar_tupleTentSum

end

end GafniTao
