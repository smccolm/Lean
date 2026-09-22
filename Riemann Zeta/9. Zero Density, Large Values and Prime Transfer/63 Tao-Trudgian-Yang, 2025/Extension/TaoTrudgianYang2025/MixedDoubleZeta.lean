import TaoTrudgianYang2025.HeathBrownDoubleZetaFinite
import Mathlib.Data.Real.Sqrt

/-!
# Mixed double-zeta Cauchy--Schwarz with both ordinate variables

The kernel is evaluated at `t - u`, as required by the Fourier expansion in
the frozen blueprint's `cauchy-schwarz` proof. Its printed display omits `u`;
we do not assert that different, generally false display. This module supplies
the finite mixed inequality needed before Bourgain's analytic selection step.
-/

open Complex Finset
open scoped ComplexConjugate
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

/-- The true mixed second moment, retaining the two ordinate sets. -/
def heathBrownMixedDifferenceMoment
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ) : ℝ :=
  ∑ t ∈ W, ∑ u ∈ U, ‖heathBrownDifferencePolynomial I a t u‖ ^ 2

/-- Finite correlation in the coefficient indices. -/
def heathBrownPhaseCorrelation (W : Finset ℝ) (n m : ℕ) : ℂ :=
  ∑ t ∈ W, star (heathBrownPhase n t) * heathBrownPhase m t

/-- Exact fourfold expansion; no absolute values are moved through a sum. -/
theorem heathBrownMixedDifferenceMoment_expansion
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ) :
    (heathBrownMixedDifferenceMoment I W U a : ℂ) =
      ∑ n ∈ I, ∑ m ∈ I, star (a n) * a m *
        heathBrownPhaseCorrelation W n m * star (heathBrownPhaseCorrelation U n m) := by
  unfold heathBrownMixedDifferenceMoment
  have hcast :
      ((∑ t ∈ W, ∑ u ∈ U, ‖heathBrownDifferencePolynomial I a t u‖ ^ 2 : ℝ) : ℂ) =
        ∑ t ∈ W, ∑ u ∈ U, ((‖heathBrownDifferencePolynomial I a t u‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast]
  simp_rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  unfold heathBrownDifferencePolynomial
  simp only [map_sum, map_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  let F : ℝ → ℝ → ℕ → ℕ → ℂ := fun t u n m =>
    star (a n) * star (heathBrownPhase n t) * star (star (heathBrownPhase n u)) *
      (a m * heathBrownPhase m t * star (heathBrownPhase m u))
  change (∑ t ∈ W, ∑ u ∈ U, ∑ n ∈ I, ∑ m ∈ I, F t u n m) = _
  calc
    _ = ∑ t ∈ W, ∑ n ∈ I, ∑ u ∈ U, ∑ m ∈ I, F t u n m := by
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.sum_comm
    _ = ∑ n ∈ I, ∑ t ∈ W, ∑ u ∈ U, ∑ m ∈ I, F t u n m := Finset.sum_comm
    _ = ∑ n ∈ I, ∑ t ∈ W, ∑ m ∈ I, ∑ u ∈ U, F t u n m := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.sum_comm
    _ = ∑ n ∈ I, ∑ m ∈ I, ∑ t ∈ W, ∑ u ∈ U, F t u n m := by
      apply Finset.sum_congr rfl
      intro n hn
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      unfold heathBrownPhaseCorrelation F
      simp only [star_sum, star_mul, star_star]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      simp only [Complex.star_def]
      ring

/-- Unit-bounded coefficients leave a product of correlation norms. -/
theorem heathBrownMixedDifferenceMoment_le_correlation
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ I, ‖a n‖ ≤ 1) :
    heathBrownMixedDifferenceMoment I W U a ≤
      ∑ n ∈ I, ∑ m ∈ I,
        ‖heathBrownPhaseCorrelation W n m‖ * ‖heathBrownPhaseCorrelation U n m‖ := by
  have hnonneg : 0 ≤ heathBrownMixedDifferenceMoment I W U a := by
    unfold heathBrownMixedDifferenceMoment
    positivity
  calc
    _ = ‖(heathBrownMixedDifferenceMoment I W U a : ℂ)‖ := by
      rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    _ = ‖∑ n ∈ I, ∑ m ∈ I, star (a n) * a m *
        heathBrownPhaseCorrelation W n m * star (heathBrownPhaseCorrelation U n m)‖ := by
      rw [heathBrownMixedDifferenceMoment_expansion]
    _ ≤ ∑ n ∈ I, ∑ m ∈ I, ‖star (a n) * a m *
        heathBrownPhaseCorrelation W n m * star (heathBrownPhaseCorrelation U n m)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => norm_sum_le _ _)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      simp only [norm_mul, norm_star]
      have hprod : ‖a n‖ * ‖a m‖ ≤ 1 := by
        simpa using mul_le_mul (ha n hn) (ha m hm) (norm_nonneg _) zero_le_one
      nlinarith [mul_nonneg (norm_nonneg (heathBrownPhaseCorrelation W n m))
        (norm_nonneg (heathBrownPhaseCorrelation U n m)),
        mul_le_mul_of_nonneg_right hprod
          (mul_nonneg (norm_nonneg (heathBrownPhaseCorrelation W n m))
            (norm_nonneg (heathBrownPhaseCorrelation U n m)))]

/-- The self-correlation norm sum equals the original self second moment. -/
theorem heathBrownPhaseCorrelation_norm_sq_sum (I : Finset ℕ) (W : Finset ℝ) :
    (∑ nm ∈ I ×ˢ I, ‖heathBrownPhaseCorrelation W nm.1 nm.2‖ ^ 2) =
      heathBrownDifferenceMoment I W (fun _ => 1) := by
  have h := heathBrownDifferenceMoment_ofReal_eq_kernel_sum I W (fun _ => 1)
  simp only [Complex.ofReal_one, one_mul] at h
  rw [h, Finset.sum_product]
  rfl

/-- Finite Cauchy--Schwarz for the actual mixed difference polynomial. -/
theorem heathBrownMixedDifferenceMoment_cauchySchwarz
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ I, ‖a n‖ ≤ 1) :
    heathBrownMixedDifferenceMoment I W U a ≤
      Real.sqrt (heathBrownDifferenceMoment I W (fun _ => 1)) *
        Real.sqrt (heathBrownDifferenceMoment I U (fun _ => 1)) := by
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (I ×ˢ I)
    (fun nm => ‖heathBrownPhaseCorrelation W nm.1 nm.2‖)
    (fun nm => ‖heathBrownPhaseCorrelation U nm.1 nm.2‖)
  rw [heathBrownPhaseCorrelation_norm_sq_sum, heathBrownPhaseCorrelation_norm_sq_sum,
    Finset.sum_product] at hCS
  exact (heathBrownMixedDifferenceMoment_le_correlation I W U a ha).trans hCS

/-- Exact conversion to the negative phase at the ordinate difference. -/
theorem heathBrownDifferencePolynomial_eq_dirichletPhase
    (I : Finset ℕ) (a : ℕ → ℂ) (hI : ∀ n ∈ I, 0 < n) (t u : ℝ) :
    heathBrownDifferencePolynomial I a t u =
      ∑ n ∈ I, a n * dirichletPhase n (t - u) := by
  unfold heathBrownDifferencePolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, heathBrownPhase_mul_star n (hI n hn)]
  congr 1
  unfold heathBrownPhase dirichletPhase
  congr 1
  ring

/-- Mixed Cauchy--Schwarz in the source's closed-support, negative-phase language.
Both ordinate variables occur in the inner polynomial. -/
theorem mixed_doubleZeta_cauchySchwarz
    (I : Finset ℕ) (W U : Finset ℝ) (a : ℕ → ℂ)
    (hI : ∀ n ∈ I, 0 < n) (ha : ∀ n ∈ I, ‖a n‖ ≤ 1) :
    (∑ t ∈ W, ∑ u ∈ U, ‖∑ n ∈ I, a n * dirichletPhase n (t - u)‖ ^ 2) ≤
      Real.sqrt (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ I, dirichletPhase n (t - u)‖ ^ 2) *
        Real.sqrt (∑ t ∈ U, ∑ u ∈ U, ‖∑ n ∈ I, dirichletPhase n (t - u)‖ ^ 2) := by
  have h := heathBrownMixedDifferenceMoment_cauchySchwarz I W U a ha
  simp only [heathBrownMixedDifferenceMoment, heathBrownDifferenceMoment,
    heathBrownDifferencePolynomial_eq_dirichletPhase I a hI,
    heathBrownDifferencePolynomial_eq_dirichletPhase I (fun _ => 1) hI, one_mul] at h
  exact h

/-- A consumer on actual large-value patterns with the same integer support. -/
theorem LargeValuePattern.mixed_doubleZeta_le
    (P Q : LargeValuePattern) (hI : P.indices = Q.indices)
    (a : ℕ → ℂ) (ha : ∀ n ∈ P.indices, ‖a n‖ ≤ 1) :
    (∑ t ∈ P.ordinates, ∑ u ∈ Q.ordinates,
      ‖∑ n ∈ P.indices, a n * dirichletPhase n (t - u)‖ ^ 2) ≤
      Real.sqrt (doubleZetaSum P) * Real.sqrt (doubleZetaSum Q) := by
  have hpos : ∀ n ∈ P.indices, 0 < n := by
    intro n hn
    rw [P.indices_eq_dyadicInterval] at hn
    exact P.scale_pos.trans_le (Finset.mem_Icc.mp hn).1
  have h := mixed_doubleZeta_cauchySchwarz P.indices P.ordinates Q.ordinates a hpos ha
  unfold doubleZetaSum
  simpa only [hI] using h

end TaoTrudgianYang2025
