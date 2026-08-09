import Mathlib.NumberTheory.Harmonic.Bounds
import RiemannZeta.GuthMaynard.ClassicalDensity
import RiemannZeta.GuthMaynard.MeanValueProof

open Complex Finset
open scoped ArithmeticFunction.Moebius BigOperators ComplexConjugate

namespace RiemannZeta.GuthMaynard

/-!
# Classical mollifier moments

This file develops the non-dyadic continuous mean-square estimate needed for
the classical Ingham mollifier.  The frequency set is the complete interval
`1 <= n <= X`, rather than the single dyadic block used by
`integral_norm_sq_dirichletTime_le`.
-/

/-- A Dirichlet polynomial supported on the complete interval `1 <= n <= X`,
written on a vertical line as a function of its ordinate. -/
noncomputable def dirichletTimeUpTo (X : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))

/-- The off-diagonal logarithmic Hilbert form for the full initial interval. -/
noncomputable def logHilbertQuadUpTo (X : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
    if n = m then 0 else
      conj (a n) * a m / (((Real.log m - Real.log n : ℝ) : ℂ))

/-- The integer-kernel main term used to estimate `logHilbertQuadUpTo`. -/
noncomputable def natMainQuadUpTo (X : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
    if n = m then 0 else
      conj (a n) * a m * (n : ℂ) /
        (((m : ℤ) - (n : ℤ) : ℤ) : ℂ)

/-- The uniformly bounded error between the logarithmic and integer kernels. -/
noncomputable def logKernelErrorQuadUpTo (X : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
    if n = m then 0 else conj (a n) * a m *
      (((((Real.log m - Real.log n)⁻¹ : ℝ) : ℂ)) -
        (n : ℂ) / (((m : ℤ) - (n : ℤ) : ℤ) : ℂ))

lemma logHilbertQuadUpTo_eq_main_add_error (X : ℕ) (a : ℕ → ℂ) :
    logHilbertQuadUpTo X a =
      natMainQuadUpTo X a + logKernelErrorQuadUpTo X a := by
  simp only [logHilbertQuadUpTo, natMainQuadUpTo, logKernelErrorQuadUpTo,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnm : n = m
  · simp [hnm]
  · simp only [hnm, if_false]
    rw [div_eq_mul_inv, ← Complex.ofReal_inv]
    ring

lemma logKernelErrorQuadUpTo_norm_le (X : ℕ) (a : ℕ → ℂ) :
    ‖logKernelErrorQuadUpTo X a‖ ≤
      (X : ℝ) * ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by
  let s := Finset.Icc 1 X
  have hterm : ∀ m ∈ s, ∀ n ∈ s,
      ‖if n = m then (0 : ℂ) else conj (a n) * a m *
        (((((Real.log m - Real.log n)⁻¹ : ℝ) : ℂ)) -
          (n : ℂ) / (((m : ℤ) - (n : ℤ) : ℤ) : ℂ))‖ ≤
        ‖a n‖ * ‖a m‖ := by
    intro m hm n hn
    by_cases hnm : n = m
    · simp [hnm, mul_nonneg]
    · simp only [hnm, if_false, norm_mul, norm_conj]
      have hnPos : 0 < n := Finset.mem_Icc.mp hn |>.1
      have hmPos : 0 < m := Finset.mem_Icc.mp hm |>.1
      have hk := norm_complex_log_kernel_error_le_one hnPos hmPos hnm
      exact (mul_le_mul_of_nonneg_left hk
        (mul_nonneg (norm_nonneg (a n)) (norm_nonneg (a m)))).trans_eq (mul_one _)
  calc
    ‖logKernelErrorQuadUpTo X a‖ ≤
        ∑ m ∈ s, ∑ n ∈ s, ‖a n‖ * ‖a m‖ := by
      unfold logKernelErrorQuadUpTo
      exact norm_sum_le_of_le s (fun m hm ↦
        norm_sum_le_of_le s (fun n hn ↦ hterm m hm n hn))
    _ = (∑ n ∈ s, ‖a n‖) ^ 2 := by
      rw [pow_two]
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (s.card : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 :=
      sum_sq_le_card_mul_sum_sq s (fun n ↦ ‖a n‖)
    _ = (X : ℝ) * ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by
      have hcard : s.card = X := by simp [s]
      rw [hcard]

/-- Coefficients scaled by the upper endpoint, for the integer Hilbert form. -/
noncomputable def natScaledCoeffUpTo (X : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) / (X : ℂ) * a n

lemma natMainQuadUpTo_eq_scaled_hilbert (X : ℕ) (a : ℕ → ℂ) (hX : 0 < X) :
    natMainQuadUpTo X a = (X : ℂ) *
      (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
        if n = m then 0 else conj (natScaledCoeffUpTo X a n) * a m /
          (((m : ℤ) - (n : ℤ) : ℤ) : ℂ)) := by
  simp only [natMainQuadUpTo, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnm : n = m
  · simp [hnm]
  · simp only [hnm, if_false, natScaledCoeffUpTo, map_mul, map_div₀, map_natCast]
    have hXC : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
    field_simp

lemma natScaledCoeffUpTo_l2_le (X : ℕ) (a : ℕ → ℂ) (hX : 0 < X) :
    (∑ n ∈ Finset.Icc 1 X, ‖natScaledCoeffUpTo X a n‖ ^ 2) ≤
      ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hnUpper : (n : ℝ) ≤ X := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hratio : (n : ℝ) / (X : ℝ) ≤ 1 := (div_le_one hXR).mpr hnUpper
  have hratioNonneg : 0 ≤ (n : ℝ) / (X : ℝ) := by positivity
  have hnormRatio : ‖(n : ℂ) / (X : ℂ)‖ = (n : ℝ) / (X : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  simp only [natScaledCoeffUpTo, norm_mul, hnormRatio]
  have hrsq : ((n : ℝ) / (X : ℝ)) ^ 2 ≤ 1 := by nlinarith
  calc
    ((n : ℝ) / (X : ℝ) * ‖a n‖) ^ 2 =
        ((n : ℝ) / (X : ℝ)) ^ 2 * ‖a n‖ ^ 2 := by ring
    _ ≤ 1 * ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hrsq (sq_nonneg ‖a n‖)
    _ = ‖a n‖ ^ 2 := one_mul _

lemma natMainQuadUpTo_norm_le (X : ℕ) (a : ℕ → ℂ) (hX : 0 < X) :
    ‖natMainQuadUpTo X a‖ ≤
      (2 * Real.pi) * (X : ℝ) *
        ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by
  let s := Finset.Icc 1 X
  let H : ℂ := ∑ m ∈ s, ∑ n ∈ s,
    if n = m then 0 else conj (natScaledCoeffUpTo X a n) * a m /
      (((m : ℤ) - (n : ℤ) : ℤ) : ℂ)
  have hHilbert : ‖H‖ ≤ Real.pi *
      ((∑ n ∈ s, ‖natScaledCoeffUpTo X a n‖ ^ 2) +
        ∑ n ∈ s, ‖a n‖ ^ 2) := by
    simpa [H] using nat_hilbertForm_norm_le s (natScaledCoeffUpTo X a) a
  have hScaled := natScaledCoeffUpTo_l2_le X a hX
  have hH : ‖H‖ ≤ 2 * Real.pi * ∑ n ∈ s, ‖a n‖ ^ 2 := by
    calc
      ‖H‖ ≤ Real.pi *
          ((∑ n ∈ s, ‖natScaledCoeffUpTo X a n‖ ^ 2) +
            ∑ n ∈ s, ‖a n‖ ^ 2) := hHilbert
      _ ≤ Real.pi * ((∑ n ∈ s, ‖a n‖ ^ 2) +
            ∑ n ∈ s, ‖a n‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
        exact add_le_add (by simpa [s] using hScaled) le_rfl
      _ = 2 * Real.pi * ∑ n ∈ s, ‖a n‖ ^ 2 := by ring
  rw [natMainQuadUpTo_eq_scaled_hilbert X a hX]
  change ‖(X : ℂ) * H‖ ≤ _
  rw [norm_mul, Complex.norm_natCast]
  calc
    (X : ℝ) * ‖H‖ ≤ (X : ℝ) *
        (2 * Real.pi * ∑ n ∈ s, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hH (by positivity)
    _ = (2 * Real.pi) * (X : ℝ) *
        ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by simp [s]; ring

theorem logHilbertQuadUpTo_norm_le (X : ℕ) (a : ℕ → ℂ) (hX : 0 < X) :
    ‖logHilbertQuadUpTo X a‖ ≤
      (2 * Real.pi + 1) * (X : ℝ) *
        ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by
  rw [logHilbertQuadUpTo_eq_main_add_error]
  calc
    ‖natMainQuadUpTo X a + logKernelErrorQuadUpTo X a‖ ≤
        ‖natMainQuadUpTo X a‖ + ‖logKernelErrorQuadUpTo X a‖ := norm_add_le _ _
    _ ≤ (2 * Real.pi) * (X : ℝ) *
          ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 +
        (X : ℝ) * ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 :=
      add_le_add (natMainQuadUpTo_norm_le X a hX) (logKernelErrorQuadUpTo_norm_le X a)
    _ = (2 * Real.pi + 1) * (X : ℝ) *
        ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by ring

lemma integral_conj_dirichletTimeUpTo_mul_dirichletTimeUpTo
    (X : ℕ) (T : ℝ) (a : ℕ → ℂ) :
    (∫ t : ℝ in 0..T,
      conj (dirichletTimeUpTo X a t) * dirichletTimeUpTo X a t) =
      (T : ℂ) * ∑ n ∈ Finset.Icc 1 X, conj (a n) * a n +
        Complex.I *
          (logHilbertQuadUpTo X (endpointTwist T a) - logHilbertQuadUpTo X a) := by
  have hexpand : ∀ t : ℝ,
      conj (dirichletTimeUpTo X a t) * dirichletTimeUpTo X a t =
        ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
            (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ)))) := by
    intro t
    simp only [dirichletTimeUpTo, map_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finset_sum]
  · rw [show
        (∑ m ∈ Finset.Icc 1 X,
          ∫ t : ℝ in 0..T, ∑ n ∈ Finset.Icc 1 X,
            conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
              (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ))))) =
        ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          ∫ t : ℝ in 0..T,
            conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
              (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ)))) by
      apply Finset.sum_congr rfl
      intro m hm
      exact intervalIntegral.integral_finset_sum (fun n hn ↦ by
        apply Continuous.intervalIntegrable
        fun_prop)]
    rw [show
        (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          ∫ t : ℝ in 0..T,
            conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
              (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ))))) =
        ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          if n = m then (T : ℂ) * (conj (a n) * a n) else
            Complex.I *
              (conj (endpointTwist T a n) * endpointTwist T a m - conj (a n) * a m) /
                ((Real.log m - Real.log n : ℝ) : ℂ) by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_conj_dirichlet_term_mul_dirichlet_term T a
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1]
    rw [show
        (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          if n = m then (T : ℂ) * (conj (a n) * a n) else
            Complex.I *
              (conj (endpointTwist T a n) * endpointTwist T a m - conj (a n) * a m) /
                ((Real.log m - Real.log n : ℝ) : ℂ)) =
        ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X, (
          (if n = m then (T : ℂ) * (conj (a n) * a n) else 0) +
          (if n = m then 0 else
            Complex.I * (conj (endpointTwist T a n) * endpointTwist T a m) /
              ((Real.log m - Real.log n : ℝ) : ℂ)) -
          (if n = m then 0 else
            Complex.I * (conj (a n) * a m) /
              ((Real.log m - Real.log n : ℝ) : ℂ))) by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hnm : n = m
      · simp [hnm]
      · simp [hnm]
        ring]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, logHilbertQuadUpTo,
      Finset.mul_sum, mul_sub]
    have hdiag :
        (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X,
          if n = m then (T : ℂ) * (conj (a n) * a n) else 0) =
        ∑ m ∈ Finset.Icc 1 X, (T : ℂ) * (conj (a m) * a m) := by
      apply Finset.sum_congr rfl
      intro m hm
      calc
        (∑ n ∈ Finset.Icc 1 X,
          if n = m then (T : ℂ) * (conj (a n) * a n) else 0) =
            ∑ n ∈ Finset.Icc 1 X,
              if n = m then (T : ℂ) * (conj (a m) * a m) else 0 := by
                apply Finset.sum_congr rfl
                intro n hn
                by_cases hnm : n = m <;> simp [hnm]
        _ = (T : ℂ) * (conj (a m) * a m) := by simp [hm]
    rw [hdiag]
    simp only [mul_ite]
    ring_nf
  · intro m hm
    apply Continuous.intervalIntegrable
    fun_prop

lemma continuous_dirichletTimeUpTo (X : ℕ) (a : ℕ → ℂ) :
    Continuous (dirichletTimeUpTo X a) := by
  change Continuous (fun t : ℝ ↦ ∑ n ∈ Finset.Icc 1 X,
    a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ))))
  fun_prop

lemma ofReal_integral_norm_sq_dirichletTimeUpTo (X : ℕ) (T : ℝ) (a : ℕ → ℂ) :
    (((∫ t : ℝ in 0..T, ‖dirichletTimeUpTo X a t‖ ^ 2) : ℝ) : ℂ) =
      (T : ℂ) * ∑ n ∈ Finset.Icc 1 X, conj (a n) * a n +
        Complex.I *
          (logHilbertQuadUpTo X (endpointTwist T a) - logHilbertQuadUpTo X a) := by
  rw [← intervalIntegral.integral_ofReal]
  · have hpoint : ∀ t : ℝ, ((‖dirichletTimeUpTo X a t‖ ^ 2 : ℝ) : ℂ) =
        conj (dirichletTimeUpTo X a t) * dirichletTimeUpTo X a t := by
      intro t
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp_rw [hpoint]
    exact integral_conj_dirichletTimeUpTo_mul_dirichletTimeUpTo X T a

/-- Continuous Montgomery mean square for an arbitrary initial interval.
The endpoint loss is linear in `X`; unlike a dyadic decomposition, this
version introduces no extra logarithm. -/
theorem integral_norm_sq_dirichletTimeUpTo_le (X : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (hX : 0 < X) (hT : 0 ≤ T) :
    (∫ t : ℝ in 0..T, ‖dirichletTimeUpTo X a t‖ ^ 2) ≤
      (T + 2 * (2 * Real.pi + 1) * (X : ℝ)) *
        ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2 := by
  let S : ℝ := ∑ n ∈ Finset.Icc 1 X, ‖a n‖ ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hdiag :
      ‖(T : ℂ) * ∑ n ∈ Finset.Icc 1 X, conj (a n) * a n‖ = T * S := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
    have hsum : (∑ n ∈ Finset.Icc 1 X, conj (a n) * a n) = (S : ℂ) := by
      dsimp [S]
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      exact map_pow Complex.ofRealHom ‖a n‖ 2
    rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
  have htwist :
      ∑ n ∈ Finset.Icc 1 X, ‖endpointTwist T a n‖ ^ 2 = S := by
    dsimp [S]
    apply Finset.sum_congr rfl
    intro n hn
    rw [norm_endpointTwist]
  have hoff :
      ‖Complex.I *
          (logHilbertQuadUpTo X (endpointTwist T a) - logHilbertQuadUpTo X a)‖ ≤
        2 * (2 * Real.pi + 1) * (X : ℝ) * S := by
    rw [norm_mul, Complex.norm_I, one_mul]
    calc
      ‖logHilbertQuadUpTo X (endpointTwist T a) - logHilbertQuadUpTo X a‖ ≤
          ‖logHilbertQuadUpTo X (endpointTwist T a)‖ +
            ‖logHilbertQuadUpTo X a‖ := norm_sub_le _ _
      _ ≤ (2 * Real.pi + 1) * (X : ℝ) * S +
          (2 * Real.pi + 1) * (X : ℝ) * S := by
        exact add_le_add (by simpa [htwist] using
          logHilbertQuadUpTo_norm_le X (endpointTwist T a) hX)
          (by simpa [S] using logHilbertQuadUpTo_norm_le X a hX)
      _ = 2 * (2 * Real.pi + 1) * (X : ℝ) * S := by ring
  let L : ℝ := ∫ t : ℝ in 0..T, ‖dirichletTimeUpTo X a t‖ ^ 2
  have hcast := ofReal_integral_norm_sq_dirichletTimeUpTo X T a
  change L ≤ (T + 2 * (2 * Real.pi + 1) * (X : ℝ)) * S
  change ((L : ℝ) : ℂ) = _ at hcast
  calc
    L ≤ |L| := le_abs_self L
    _ = ‖(L : ℂ)‖ := (Complex.norm_real L).symm
    _ = ‖(T : ℂ) * ∑ n ∈ Finset.Icc 1 X, conj (a n) * a n +
        Complex.I *
          (logHilbertQuadUpTo X (endpointTwist T a) - logHilbertQuadUpTo X a)‖ := by
      rw [hcast]
    _ ≤ ‖(T : ℂ) * ∑ n ∈ Finset.Icc 1 X, conj (a n) * a n‖ +
        ‖Complex.I *
          (logHilbertQuadUpTo X (endpointTwist T a) - logHilbertQuadUpTo X a)‖ :=
      norm_add_le _ _
    _ ≤ T * S + 2 * (2 * Real.pi + 1) * (X : ℝ) * S := by
      rw [hdiag]
      exact add_le_add le_rfl hoff
    _ = (T + 2 * (2 * Real.pi + 1) * (X : ℝ)) * S := by ring

/-- Coefficients of the critical-line Möbius mollifier. -/
noncomputable def mollifierCriticalCoeff (n : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
    (n : ℂ) ^ (-((1 / 2 : ℝ) : ℂ))

lemma zetaMollifier_criticalLine_eq_dirichletTimeUpTo (X : ℕ) (t : ℝ) :
    zetaMollifier X (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
      dirichletTimeUpTo X mollifierCriticalCoeff t := by
  unfold zetaMollifier dirichletTimeUpTo mollifierCriticalCoeff
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := Finset.mem_Icc.mp hn |>.1
  rw [show -(((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ)) =
      -((1 / 2 : ℝ) : ℂ) + (-(t : ℂ)) * Complex.I by ring]
  rw [Complex.cpow_add _ _ (by exact_mod_cast hnPos.ne'),
    nat_cpow_neg_mul_I_eq n t hnPos]
  ring

lemma norm_mollifierCriticalCoeff_sq_le_inv (n : ℕ) (hn : 0 < n) :
    ‖mollifierCriticalCoeff n‖ ^ 2 ≤ (n : ℝ)⁻¹ := by
  rw [mollifierCriticalCoeff, norm_mul, Complex.norm_natCast_cpow_of_pos hn]
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 :=
    norm_moebius_cast_le_one n
  have hpowNonneg : 0 ≤ (n : ℝ) ^ (-((1 / 2 : ℝ) : ℂ)).re :=
    Real.rpow_nonneg (by positivity) _
  have hmul :
      ‖(ArithmeticFunction.moebius n : ℂ)‖ *
          (n : ℝ) ^ (-((1 / 2 : ℝ) : ℂ)).re ≤
        (n : ℝ) ^ (-((1 / 2 : ℝ) : ℂ)).re :=
    mul_le_of_le_one_left hpowNonneg hmu
  calc
    (‖(ArithmeticFunction.moebius n : ℂ)‖ *
        (n : ℝ) ^ (-((1 / 2 : ℝ) : ℂ)).re) ^ 2 ≤
        ((n : ℝ) ^ (-((1 / 2 : ℝ) : ℂ)).re) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hpowNonneg) hpowNonneg).mpr hmul
    _ = (n : ℝ)⁻¹ := by
      norm_num
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
      exact Real.rpow_neg_one (n : ℝ)

lemma mollifierCriticalCoeff_l2_le_harmonic (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, ‖mollifierCriticalCoeff n‖ ^ 2) ≤
      (harmonic X : ℝ) := by
  rw [harmonic_eq_sum_Icc]
  push_cast
  exact Finset.sum_le_sum fun n hn ↦
    norm_mollifierCriticalCoeff_sq_le_inv n (Finset.mem_Icc.mp hn).1

/-- The critical-line second moment of the actual finite Möbius mollifier.
This is the qualitative form of the mollifier boundary estimate used by
Ingham; the explicit source improves the constants, not the powers of `T`,
`X`, or `log X`. -/
theorem integral_norm_sq_zetaMollifier_criticalLine_le (X : ℕ) (T : ℝ)
    (hX : 0 < X) (hT : 0 ≤ T) :
    (∫ t : ℝ in 0..T,
        ‖zetaMollifier X (((1 / 2 : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ ^ 2) ≤
      (T + 2 * (2 * Real.pi + 1) * (X : ℝ)) * (1 + Real.log X) := by
  simp_rw [zetaMollifier_criticalLine_eq_dirichletTimeUpTo]
  have hMean := integral_norm_sq_dirichletTimeUpTo_le
    X T mollifierCriticalCoeff hX hT
  have hCoeff := mollifierCriticalCoeff_l2_le_harmonic X
  have hHarmonic := harmonic_le_one_add_log X
  have hFactor : 0 ≤ T + 2 * (2 * Real.pi + 1) * (X : ℝ) := by positivity
  exact hMean.trans <| mul_le_mul_of_nonneg_left (hCoeff.trans hHarmonic) hFactor

end RiemannZeta.GuthMaynard
