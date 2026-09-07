import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import RiemannZeta.GuthMaynard.MeanValueCS
import RiemannZeta.GuthMaynard.MeanValue
import RiemannZeta.GuthMaynard.Separated

open Complex Set
open scoped Interval ComplexConjugate

namespace RiemannZeta.GuthMaynard

/-- The `trigPoly` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def trigPoly (s : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ s, a n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))

lemma integral_cexp_int (k : ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))) =
      if k = 0 then (2 * Real.pi : ℝ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · simp only [hk, if_false]
    have hc : Complex.I * (k : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hk)
    rw [integral_exp_mul_complex hc]
    have hcexp :
        Complex.exp (Complex.I * (k : ℂ) * (((2 * Real.pi : ℝ) : ℂ))) = 1 := by
      rw [show Complex.I * (k : ℂ) * (((2 * Real.pi : ℝ) : ℂ)) =
          (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [hcexp]
    simp

lemma integral_conj_fourier_term_mul_fourier_term (a b : ℂ) (n m : ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      conj (a * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
        (b * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)))) =
      if n = m then (2 * Real.pi : ℝ) * (conj a * b) else 0 := by
  have hfun : ∀ x : ℝ,
      conj (a * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
          (b * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))) =
        (conj a * b) * Complex.exp (Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ)) := by
    intro x
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, conj_I, map_intCast, conj_ofReal, neg_mul]
    rw [show (conj a * Complex.exp (- (Complex.I * (n : ℂ) * (x : ℂ)))) *
          (b * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))) =
        (conj a * b) * (Complex.exp (- (Complex.I * (n : ℂ) * (x : ℂ))) *
          Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))) by ring]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  simp_rw [hfun]
  calc
    (∫ x : ℝ in 0..2 * Real.pi,
        (conj a * b) * Complex.exp (Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ))) =
        (conj a * b) * (∫ x : ℝ in 0..2 * Real.pi,
          Complex.exp (Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ))) := by
      exact intervalIntegral.integral_const_mul (conj a * b)
        (fun x : ℝ => Complex.exp (Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ)))
    _ = _ := by
      rw [integral_cexp_int (m - n)]
      by_cases hnm : n = m
      · subst m
        simp
        ring
      · have hsub : m - n ≠ 0 := sub_ne_zero.mpr (Ne.symm hnm)
        simp [hnm, hsub]

lemma integral_conj_trigPoly_mul_trigPoly (s : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ x : ℝ in 0..2 * Real.pi, conj (trigPoly s a x) * trigPoly s b x) =
      (2 * Real.pi : ℝ) * ∑ n ∈ s, conj (a n) * b n := by
  have hexpand : ∀ x : ℝ,
      conj (trigPoly s a x) * trigPoly s b x =
        ∑ m ∈ s, ∑ n ∈ s,
          conj (a n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
            (b m * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))) := by
    intro x
    simp only [trigPoly, map_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · calc
      (∑ m ∈ s, ∫ x : ℝ in 0..2 * Real.pi, ∑ n ∈ s,
          conj (a n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
            (b m * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)))) =
          ∑ m ∈ s, ∑ n ∈ s, ∫ x : ℝ in 0..2 * Real.pi,
            conj (a n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
              (b m * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact intervalIntegral.integral_finsetSum (fun n hn => by
          apply Continuous.intervalIntegrable
          fun_prop)
      _ = (2 * Real.pi : ℝ) * ∑ n ∈ s, conj (a n) * b n := by
        simp_rw [integral_conj_fourier_term_mul_fourier_term]
        simp
        simp only [Finset.mul_sum]
  · intro m hm
    apply Continuous.intervalIntegrable
    fun_prop

lemma integral_norm_sq_trigPoly (s : Finset ℤ) (a : ℤ → ℂ) :
    (∫ x : ℝ in 0..2 * Real.pi, ‖trigPoly s a x‖ ^ 2) =
      2 * Real.pi * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hpoint : ∀ x : ℝ, ((‖trigPoly s a x‖ ^ 2 : ℝ) : ℂ) =
      conj (trigPoly s a x) * trigPoly s a x := by
    intro x
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  simp_rw [hpoint]
  rw [integral_conj_trigPoly_mul_trigPoly]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  symm
  rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_conj_mul_self]

lemma continuous_trigPoly (s : Finset ℤ) (a : ℤ → ℂ) :
    Continuous (trigPoly s a) := by
  change Continuous (fun x : ℝ =>
    ∑ n ∈ s, a n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)))
  fun_prop

lemma integral_sawtooth_cexp (k : ℤ) (hk : k ≠ 0) :
    (∫ x : ℝ in 0..2 * Real.pi,
      ((Real.pi - x : ℝ) : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))) =
      2 * Real.pi * Complex.I / (k : ℂ) := by
  let c : ℂ := Complex.I * (k : ℂ)
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr hk)
  let v : ℝ → ℂ := fun x => Complex.exp (c * (x : ℂ)) / c
  have hv : ∀ x : ℝ, HasDerivAt v (Complex.exp (c * (x : ℂ))) x := by
    intro x
    dsimp [v]
    convert ((Complex.hasDerivAt_exp (c * (x : ℂ))).comp x
      (((hasDerivAt_id x).ofReal_comp).const_mul c)).div_const c using 1
    field_simp
    simp
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => ((Real.pi - y : ℝ) : ℂ)) (-1) x := by
    intro x
    convert ((hasDerivAt_const x Real.pi).sub (hasDerivAt_id x)).ofReal_comp using 1
    simp
  have hu' : IntervalIntegrable (fun _ : ℝ => (-1 : ℂ)) MeasureTheory.volume 0
      (2 * Real.pi) := continuous_const.intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun y : ℝ => Complex.exp (c * (y : ℂ)))
      MeasureTheory.volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (u := fun y : ℝ => ((Real.pi - y : ℝ) : ℂ))
    (u' := fun _ => (-1 : ℂ)) (v := v)
    (v' := fun y => Complex.exp (c * (y : ℂ)))
    (fun x _ => hu x) (fun x _ => hv x) hu' hv'
  change (∫ x : ℝ in 0..2 * Real.pi,
      ((Real.pi - x : ℝ) : ℂ) * Complex.exp (c * (x : ℂ))) = _
  rw [show (∫ x : ℝ in 0..2 * Real.pi,
      ((Real.pi - x : ℝ) : ℂ) * Complex.exp (c * (x : ℂ))) = _ by
        simpa only using hparts]
  have hcexp : Complex.exp (c * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    dsimp [c]
    rw [show Complex.I * (k : ℂ) * ((2 * Real.pi : ℝ) : ℂ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  have hv0 : v 0 = 1 / c := by simp [v]
  have hv2 : v (2 * Real.pi) = 1 / c := by
    change Complex.exp (c * (((2 * Real.pi : ℝ) : ℂ))) / c = 1 / c
    rw [hcexp]
  have hvint : (∫ x : ℝ in 0..2 * Real.pi, v x) = 0 := by
    simp only [v, div_eq_mul_inv]
    calc
      (∫ x : ℝ in 0..2 * Real.pi, Complex.exp (c * (x : ℂ)) * c⁻¹) =
          (∫ x : ℝ in 0..2 * Real.pi, Complex.exp (c * (x : ℂ))) * c⁻¹ := by
            exact intervalIntegral.integral_mul_const c⁻¹
              (fun x : ℝ => Complex.exp (c * (x : ℂ)))
      _ = 0 := by rw [integral_exp_mul_complex hc, hcexp]; simp
  have hterm : (∫ x : ℝ in 0..2 * Real.pi, (-1 : ℂ) * v x) = 0 := by
    calc
      (∫ x : ℝ in 0..2 * Real.pi, (-1 : ℂ) * v x) =
          (-1 : ℂ) * (∫ x : ℝ in 0..2 * Real.pi, v x) := by
            exact intervalIntegral.integral_const_mul (-1 : ℂ) v
      _ = 0 := by rw [hvint]; simp
  rw [hv0, hv2]
  calc
    ((Real.pi - 2 * Real.pi : ℝ) : ℂ) * (1 / c) -
          ((Real.pi - 0 : ℝ) : ℂ) * (1 / c) -
          (∫ x : ℝ in 0..2 * Real.pi, (-1 : ℂ) * v x) =
        ((Real.pi - 2 * Real.pi : ℝ) : ℂ) * (1 / c) -
          ((Real.pi - 0 : ℝ) : ℂ) * (1 / c) - 0 := by
            exact congrArg
              (fun z : ℂ => ((Real.pi - 2 * Real.pi : ℝ) : ℂ) * (1 / c) -
                ((Real.pi - 0 : ℝ) : ℂ) * (1 / c) - z) hterm
    _ = 2 * Real.pi * Complex.I / (k : ℂ) := by
      simp only [sub_zero]
      dsimp [c]
      field_simp
      rw [Complex.I_sq]
      push_cast
      ring_nf

lemma integral_sawtooth_cexp_all (k : ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      ((Real.pi - x : ℝ) : ℂ) * Complex.exp (Complex.I * (k : ℂ) * (x : ℂ))) =
      if k = 0 then 0 else 2 * Real.pi * Complex.I / (k : ℂ) := by
  by_cases hk : k = 0
  · subst k
    simp
    simp_rw [← Complex.ofReal_sub]
    rw [intervalIntegral.integral_ofReal]
    norm_cast
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => Real.pi) (g := fun x : ℝ => x)
      (continuous_const.intervalIntegrable 0 (2 * Real.pi))
      (continuous_id.intervalIntegrable 0 (2 * Real.pi))]
    simp
    ring_nf
  · simpa only [hk, if_false] using integral_sawtooth_cexp k hk

/-- The `hilbertForm` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def hilbertForm (s : Finset ℤ) (a b : ℤ → ℂ) : ℂ :=
  ∑ m ∈ s, ∑ n ∈ s,
    if n = m then 0 else conj (a n) * b m / ((m - n : ℤ) : ℂ)

lemma integral_sawtooth_conj_fourier_mul_fourier (a b : ℂ) (n m : ℤ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      ((Real.pi - x : ℝ) : ℂ) *
        (conj (a * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
          (b * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))))) =
      if n = m then 0 else
        2 * Real.pi * Complex.I * (conj a * b / ((m - n : ℤ) : ℂ)) := by
  have hfourier : ∀ x : ℝ,
      conj (a * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
          (b * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))) =
        (conj a * b) * Complex.exp (Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ)) := by
    intro x
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, conj_I, map_intCast, conj_ofReal, neg_mul]
    rw [show (conj a * Complex.exp (- (Complex.I * (n : ℂ) * (x : ℂ)))) *
          (b * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))) =
        (conj a * b) * (Complex.exp (- (Complex.I * (n : ℂ) * (x : ℂ))) *
          Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))) by ring]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  simp_rw [hfourier]
  calc
    (∫ x : ℝ in 0..2 * Real.pi,
      ((Real.pi - x : ℝ) : ℂ) * ((conj a * b) *
        Complex.exp (Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ)))) =
        ∫ x : ℝ in 0..2 * Real.pi, (conj a * b) *
          (((Real.pi - x : ℝ) : ℂ) *
            Complex.exp (Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = (conj a * b) * (∫ x : ℝ in 0..2 * Real.pi,
        ((Real.pi - x : ℝ) : ℂ) *
          Complex.exp (Complex.I * ((m - n : ℤ) : ℂ) * (x : ℂ))) := by
      exact intervalIntegral.integral_const_mul (conj a * b) _
    _ = if n = m then 0 else
        2 * Real.pi * Complex.I * (conj a * b / ((m - n : ℤ) : ℂ)) := by
      rw [integral_sawtooth_cexp_all]
      by_cases hnm : n = m
      · simp [hnm]
      · have hsub : m - n ≠ 0 := sub_ne_zero.mpr (Ne.symm hnm)
        simp only [hnm, if_false, hsub]
        ring

lemma integral_sawtooth_conj_trigPoly_mul_trigPoly
    (s : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ x : ℝ in 0..2 * Real.pi,
      ((Real.pi - x : ℝ) : ℂ) * (conj (trigPoly s a x) * trigPoly s b x)) =
      2 * Real.pi * Complex.I * hilbertForm s a b := by
  have hexpand : ∀ x : ℝ,
      ((Real.pi - x : ℝ) : ℂ) * (conj (trigPoly s a x) * trigPoly s b x) =
        ∑ m ∈ s, ∑ n ∈ s,
          ((Real.pi - x : ℝ) : ℂ) *
            (conj (a n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
              (b m * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)))) := by
    intro x
    simp only [trigPoly, map_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · calc
      (∑ m ∈ s, ∫ x : ℝ in 0..2 * Real.pi, ∑ n ∈ s,
          ((Real.pi - x : ℝ) : ℂ) *
            (conj (a n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
              (b m * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ))))) =
          ∑ m ∈ s, ∑ n ∈ s, ∫ x : ℝ in 0..2 * Real.pi,
            ((Real.pi - x : ℝ) : ℂ) *
              (conj (a n * Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) *
                (b m * Complex.exp (Complex.I * (m : ℂ) * (x : ℂ)))) := by
        apply Finset.sum_congr rfl
        intro m hm
        exact intervalIntegral.integral_finsetSum (fun n hn => by
          apply Continuous.intervalIntegrable
          fun_prop)
      _ = 2 * Real.pi * Complex.I * hilbertForm s a b := by
        simp_rw [integral_sawtooth_conj_fourier_mul_fourier]
        simp only [hilbertForm]
        simp only [Finset.mul_sum, mul_ite, mul_zero]
  · intro m hm
    apply Continuous.intervalIntegrable
    fun_prop

lemma norm_sawtooth_conj_trigPoly_mul_trigPoly_le
    (s : Finset ℤ) (a b : ℤ → ℂ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    ‖((Real.pi - x : ℝ) : ℂ) * (conj (trigPoly s a x) * trigPoly s b x)‖ ≤
      Real.pi * (‖trigPoly s a x‖ ^ 2 + ‖trigPoly s b x‖ ^ 2) := by
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hw : |Real.pi - x| ≤ Real.pi := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  have huv : ‖trigPoly s a x‖ * ‖trigPoly s b x‖ ≤
      ‖trigPoly s a x‖ ^ 2 + ‖trigPoly s b x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖trigPoly s a x‖ - ‖trigPoly s b x‖)]
  calc
    ‖((Real.pi - x : ℝ) : ℂ) * (conj (trigPoly s a x) * trigPoly s b x)‖ =
        |Real.pi - x| * (‖trigPoly s a x‖ * ‖trigPoly s b x‖) := by
      simp only [norm_mul, norm_conj, norm_real, Real.norm_eq_abs]
    _ ≤ Real.pi * (‖trigPoly s a x‖ * ‖trigPoly s b x‖) :=
      mul_le_mul_of_nonneg_right hw (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ Real.pi * (‖trigPoly s a x‖ ^ 2 + ‖trigPoly s b x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left huv hpi

theorem hilbertForm_norm_le (s : Finset ℤ) (a b : ℤ → ℂ) :
    ‖hilbertForm s a b‖ ≤
      Real.pi * ((∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖b n‖ ^ 2) := by
  let F : ℝ → ℂ := fun x =>
    ((Real.pi - x : ℝ) : ℂ) * (conj (trigPoly s a x) * trigPoly s b x)
  let G : ℝ → ℝ := fun x =>
    Real.pi * (‖trigPoly s a x‖ ^ 2 + ‖trigPoly s b x‖ ^ 2)
  have htwoPi : 0 ≤ 2 * Real.pi := by positivity
  have htwoPiPos : 0 < 2 * Real.pi := by positivity
  have hFcont : Continuous F := by
    dsimp [F]
    have haCont := continuous_trigPoly s a
    have hbCont := continuous_trigPoly s b
    fun_prop (disch := aesop)
  have hGcont : Continuous G := by
    dsimp [G]
    have haCont := continuous_trigPoly s a
    have hbCont := continuous_trigPoly s b
    fun_prop (disch := aesop)
  have hNormIntegral : ‖∫ x : ℝ in 0..2 * Real.pi, F x‖ ≤
      ∫ x : ℝ in 0..2 * Real.pi, ‖F x‖ :=
    intervalIntegral.norm_integral_le_integral_norm htwoPi
  have hPointwiseIntegral : (∫ x : ℝ in 0..2 * Real.pi, ‖F x‖) ≤
      ∫ x : ℝ in 0..2 * Real.pi, G x := by
    apply intervalIntegral.integral_mono_on htwoPi
      (hFcont.norm.intervalIntegrable 0 (2 * Real.pi))
      (hGcont.intervalIntegrable 0 (2 * Real.pi))
    intro x hx
    exact norm_sawtooth_conj_trigPoly_mul_trigPoly_le s a b hx
  have hGIntegral : (∫ x : ℝ in 0..2 * Real.pi, G x) =
      2 * Real.pi * Real.pi *
        ((∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖b n‖ ^ 2) := by
    dsimp [G]
    have haInt : IntervalIntegrable (fun x : ℝ => ‖trigPoly s a x‖ ^ 2)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      ((continuous_trigPoly s a).norm.pow 2).intervalIntegrable 0 (2 * Real.pi)
    have hbInt : IntervalIntegrable (fun x : ℝ => ‖trigPoly s b x‖ ^ 2)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      ((continuous_trigPoly s b).norm.pow 2).intervalIntegrable 0 (2 * Real.pi)
    rw [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add haInt hbInt]
    rw [integral_norm_sq_trigPoly, integral_norm_sq_trigPoly]
    ring
  have hRepresentation := congrArg norm
    (integral_sawtooth_conj_trigPoly_mul_trigPoly s a b)
  have hScaled : 2 * Real.pi * ‖hilbertForm s a b‖ ≤
      2 * Real.pi * Real.pi *
        ((∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖b n‖ ^ 2) := by
    calc
      2 * Real.pi * ‖hilbertForm s a b‖ = ‖∫ x : ℝ in 0..2 * Real.pi, F x‖ := by
        rw [hRepresentation]
        simp only [norm_mul, norm_real, Real.norm_eq_abs, norm_I]
        have hnormTwo : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [hnormTwo]
        rw [abs_of_pos Real.pi_pos]
        ring
      _ ≤ ∫ x : ℝ in 0..2 * Real.pi, ‖F x‖ := hNormIntegral
      _ ≤ ∫ x : ℝ in 0..2 * Real.pi, G x := hPointwiseIntegral
      _ = _ := hGIntegral
  nlinarith

theorem nat_hilbertForm_norm_le (s : Finset ℕ) (a b : ℕ → ℂ) :
    ‖∑ m ∈ s, ∑ n ∈ s, if n = m then 0 else
        conj (a n) * b m / (((m : ℤ) - (n : ℤ) : ℤ) : ℂ)‖ ≤
      Real.pi * ((∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖b n‖ ^ 2) := by
  let sz : Finset ℤ := s.image (fun n : ℕ => (n : ℤ))
  let az : ℤ → ℂ := fun z => if 0 ≤ z then a z.toNat else 0
  let bz : ℤ → ℂ := fun z => if 0 ≤ z then b z.toNat else 0
  have h := hilbertForm_norm_le sz az bz
  simpa [hilbertForm, sz, az, bz] using h

lemma abs_inv_log_sub_sub_div_le_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x ≠ y) :
    |(Real.log y - Real.log x)⁻¹ - x / (y - x)| ≤ 1 := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · let d := y - x
    have hd : 0 < d := sub_pos.mpr hlt
    have hr : 0 < y / x := div_pos hy hx
    have hlog : Real.log y - Real.log x = Real.log (y / x) := by
      rw [Real.log_div hy.ne' hx.ne']
    have hLpos : 0 < Real.log (y / x) := Real.log_pos ((one_lt_div hx).2 hlt)
    have hLower : d / y ≤ Real.log (y / x) := by
      have := Real.one_sub_inv_le_log_of_pos hr
      dsimp [d]
      convert this using 1
      all_goals field_simp
    have hUpper : Real.log (y / x) ≤ d / x := by
      have := Real.log_le_sub_one_of_pos hr
      dsimp [d]
      convert this using 1
      all_goals field_simp
    have hInvLower : x / d ≤ (Real.log (y / x))⁻¹ := by
      calc
        x / d = (d / x)⁻¹ := by rw [inv_div]
        _ ≤ (Real.log (y / x))⁻¹ := inv_anti₀ hLpos hUpper
    have hInvUpper : (Real.log (y / x))⁻¹ ≤ y / d := by
      calc
        (Real.log (y / x))⁻¹ ≤ (d / y)⁻¹ :=
          inv_anti₀ (div_pos hd hy) hLower
        _ = y / d := by rw [inv_div]
    rw [hlog]
    rw [abs_le]
    constructor
    · linarith
    · have hyd : y / d = x / d + 1 := by
        have hone : (1 : ℝ) = d / d := (div_self hd.ne').symm
        rw [hone, ← add_div]
        dsimp [d]
        ring
      linarith
  · let d := x - y
    have hd : 0 < d := sub_pos.mpr hgt
    have hr : 0 < x / y := div_pos hx hy
    have hlog : Real.log y - Real.log x = -Real.log (x / y) := by
      rw [Real.log_div hx.ne' hy.ne']
      ring
    have hLpos : 0 < Real.log (x / y) := Real.log_pos ((one_lt_div hy).2 hgt)
    have hLower : d / x ≤ Real.log (x / y) := by
      have := Real.one_sub_inv_le_log_of_pos hr
      dsimp [d]
      convert this using 1
      all_goals field_simp
    have hUpper : Real.log (x / y) ≤ d / y := by
      have := Real.log_le_sub_one_of_pos hr
      dsimp [d]
      convert this using 1
      all_goals field_simp
    have hInvLower : y / d ≤ (Real.log (x / y))⁻¹ := by
      calc
        y / d = (d / y)⁻¹ := by rw [inv_div]
        _ ≤ (Real.log (x / y))⁻¹ := inv_anti₀ hLpos hUpper
    have hInvUpper : (Real.log (x / y))⁻¹ ≤ x / d := by
      calc
        (Real.log (x / y))⁻¹ ≤ (d / x)⁻¹ :=
          inv_anti₀ (div_pos hd hx) hLower
        _ = x / d := by rw [inv_div]
    rw [hlog]
    have hnegInv : (-Real.log (x / y))⁻¹ = -(Real.log (x / y))⁻¹ := by
      rw [inv_neg]
    rw [hnegInv]
    have hyx : y - x = -d := by dsimp [d]; ring
    rw [hyx, div_neg]
    rw [abs_le]
    have hxd : x / d = y / d + 1 := by
      have hone : (1 : ℝ) = d / d := (div_self hd.ne').symm
      rw [hone, ← add_div]
      dsimp [d]
      ring
    constructor
    · linarith
    · linarith

lemma norm_complex_log_kernel_error_le_one {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hnm : n ≠ m) :
    ‖(((Real.log m - Real.log n)⁻¹ : ℝ) : ℂ) -
        (n : ℂ) / (((m : ℤ) - (n : ℤ) : ℤ) : ℂ)‖ ≤ 1 := by
  have hreal := abs_inv_log_sub_sub_div_le_one
    (show (0 : ℝ) < n by exact_mod_cast hn)
    (show (0 : ℝ) < m by exact_mod_cast hm)
    (by exact_mod_cast hnm)
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_intCast]
  rw [← Complex.ofReal_div, ← Complex.ofReal_sub]
  rw [Complex.norm_real, Real.norm_eq_abs]
  norm_cast at hreal ⊢

/-- The `logHilbertQuad` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def logHilbertQuad (N : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
    if n = m then 0 else
      conj (a n) * a m / (((Real.log m - Real.log n : ℝ) : ℂ))

/-- The `natMainQuad` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def natMainQuad (N : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
    if n = m then 0 else
      conj (a n) * a m * (n : ℂ) /
        (((m : ℤ) - (n : ℤ) : ℤ) : ℂ)

/-- The `logKernelErrorQuad` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def logKernelErrorQuad (N : ℕ) (a : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
    if n = m then 0 else conj (a n) * a m *
      (((((Real.log m - Real.log n)⁻¹ : ℝ) : ℂ)) -
        (n : ℂ) / (((m : ℤ) - (n : ℤ) : ℤ) : ℂ))

lemma logHilbertQuad_eq_main_add_error (N : ℕ) (a : ℕ → ℂ) :
    logHilbertQuad N a = natMainQuad N a + logKernelErrorQuad N a := by
  simp only [logHilbertQuad, natMainQuad, logKernelErrorQuad, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnm : n = m
  · simp [hnm]
  · simp only [hnm, if_false]
    rw [div_eq_mul_inv]
    rw [← Complex.ofReal_inv]
    ring

lemma logKernelErrorQuad_norm_le (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    ‖logKernelErrorQuad N a‖ ≤
      (N : ℝ) * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  let s := Finset.Ioc N (2 * N)
  have hterm : ∀ m ∈ s, ∀ n ∈ s,
      ‖if n = m then (0 : ℂ) else conj (a n) * a m *
        (((((Real.log m - Real.log n)⁻¹ : ℝ) : ℂ)) -
          (n : ℂ) / (((m : ℤ) - (n : ℤ) : ℤ) : ℂ))‖ ≤
        ‖a n‖ * ‖a m‖ := by
    intro m hm n hn
    by_cases hnm : n = m
    · simp [hnm, mul_nonneg]
    · simp only [hnm, if_false, norm_mul, norm_conj]
      have hnPos : 0 < n := lt_trans hN (Finset.mem_Ioc.mp hn).1
      have hmPos : 0 < m := lt_trans hN (Finset.mem_Ioc.mp hm).1
      have hk := norm_complex_log_kernel_error_le_one hnPos hmPos hnm
      exact (mul_le_mul_of_nonneg_left hk
        (mul_nonneg (norm_nonneg (a n)) (norm_nonneg (a m)))).trans_eq (mul_one _)
  calc
    ‖logKernelErrorQuad N a‖ ≤
        ∑ m ∈ s, ∑ n ∈ s, ‖a n‖ * ‖a m‖ := by
      unfold logKernelErrorQuad
      exact norm_sum_le_of_le s (fun m hm =>
        norm_sum_le_of_le s (fun n hn => hterm m hm n hn))
    _ = (∑ n ∈ s, ‖a n‖) ^ 2 := by
      rw [pow_two]
      simp only [Finset.mul_sum, Finset.sum_mul]
    _ ≤ (s.card : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 :=
      RiemannZeta.GuthMaynard.sum_sq_le_card_mul_sum_sq s (fun n => ‖a n‖)
    _ = (N : ℝ) * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
      have hcard : s.card = N := by
        dsimp [s]
        simp
        omega
      rw [hcard]

/-- The `natScaledCoeff` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def natScaledCoeff (N : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n : ℂ) / (N : ℂ) * a n

lemma natMainQuad_eq_scaled_hilbert (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    natMainQuad N a = (N : ℂ) *
      (∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
        if n = m then 0 else conj (natScaledCoeff N a n) * a m /
          (((m : ℤ) - (n : ℤ) : ℤ) : ℂ)) := by
  simp only [natMainQuad, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnm : n = m
  · simp [hnm]
  · simp only [hnm, if_false, natScaledCoeff, map_mul, map_div₀, map_natCast]
    have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp

lemma natScaledCoeff_l2_le (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N (2 * N), ‖natScaledCoeff N a n‖ ^ 2) ≤
      4 * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnUpper : (n : ℝ) ≤ 2 * N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hratio : (n : ℝ) / (N : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hNR]
    nlinarith
  have hratioNonneg : 0 ≤ (n : ℝ) / (N : ℝ) := by positivity
  have hnormRatio : ‖(n : ℂ) / (N : ℂ)‖ = (n : ℝ) / (N : ℝ) := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  simp only [natScaledCoeff, norm_mul, hnormRatio]
  have hrsq : ((n : ℝ) / (N : ℝ)) ^ 2 ≤ 4 := by nlinarith
  calc
    ((n : ℝ) / (N : ℝ) * ‖a n‖) ^ 2 =
        ((n : ℝ) / (N : ℝ)) ^ 2 * ‖a n‖ ^ 2 := by ring
    _ ≤ 4 * ‖a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hrsq (sq_nonneg ‖a n‖)

lemma natMainQuad_norm_le (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    ‖natMainQuad N a‖ ≤
      (5 * Real.pi) * (N : ℝ) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  let s := Finset.Ioc N (2 * N)
  let H : ℂ := ∑ m ∈ s, ∑ n ∈ s,
    if n = m then 0 else conj (natScaledCoeff N a n) * a m /
      (((m : ℤ) - (n : ℤ) : ℤ) : ℂ)
  have hHilbert : ‖H‖ ≤ Real.pi *
      ((∑ n ∈ s, ‖natScaledCoeff N a n‖ ^ 2) + ∑ n ∈ s, ‖a n‖ ^ 2) := by
    exact nat_hilbertForm_norm_le s (natScaledCoeff N a) a
  have hScaled := natScaledCoeff_l2_le N a hN
  have hH : ‖H‖ ≤ 5 * Real.pi * ∑ n ∈ s, ‖a n‖ ^ 2 := by
    have hpi := Real.pi_pos.le
    calc
      ‖H‖ ≤ Real.pi *
          ((∑ n ∈ s, ‖natScaledCoeff N a n‖ ^ 2) + ∑ n ∈ s, ‖a n‖ ^ 2) := hHilbert
      _ ≤ Real.pi * (4 * (∑ n ∈ s, ‖a n‖ ^ 2) + ∑ n ∈ s, ‖a n‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hpi
        exact add_le_add (by simpa [s] using hScaled) le_rfl
      _ = 5 * Real.pi * ∑ n ∈ s, ‖a n‖ ^ 2 := by ring
  rw [natMainQuad_eq_scaled_hilbert N a hN]
  change ‖(N : ℂ) * H‖ ≤ _
  rw [norm_mul, Complex.norm_natCast]
  have hNnonneg : (0 : ℝ) ≤ N := by positivity
  calc
    (N : ℝ) * ‖H‖ ≤ (N : ℝ) *
        (5 * Real.pi * ∑ n ∈ s, ‖a n‖ ^ 2) := mul_le_mul_of_nonneg_left hH hNnonneg
    _ = (5 * Real.pi) * (N : ℝ) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by simp [s]; ring

theorem logHilbertQuad_norm_le (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    ‖logHilbertQuad N a‖ ≤
      (5 * Real.pi + 1) * (N : ℝ) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  rw [logHilbertQuad_eq_main_add_error]
  calc
    ‖natMainQuad N a + logKernelErrorQuad N a‖ ≤
        ‖natMainQuad N a‖ + ‖logKernelErrorQuad N a‖ := norm_add_le _ _
    _ ≤ (5 * Real.pi) * (N : ℝ) *
          ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 +
        (N : ℝ) * ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 :=
      add_le_add (natMainQuad_norm_le N a hN) (logKernelErrorQuad_norm_le N a hN)
    _ = (5 * Real.pi + 1) * (N : ℝ) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by ring

/-- The `dirichletTime` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def dirichletTime (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))

/-- The `endpointTwist` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def endpointTwist (T : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * Complex.exp (-(Complex.I * (T : ℂ) * (Real.log n : ℂ)))

lemma norm_endpointTwist (T : ℝ) (a : ℕ → ℂ) (n : ℕ) :
    ‖endpointTwist T a n‖ = ‖a n‖ := by
  rw [endpointTwist, norm_mul, Complex.norm_exp]
  have hre : (-(Complex.I * (T : ℂ) * (Real.log n : ℂ))).re = 0 := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, Real.exp_zero, mul_one]

lemma integral_conj_dirichlet_term_mul_dirichlet_term
    (T : ℝ) (a : ℕ → ℂ) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (∫ t : ℝ in 0..T,
      conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
        (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ))))) =
      if n = m then (T : ℂ) * (conj (a n) * a n) else
        Complex.I *
          (conj (endpointTwist T a n) * endpointTwist T a m - conj (a n) * a m) /
            ((Real.log m - Real.log n : ℝ) : ℂ) := by
  by_cases hnm : n = m
  · subst m
    simp only [if_pos]
    have hpoint : ∀ t : ℝ,
        conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
          (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) =
        conj (a n) * a n := by
      intro t
      rw [map_mul, ← Complex.exp_conj]
      simp only [map_neg, map_mul, conj_I, conj_ofReal]
      rw [show -(-Complex.I * (t : ℂ) * (Real.log n : ℂ)) =
          Complex.I * (t : ℂ) * (Real.log n : ℂ) by ring]
      rw [show conj (a n) * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) *
          (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) =
        (conj (a n) * a n) *
          (Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) *
            Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) by ring]
      rw [show Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) *
          Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ))) = 1 by
        rw [← Complex.exp_add]; simp]
      simp
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const]
    rw [sub_zero]
    exact Complex.real_smul
  · simp only [if_neg hnm]
    have hlogne : Real.log n - Real.log m ≠ 0 := by
      rw [sub_ne_zero]
      exact ne_of_apply_ne Real.exp (by
        simpa [Real.exp_log (show (0 : ℝ) < n by exact_mod_cast hn),
          Real.exp_log (show (0 : ℝ) < m by exact_mod_cast hm)] using hnm)
    let c : ℂ := Complex.I * ((Real.log n - Real.log m : ℝ) : ℂ)
    have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hlogne)
    have hpoint : ∀ t : ℝ,
        conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
          (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ)))) =
        (conj (a n) * a m) * Complex.exp (c * (t : ℂ)) := by
      intro t
      rw [map_mul, ← Complex.exp_conj]
      simp only [map_neg, map_mul, conj_I, conj_ofReal]
      rw [show -(-Complex.I * (t : ℂ) * (Real.log n : ℂ)) =
          Complex.I * (t : ℂ) * (Real.log n : ℂ) by ring]
      rw [show conj (a n) * Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) *
          (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ)))) =
        (conj (a n) * a m) *
          (Complex.exp (Complex.I * (t : ℂ) * (Real.log n : ℂ)) *
            Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ)))) by ring]
      rw [← Complex.exp_add]
      congr 1
      dsimp [c]
      push_cast
      ring_nf
    simp_rw [hpoint]
    rw [show (∫ t : ℝ in 0..T, (conj (a n) * a m) * Complex.exp (c * (t : ℂ))) =
        (conj (a n) * a m) * (∫ t : ℝ in 0..T, Complex.exp (c * (t : ℂ))) by
      exact intervalIntegral.integral_const_mul (conj (a n) * a m) _]
    rw [integral_exp_mul_complex hc]
    unfold endpointTwist
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_neg, map_mul, conj_I, conj_ofReal]
    rw [show -(-Complex.I * (T : ℂ) * (Real.log n : ℂ)) =
        Complex.I * (T : ℂ) * (Real.log n : ℂ) by ring]
    rw [show conj (a n) * Complex.exp (Complex.I * (T : ℂ) * (Real.log n : ℂ)) *
        (a m * Complex.exp (-(Complex.I * (T : ℂ) * (Real.log m : ℂ)))) =
      (conj (a n) * a m) *
        (Complex.exp (Complex.I * (T : ℂ) * (Real.log n : ℂ)) *
          Complex.exp (-(Complex.I * (T : ℂ) * (Real.log m : ℂ)))) by ring]
    rw [show Complex.exp (Complex.I * (T : ℂ) * (Real.log n : ℂ)) *
        Complex.exp (-(Complex.I * (T : ℂ) * (Real.log m : ℂ))) =
      Complex.exp (c * (T : ℂ)) by
      rw [← Complex.exp_add]; congr 1; dsimp [c]; push_cast; ring]
    dsimp [c]
    simp only [mul_zero, Complex.exp_zero]
    have hdiff : (((Real.log m - Real.log n : ℝ) : ℂ)) =
        -(((Real.log n - Real.log m : ℝ) : ℂ)) := by
      push_cast
      ring
    rw [hdiff, div_neg]
    have hdC : (((Real.log n - Real.log m : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast hlogne
    field_simp [hdC, Complex.I_ne_zero]
    rw [Complex.I_sq]
    ring

lemma integral_conj_dirichletTime_mul_dirichletTime
    (N : ℕ) (T : ℝ) (a : ℕ → ℂ) :
    (∫ t : ℝ in 0..T, conj (dirichletTime N a t) * dirichletTime N a t) =
      (T : ℂ) * ∑ n ∈ Finset.Ioc N (2 * N), conj (a n) * a n +
        Complex.I * (logHilbertQuad N (endpointTwist T a) - logHilbertQuad N a) := by
  have hexpand : ∀ t : ℝ,
      conj (dirichletTime N a t) * dirichletTime N a t =
        ∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
          conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
            (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ)))) := by
    intro t
    simp only [dirichletTime, map_sum, Finset.sum_mul, Finset.mul_sum]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finsetSum]
  · rw [show
        (∑ m ∈ Finset.Ioc N (2 * N),
          ∫ t : ℝ in 0..T, ∑ n ∈ Finset.Ioc N (2 * N),
            conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
              (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ))))) =
        ∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
          ∫ t : ℝ in 0..T,
            conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
              (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ)))) by
      apply Finset.sum_congr rfl
      intro m hm
      exact intervalIntegral.integral_finsetSum (fun n hn => by
        apply Continuous.intervalIntegrable
        fun_prop)]
    rw [show
        (∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
          ∫ t : ℝ in 0..T,
            conj (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) *
              (a m * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log m : ℂ))))) =
        ∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
          if n = m then (T : ℂ) * (conj (a n) * a n) else
            Complex.I *
              (conj (endpointTwist T a n) * endpointTwist T a m - conj (a n) * a m) /
                ((Real.log m - Real.log n : ℝ) : ℂ) by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_conj_dirichlet_term_mul_dirichlet_term T a
        (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)
        (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hm).1)]
    rw [show
        (∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
          if n = m then (T : ℂ) * (conj (a n) * a n) else
            Complex.I *
              (conj (endpointTwist T a n) * endpointTwist T a m - conj (a n) * a m) /
                ((Real.log m - Real.log n : ℝ) : ℂ)) =
        ∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N), (
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
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, logHilbertQuad,
      Finset.mul_sum, mul_sub]
    have hdiag :
        (∑ m ∈ Finset.Ioc N (2 * N), ∑ n ∈ Finset.Ioc N (2 * N),
          if n = m then (T : ℂ) * (conj (a n) * a n) else 0) =
        ∑ m ∈ Finset.Ioc N (2 * N), (T : ℂ) * (conj (a m) * a m) := by
      apply Finset.sum_congr rfl
      intro m hm
      calc
        (∑ n ∈ Finset.Ioc N (2 * N),
          if n = m then (T : ℂ) * (conj (a n) * a n) else 0) =
            ∑ n ∈ Finset.Ioc N (2 * N),
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

lemma continuous_dirichletTime (N : ℕ) (a : ℕ → ℂ) :
    Continuous (dirichletTime N a) := by
  change Continuous (fun t : ℝ => ∑ n ∈ Finset.Ioc N (2 * N),
    a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ))))
  fun_prop

lemma ofReal_integral_norm_sq_dirichletTime (N : ℕ) (T : ℝ) (a : ℕ → ℂ) :
    (((∫ t : ℝ in 0..T, ‖dirichletTime N a t‖ ^ 2) : ℝ) : ℂ) =
      (T : ℂ) * ∑ n ∈ Finset.Ioc N (2 * N), conj (a n) * a n +
        Complex.I * (logHilbertQuad N (endpointTwist T a) - logHilbertQuad N a) := by
  rw [← intervalIntegral.integral_ofReal]
  · have hpoint : ∀ t : ℝ, ((‖dirichletTime N a t‖ ^ 2 : ℝ) : ℂ) =
        conj (dirichletTime N a t) * dirichletTime N a t := by
      intro t
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    simp_rw [hpoint]
    exact integral_conj_dirichletTime_mul_dirichletTime N T a

theorem integral_norm_sq_dirichletTime_le (N : ℕ) (T : ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hT : 0 ≤ T) :
    (∫ t : ℝ in 0..T, ‖dirichletTime N a t‖ ^ 2) ≤
      (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  let S : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hdiag :
      ‖(T : ℂ) * ∑ n ∈ Finset.Ioc N (2 * N), conj (a n) * a n‖ = T * S := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
    have hsum : (∑ n ∈ Finset.Ioc N (2 * N), conj (a n) * a n) = (S : ℂ) := by
      dsimp [S]
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      exact map_pow Complex.ofRealHom ‖a n‖ 2
    rw [hsum, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS]
  have htwist :
      ∑ n ∈ Finset.Ioc N (2 * N), ‖endpointTwist T a n‖ ^ 2 = S := by
    dsimp [S]
    apply Finset.sum_congr rfl
    intro n hn
    rw [norm_endpointTwist]
  have hoff :
      ‖Complex.I * (logHilbertQuad N (endpointTwist T a) - logHilbertQuad N a)‖ ≤
        2 * (5 * Real.pi + 1) * (N : ℝ) * S := by
    rw [norm_mul, Complex.norm_I, one_mul]
    calc
      ‖logHilbertQuad N (endpointTwist T a) - logHilbertQuad N a‖ ≤
          ‖logHilbertQuad N (endpointTwist T a)‖ + ‖logHilbertQuad N a‖ :=
        norm_sub_le _ _
      _ ≤ (5 * Real.pi + 1) * (N : ℝ) * S +
          (5 * Real.pi + 1) * (N : ℝ) * S := by
        exact add_le_add (by simpa [htwist] using
          logHilbertQuad_norm_le N (endpointTwist T a) hN)
          (by simpa [S] using logHilbertQuad_norm_le N a hN)
      _ = 2 * (5 * Real.pi + 1) * (N : ℝ) * S := by ring
  let L : ℝ := ∫ t : ℝ in 0..T, ‖dirichletTime N a t‖ ^ 2
  have hcast := ofReal_integral_norm_sq_dirichletTime N T a
  change L ≤ (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) * S
  change ((L : ℝ) : ℂ) = _ at hcast
  calc
    L ≤ |L| := le_abs_self L
    _ = ‖(L : ℂ)‖ := (Complex.norm_real L).symm
    _ = ‖(T : ℂ) * ∑ n ∈ Finset.Ioc N (2 * N), conj (a n) * a n +
        Complex.I * (logHilbertQuad N (endpointTwist T a) - logHilbertQuad N a)‖ := by
          rw [hcast]
    _ ≤ ‖(T : ℂ) * ∑ n ∈ Finset.Ioc N (2 * N), conj (a n) * a n‖ +
        ‖Complex.I * (logHilbertQuad N (endpointTwist T a) - logHilbertQuad N a)‖ :=
      norm_add_le _ _
    _ ≤ T * S + 2 * (5 * Real.pi + 1) * (N : ℝ) * S := add_le_add (le_of_eq hdiag) hoff
    _ = (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) * S := by ring

lemma local_sample_le_energy (g : ℝ → ℂ) (t : ℝ)
    (hg : Differentiable ℝ g) (hgd : Continuous (deriv g)) :
    ‖g t‖ ^ 2 ≤ ∫ x : ℝ in t..t + 1, 2 * ‖g x‖ ^ 2 + ‖deriv g x‖ ^ 2 := by
  let h : ℝ → ℝ := fun x => ‖g x‖ ^ 2
  let q : ℝ → ℝ := fun x => ‖g x‖ ^ 2 + ‖deriv g x‖ ^ 2
  have hhCont : Continuous h := hg.continuous.norm.pow 2
  have hqCont : Continuous q := hg.continuous.norm.pow 2 |>.add (hgd.norm.pow 2)
  have hderivBound : ∀ y : ℝ, ‖deriv h y‖ ≤ q y := by
    intro y
    have hy := (hg y).hasDerivAt.norm_sq
    have hderiv := hy.deriv
    rw [hderiv, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hinner : |inner ℝ (g y) (deriv g y)| ≤ ‖g y‖ * ‖deriv g y‖ :=
      abs_real_inner_le_norm _ _
    dsimp [q]
    calc
      2 * |inner ℝ (g y) (deriv g y)| ≤ 2 * (‖g y‖ * ‖deriv g y‖) :=
        mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ ‖g y‖ ^ 2 + ‖deriv g y‖ ^ 2 := by
        nlinarith [sq_nonneg (‖g y‖ - ‖deriv g y‖)]
  have hpoint : ∀ x ∈ Set.Icc t (t + 1), h t ≤ h x + ∫ y : ℝ in t..t + 1, q y := by
    intro x hx
    have htx : t ≤ x := hx.1
    have hdist : ‖h x - h t‖ ≤ ∫ y : ℝ in t..x, q y := by
      apply norm_sub_le_integral_of_norm_deriv_le_of_le htx
      · exact hhCont.continuousOn
      · intro y hy
        exact (hg y).hasDerivAt.norm_sq.differentiableAt.differentiableWithinAt
      · exact Filter.Eventually.of_forall fun y _hy => hderivBound y
      · exact hqCont.intervalIntegrable (μ := MeasureTheory.volume) t x
    have hmono : (∫ y : ℝ in t..x, q y) ≤ ∫ y : ℝ in t..t + 1, q y := by
      apply intervalIntegral.integral_mono_interval le_rfl htx hx.2
      · exact Filter.Eventually.of_forall fun y => by
          change 0 ≤ q y
          dsimp [q]
          positivity
      · exact hqCont.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1)
    have hbasic : h t ≤ h x + ‖h x - h t‖ := by
      rw [Real.norm_eq_abs]
      linarith [neg_le_abs (h x - h t)]
    exact hbasic.trans (by
      simpa [add_comm] using add_le_add_left (hdist.trans hmono) (h x))
  let Q : ℝ := ∫ y : ℝ in t..t + 1, q y
  have hfInt : IntervalIntegrable (fun _ : ℝ => h t) MeasureTheory.volume t (t + 1) :=
    continuous_const.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1)
  have hgInt : IntervalIntegrable (fun x => h x + Q) MeasureTheory.volume t (t + 1) :=
    (hhCont.add continuous_const).intervalIntegrable (μ := MeasureTheory.volume) t (t + 1)
  have hpointQ : ∀ x ∈ Set.Icc t (t + 1), h t ≤ h x + Q := by
    simpa [Q] using hpoint
  have hmonoInt := intervalIntegral.integral_mono_on (show t ≤ t + 1 by linarith)
    hfInt hgInt hpointQ
  dsimp [h] at hmonoInt ⊢
  rw [intervalIntegral.integral_const] at hmonoInt
  norm_num at hmonoInt
  dsimp [Q, q] at hmonoInt
  refine hmonoInt.trans_eq ?_
  rw [intervalIntegral.integral_add
    (hg.continuous.norm.pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))]
  rw [intervalIntegral.integral_const]
  norm_num
  rw [intervalIntegral.integral_add
    (hg.continuous.norm.pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))
    (hgd.norm.pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))]
  rw [← add_assoc]
  rw [← intervalIntegral.integral_add
    (hg.continuous.norm.pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))
    (hg.continuous.norm.pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))]
  rw [← intervalIntegral.integral_add
    (f := fun x => ‖g x‖ ^ 2 + ‖g x‖ ^ 2)
    (g := fun x => ‖deriv g x‖ ^ 2)
    ((hg.continuous.norm.pow 2).add (hg.continuous.norm.pow 2) |>.intervalIntegrable
      (μ := MeasureTheory.volume) t (t + 1))
    (hgd.norm.pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1))]
  congr 1
  funext x
  ring_nf

lemma sum_local_intervalIntegrals_le (T : ℝ) (W : Finset ℝ) (q : ℝ → ℝ)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hBase : RiemannZeta.GuthMaynard.InBaseInterval T W)
    (hT : 0 ≤ T) (hqCont : Continuous q) (hqNonneg : ∀ x, 0 ≤ q x) :
    (∑ t ∈ W, ∫ x : ℝ in t..t + 1, q x) ≤ ∫ x : ℝ in 0..T + 1, q x := by
  let A : ℝ → Set ℝ := fun t => Set.Ioc t (t + 1)
  have hPair : Set.Pairwise (↑W : Set ℝ) (Function.onFun Disjoint A) := by
    intro x hx y hy hxy
    change Disjoint (A x) (A y)
    rw [Set.disjoint_left]
    intro z hzx hzy
    have hdist := hSep x hx y hy hxy
    rw [Real.dist_eq] at hdist
    have hxData : x < z ∧ z ≤ x + 1 := hzx
    have hyData : y < z ∧ z ≤ y + 1 := hzy
    rcases lt_or_gt_of_ne hxy with hxylt | hyxlt
    · have : 1 ≤ y - x := by
        rw [abs_of_nonpos (sub_nonpos.mpr hxylt.le)] at hdist
        simpa only [neg_sub] using hdist
      linarith
    · have : 1 ≤ x - y := by
        rw [abs_of_nonneg (sub_nonneg.mpr hyxlt.le)] at hdist
        exact hdist
      linarith
  have hUnionSubset : (⋃ t ∈ W, A t) ⊆ Set.Ioc 0 (T + 1) := by
    intro z hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨t, hz⟩ := hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨htW, hzt⟩ := hz
    have htBase := hBase t htW
    exact ⟨lt_of_le_of_lt htBase.1 hzt.1, by linarith [hzt.2, htBase.2]⟩
  have hUnionEq :
      (∫ x in ⋃ t ∈ W, A t, q x) = ∑ t ∈ W, ∫ x in A t, q x := by
    apply MeasureTheory.integral_biUnion_finset W
    · intro t ht
      exact measurableSet_Ioc
    · exact hPair
    · intro t ht
      exact (hqCont.intervalIntegrable (μ := MeasureTheory.volume) t (t + 1)).1
  have hMono : (∫ x in ⋃ t ∈ W, A t, q x) ≤ ∫ x in Set.Ioc 0 (T + 1), q x := by
    apply MeasureTheory.setIntegral_mono_set
    · exact hqCont.intervalIntegrable (μ := MeasureTheory.volume) 0 (T + 1) |>.1
    · exact Filter.Eventually.of_forall fun x => hqNonneg x
    · exact hUnionSubset.eventuallyLE
  rw [hUnionEq] at hMono
  have hLocal : ∀ t ∈ W, (∫ x : ℝ in t..t + 1, q x) = ∫ x in A t, q x := by
    intro t ht
    rw [intervalIntegral.integral_of_le (by linarith : t ≤ t + 1)]
  calc
    (∑ t ∈ W, ∫ x : ℝ in t..t + 1, q x) = ∑ t ∈ W, ∫ x in A t, q x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact hLocal t ht
    _ ≤ ∫ x in Set.Ioc 0 (T + 1), q x := hMono
    _ = ∫ x : ℝ in 0..T + 1, q x := by
      rw [intervalIntegral.integral_of_le (by linarith)]

/-- The `centeredDirichletTime` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def centeredDirichletTime (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N),
    a n * Complex.exp
      (Complex.I * (t : ℂ) * ((Real.log N - Real.log n : ℝ) : ℂ))

/-- The `centeredDerivCoeff` definition used by the source-facing construction in `MeanValueProof`. -/
noncomputable def centeredDerivCoeff (N : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n * (Complex.I * ((Real.log N - Real.log n : ℝ) : ℂ))

lemma centeredDirichletTime_eq (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    centeredDirichletTime N a t =
      Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) * dirichletTime N a t := by
  simp only [centeredDirichletTime, dirichletTime, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [show Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) *
      (a n * Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) =
    a n * (Complex.exp (Complex.I * (t : ℂ) * (Real.log N : ℂ)) *
      Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ)))) by ring]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

lemma norm_centeredDirichletTime (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖centeredDirichletTime N a t‖ = ‖dirichletTime N a t‖ := by
  rw [centeredDirichletTime_eq, norm_mul, Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * (Real.log N : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring_nf
  rw [hre, Real.exp_zero, one_mul]

lemma hasDerivAt_centeredDirichletTime (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    HasDerivAt (centeredDirichletTime N a)
      (centeredDirichletTime N (centeredDerivCoeff N a) t) t := by
  unfold centeredDirichletTime
  apply HasDerivAt.fun_sum
  intro n hn
  let c : ℂ := Complex.I * ((Real.log N - Real.log n : ℝ) : ℂ)
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (c * (x : ℂ)))
      (Complex.exp (c * (t : ℂ)) * c) t := by
    convert (Complex.hasDerivAt_exp (c * (t : ℂ))).comp t
      (((hasDerivAt_id t).ofReal_comp).const_mul c) using 1
    all_goals simp
  convert hexp.const_mul (a n) using 1
  · funext y
    congr 2
    dsimp [c]
    ring
  · dsimp [centeredDerivCoeff, c]
    ring_nf

lemma differentiable_centeredDirichletTime (N : ℕ) (a : ℕ → ℂ) :
    Differentiable ℝ (centeredDirichletTime N a) := by
  intro t
  exact (hasDerivAt_centeredDirichletTime N a t).differentiableAt

lemma deriv_centeredDirichletTime (N : ℕ) (a : ℕ → ℂ) (t : ℝ) :
    deriv (centeredDirichletTime N a) t =
      centeredDirichletTime N (centeredDerivCoeff N a) t :=
  (hasDerivAt_centeredDirichletTime N a t).deriv

lemma continuous_deriv_centeredDirichletTime (N : ℕ) (a : ℕ → ℂ) :
    Continuous (deriv (centeredDirichletTime N a)) := by
  rw [show deriv (centeredDirichletTime N a) =
      centeredDirichletTime N (centeredDerivCoeff N a) by
    funext t
    exact deriv_centeredDirichletTime N a t]
  exact differentiable_centeredDirichletTime N (centeredDerivCoeff N a) |>.continuous

lemma abs_log_ratio_le_one (N n : ℕ) (hN : 0 < N) (hn : n ∈ Finset.Ioc N (2 * N)) :
    |Real.log N - Real.log n| ≤ 1 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnR : (0 : ℝ) < n := by exact_mod_cast
    (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
  have hn2N : (n : ℝ) ≤ 2 * N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hlogNn : Real.log N ≤ Real.log n := Real.log_le_log hNR hNn
  have hlogn2N : Real.log n ≤ Real.log (2 * N) := Real.log_le_log hnR hn2N
  have hlogTwo : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at h ⊢
    exact h
  rw [abs_of_nonpos (sub_nonpos.mpr hlogNn)]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by exact_mod_cast hN.ne') ] at hlogn2N
  linarith

lemma centeredDerivCoeff_l2_le (N : ℕ) (a : ℕ → ℂ) (hN : 0 < N) :
    (∑ n ∈ Finset.Ioc N (2 * N), ‖centeredDerivCoeff N a n‖ ^ 2) ≤
      ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro n hn
  rw [centeredDerivCoeff, norm_mul, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  have hlog := abs_log_ratio_le_one N n hN hn
  have hnonneg : 0 ≤ |Real.log N - Real.log n| := abs_nonneg _
  have ha : 0 ≤ ‖a n‖ := norm_nonneg _
  have hmul : ‖a n‖ * |Real.log N - Real.log n| ≤ ‖a n‖ :=
    mul_le_of_le_one_right ha hlog
  nlinarith [sq_nonneg (‖a n‖ - ‖a n‖ * |Real.log N - Real.log n|)]

lemma nat_cpow_neg_mul_I_eq (n : ℕ) (t : ℝ) (hn : 0 < n) :
    (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
      Complex.exp (-(Complex.I * (t : ℂ) * (Real.log n : ℂ))) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne')]
  rw [← Complex.natCast_log]
  congr 1
  ring

theorem montgomery_mean_value_estimate (N : ℕ) (T : ℝ) (W : Finset ℝ) (a : ℕ → ℂ)
    (hN : 0 < N) (hT : 1 ≤ T)
    (hSep : RiemannZeta.GuthMaynard.IsSeparated 1 W)
    (hBase : RiemannZeta.GuthMaynard.InBaseInterval T W) :
    (∑ t ∈ W, ‖∑ n ∈ Finset.Ioc N (2 * N),
      a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2) ≤
      (3 * (2 + 2 * (5 * Real.pi + 1))) * (T + (N : ℝ)) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
  let g : ℝ → ℂ := centeredDirichletTime N a
  let b : ℕ → ℂ := centeredDerivCoeff N a
  let q : ℝ → ℝ := fun x => 2 * ‖g x‖ ^ 2 + ‖deriv g x‖ ^ 2
  let S : ℝ := ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2
  let K : ℝ := 2 * (5 * Real.pi + 1)
  let U : ℝ := T + 1
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hU : 0 ≤ U := by dsimp [U]; linarith
  have hphase : ∀ t ∈ W,
      (∑ n ∈ Finset.Ioc N (2 * N), a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
        dirichletTime N a t := by
    intro t ht
    apply Finset.sum_congr rfl
    intro n hn
    rw [nat_cpow_neg_mul_I_eq n t
      (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)]
  have hgDiff : Differentiable ℝ g := differentiable_centeredDirichletTime N a
  have hgdCont : Continuous (deriv g) := continuous_deriv_centeredDirichletTime N a
  have hqCont : Continuous q := by
    dsimp [q]
    exact (hgDiff.continuous.norm.pow 2).const_mul 2 |>.add (hgdCont.norm.pow 2)
  have hqNonneg : ∀ x, 0 ≤ q x := by
    intro x
    dsimp [q]
    positivity
  have hLocal : ∀ t ∈ W, ‖g t‖ ^ 2 ≤ ∫ x : ℝ in t..t + 1, q x := by
    intro t ht
    exact local_sample_le_energy g t hgDiff hgdCont
  have hDisjoint := sum_local_intervalIntegrals_le T W q hSep hBase
    (by linarith : 0 ≤ T) hqCont hqNonneg
  have hMain : (∫ x : ℝ in 0..U, ‖g x‖ ^ 2) ≤ (U + K * (N : ℝ)) * S := by
    dsimp [g, U, K, S]
    simpa only [norm_centeredDirichletTime] using
      integral_norm_sq_dirichletTime_le N (T + 1) a hN (by linarith)
  have hbL2 : (∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2) ≤ S := by
    exact centeredDerivCoeff_l2_le N a hN
  have hDerivRaw :
      (∫ x : ℝ in 0..U, ‖deriv g x‖ ^ 2) ≤
        (U + K * (N : ℝ)) * ∑ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ^ 2 := by
    dsimp [g, b, U, K]
    simp_rw [deriv_centeredDirichletTime, norm_centeredDirichletTime]
    exact integral_norm_sq_dirichletTime_le N (T + 1) (centeredDerivCoeff N a)
      hN (by linarith)
  have hFactor : 0 ≤ U + K * (N : ℝ) := by positivity
  have hDeriv : (∫ x : ℝ in 0..U, ‖deriv g x‖ ^ 2) ≤
      (U + K * (N : ℝ)) * S :=
    hDerivRaw.trans (mul_le_mul_of_nonneg_left hbL2 hFactor)
  have hGlobal : (∫ x : ℝ in 0..U, q x) ≤ 3 * (U + K * (N : ℝ)) * S := by
    dsimp [q]
    rw [intervalIntegral.integral_add
      ((hgDiff.continuous.norm.pow 2).const_mul 2 |>.intervalIntegrable
        (μ := MeasureTheory.volume) 0 U)
      (hgdCont.norm.pow 2 |>.intervalIntegrable (μ := MeasureTheory.volume) 0 U)]
    rw [intervalIntegral.integral_const_mul]
    calc
      2 * (∫ x : ℝ in 0..U, ‖g x‖ ^ 2) +
          ∫ x : ℝ in 0..U, ‖deriv g x‖ ^ 2 ≤
          2 * ((U + K * (N : ℝ)) * S) + (U + K * (N : ℝ)) * S := by
        exact add_le_add (mul_le_mul_of_nonneg_left hMain (by norm_num)) hDeriv
      _ = 3 * (U + K * (N : ℝ)) * S := by ring
  have hScale : U + K * (N : ℝ) ≤ (2 + K) * (T + (N : ℝ)) := by
    have hNR : (0 : ℝ) < N := by exact_mod_cast hN
    dsimp [U]
    nlinarith
  calc
    (∑ t ∈ W, ‖∑ n ∈ Finset.Ioc N (2 * N),
        a n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2) =
        ∑ t ∈ W, ‖g t‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [hphase t ht]
          dsimp [g]
          rw [norm_centeredDirichletTime]
    _ ≤ ∑ t ∈ W, ∫ x : ℝ in t..t + 1, q x := by
      exact Finset.sum_le_sum hLocal
    _ ≤ ∫ x : ℝ in 0..T + 1, q x := hDisjoint
    _ ≤ 3 * (U + K * (N : ℝ)) * S := by simpa [U] using hGlobal
    _ ≤ 3 * ((2 + K) * (T + (N : ℝ))) * S := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hScale (by norm_num)) hS
    _ = (3 * (2 + 2 * (5 * Real.pi + 1))) * (T + (N : ℝ)) *
        ∑ n ∈ Finset.Ioc N (2 * N), ‖a n‖ ^ 2 := by
      dsimp [K, S]
      ring

theorem montgomery_mean_value_native :
    RiemannZeta.GuthMaynard.MontgomeryMeanValue := by
  refine ⟨3 * (2 + 2 * (5 * Real.pi + 1)), by positivity, ?_⟩
  intro N T W a hN hT hSep hBase
  exact montgomery_mean_value_estimate N T W a hN hT hSep hBase

end RiemannZeta.GuthMaynard
