import PrimeNumberTheoremAnd.ZetaBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform zeta bound to the left of one

The installed Euler–Maclaurin continuation retains its pole explicitly.
All estimates are uniform down to zero height and up to lambda one half.
-/

namespace DongWangWangZhang2026

open Complex MeasureTheory Set intervalIntegral

noncomputable section

/-- The finite power sum with its exact reciprocal-exponent loss. -/
theorem sum_Icc_rpow_sub_one_le (N : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    ∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (a - 1) ≤ (N : ℝ) ^ a / a := by
  induction N with
  | zero => simp [Real.zero_rpow ha.ne']
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    by_cases hN : N = 0
    · subst N
      simpa using (one_le_div ha).mpr ha1
    have hN0 : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hm : AntitoneOn (fun u : ℝ => u ^ (a - 1)) (Icc (N : ℝ) (N + 1)) := by
      intro u hu v _ huv
      exact Real.rpow_le_rpow_of_nonpos (hN0.trans_le hu.1) huv (by linarith)
    have hm' : AntitoneOn (fun u : ℝ => u ^ (a - 1))
        (Icc (N : ℝ) ((N : ℝ) + (1 : ℕ))) := by simpa only [Nat.cast_one] using hm
    have hcell := hm'.sum_le_integral
    simp only [Finset.sum_range_one, Nat.cast_one, zero_add] at hcell
    rw [integral_rpow (Or.inl (by linarith)), sub_add_cancel, sub_div] at hcell
    push_cast
    linarith

/-- Uniform finite truncation error with the zeta pole left in the main term. -/
theorem norm_zeta_sub_sum_pole_le {N : ℕ} (hN : 1 ≤ N) {σ v : ℝ}
    (hσ : 0 < σ) (hs : (σ : ℂ) + v * Complex.I ≠ 1) :
    ‖riemannZeta ((σ : ℂ) + v * Complex.I) -
      ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ ((σ : ℂ) + v * Complex.I)) +
        (-(N : ℂ) ^ (1 - ((σ : ℂ) + v * Complex.I))) /
          (1 - ((σ : ℂ) + v * Complex.I)))‖ ≤
      (N : ℝ) ^ (-σ) / 2 + (σ + |v|) * (N : ℝ) ^ (-σ) / σ := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  rw [← Zeta0EqZeta (by omega : 0 < N) (by simpa using hσ) hs, riemannZeta0]
  rw [show ∀ a b c d : ℂ, a + b + c + d - (a + b) = c + d by intros; ring]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div, norm_neg, show ‖(2 : ℂ)‖ = 2 by norm_num]
    rw [show (N : ℂ) = ((N : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos hN0]
    simp
  · rw [norm_mul]
    have hnorm : ‖(σ : ℂ) + v * Complex.I‖ ≤ σ + |v| := by
      simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hσ, norm_mul,
        norm_I, mul_one] using norm_add_le (σ : ℂ) (v * Complex.I)
    exact (mul_le_mul hnorm (ZetaBnd_aux1b N hN hσ) (norm_nonneg _) (by positivity)).trans_eq
      (by ring)

/-- The Dirichlet polynomial in the continuation has the required uniform size. -/
theorem norm_zeta_polynomial_le (N : ℕ) {a v : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    ‖∑ n ∈ Finset.range (N + 1),
      1 / (n : ℂ) ^ (((1 - a : ℝ) : ℂ) + v * Complex.I)‖ ≤ (N : ℝ) ^ a / a := by
  have hs0 : ((1 - a : ℝ) : ℂ) + v * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, zero_re] at this
    linarith
  rw [Finset.sum_range_eq_add_Ico _ (by omega)]
  simp only [Nat.cast_zero, Complex.zero_cpow hs0, div_zero, zero_add,
    Finset.Ico_add_one_right_eq_Icc]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun n hn => ?_).trans
    (sum_Icc_rpow_sub_one_le N ha (by linarith)))
  have hn0 : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)
  rw [norm_div, norm_one, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
    norm_cpow_eq_rpow_re_of_pos hn0]
  simp only [add_re, ofReal_re, mul_I_re, ofReal_im]
  rw [one_div, ← Real.rpow_neg hn0.le]
  exact le_of_eq (by congr 1; ring)

/-- Left-strip zeta estimate at any natural cutoff above the height. -/
theorem norm_zeta_left_strip_le_cutoff {N : ℕ} {a v : ℝ}
    (ha : 0 < a) (ha2 : a ≤ 1 / 2) (hNv : 2 + |v| ≤ (N : ℝ)) :
    ‖riemannZeta (((1 - a : ℝ) : ℂ) + v * Complex.I)‖ ≤ 4 * (N : ℝ) ^ a / a := by
  have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg v]
  have hN : 1 ≤ N := by exact_mod_cast hN1
  have hN0 : 0 < (N : ℝ) := by linarith
  have hσ : 0 < 1 - a := by linarith
  have hs : ((1 - a : ℝ) : ℂ) + v * Complex.I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, one_re] at this
    linarith
  have hpoly := norm_zeta_polynomial_le N (v := v) ha ha2
  have herr := norm_zeta_sub_sum_pole_le hN hσ hs
  have hpole :
      ‖(-(N : ℂ) ^ (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I))) /
        (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I))‖ ≤ (N : ℝ) ^ a / a := by
    rw [norm_div, norm_neg, show (N : ℂ) = ((N : ℝ) : ℂ) by simp,
      norm_cpow_eq_rpow_re_of_pos hN0]
    have hre : (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I)).re = a := by simp
    rw [hre]
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) ha
    have h := Complex.abs_re_le_norm (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I))
    simpa only [hre, abs_of_pos ha] using h
  have htail : (1 - a + |v|) * (N : ℝ) ^ (-(1 - a)) / (1 - a) ≤ (N : ℝ) ^ a / a := by
    calc
      _ ≤ (N : ℝ) * (N : ℝ) ^ (-(1 - a)) / (1 - a) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hN0.le _)) hσ.le
      _ = (N : ℝ) ^ a / (1 - a) := by
        rw [show -(1 - a) = a - 1 by ring, Real.rpow_sub hN0, Real.rpow_one]
        congr 1
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) ha (by linarith)
  have hhalf : (N : ℝ) ^ (-(1 - a)) / 2 ≤ (N : ℝ) ^ a / a := by
    calc
      _ ≤ (N : ℝ) ^ a / 2 := div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hN0.le _) ha (by linarith)
  have htriangle := norm_add_le
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ (((1 - a : ℝ) : ℂ) + v * Complex.I))
    ((-(N : ℂ) ^ (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I))) /
      (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I)))
  have hz := norm_add_le
    (riemannZeta (((1 - a : ℝ) : ℂ) + v * Complex.I) -
      ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ (((1 - a : ℝ) : ℂ) + v * Complex.I)) +
        (-(N : ℂ) ^ (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I))) /
          (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I))))
    ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ (((1 - a : ℝ) : ℂ) + v * Complex.I)) +
        (-(N : ℂ) ^ (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I))) /
          (1 - (((1 - a : ℝ) : ℂ) + v * Complex.I)))
  simp only [sub_add_cancel] at hz
  simp only [div_eq_mul_inv] at herr hpole htail hhalf hpoly htriangle hz ⊢
  linarith only [herr, hpole, htail, hhalf, hpoly, htriangle, hz]

/-- Lemma 3.1, with an explicit absolute constant and no height restriction. -/
theorem norm_zeta_left_strip_le (a v : ℝ) (ha : 0 < a) (ha2 : a ≤ 1 / 2) :
    ‖riemannZeta (((1 - a : ℝ) : ℂ) + v * Complex.I)‖ ≤
      8 * (2 + |v|) ^ a / a := by
  let X := 2 + |v|
  let N := ⌈X⌉₊
  have hX : 0 < X := by dsimp [X]; positivity
  have hNX : X ≤ (N : ℝ) := Nat.le_ceil X
  have hNupper : (N : ℝ) ≤ 2 * X :=
    (Nat.ceil_lt_add_one hX.le).le.trans (by dsimp [X]; linarith [abs_nonneg v])
  have hp : (N : ℝ) ^ a ≤ 2 * X ^ a := by
    calc
      _ ≤ (2 * X) ^ a := Real.rpow_le_rpow (by positivity) hNupper ha.le
      _ = (2 : ℝ) ^ a * X ^ a := Real.mul_rpow (by norm_num) hX.le
      _ ≤ 2 * X ^ a := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by linarith)) (Real.rpow_nonneg hX.le _)
  exact (norm_zeta_left_strip_le_cutoff ha ha2 hNX).trans
    (div_le_div_of_nonneg_right (by nlinarith only [hp]) ha.le)

end
end DongWangWangZhang2026
