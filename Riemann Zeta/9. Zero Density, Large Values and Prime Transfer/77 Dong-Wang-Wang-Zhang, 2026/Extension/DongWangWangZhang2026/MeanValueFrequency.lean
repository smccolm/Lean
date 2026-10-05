import DongWangWangZhang2026.MeanValueTransform
import GuthMaynard.MeanValueProof
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.PSeries

/-!
# Frequency estimates for the actual logarithmic coefficients

The existing continuous Montgomery estimate supplies the block mean square.
A Gaussian Gram argument then gives the sharp index-weighted estimate for full
initial segments; dominated convergence and explicit coefficient sums give the
full zeta-derivative mean square and two-sided far tail. All constants are uniform
in the height twist. This Gaussian averaging is distinct from the paper's
residue-bearing continued transform.
-/

namespace DongWangWangZhang2026

open Complex Finset MeasureTheory Filter
open scoped Topology

noncomputable section

/-- A dyadic block of the logarithmically weighted shifted zeta series. -/
def zetaLogBlock (N : ℕ) (σ t y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2 * N), ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * zetaTerm (t - y) n

/-- These blocks contain the exact coefficients of the differentiated phase series. -/
theorem zetaLogBlock_eq_LSeries_terms (N : ℕ) (σ t y : ℝ) :
    zetaLogBlock N σ t y = ∑ n ∈ Finset.Ioc N (2 * N),
      LSeries.term (fun m => (Real.log m : ℂ) * zetaTerm t m) ((σ : ℂ) + (y : ℂ) * I) n := by
  unfold zetaLogBlock
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)
  have hcn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  rw [LSeries.term_of_ne_zero hn0]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast,
    zetaTerm_eq_cpow _ hn0, zetaTerm_eq_cpow _ hn0, mul_div_assoc,
    ← Complex.cpow_sub _ _ hcn, mul_assoc, ← Complex.cpow_add _ _ hcn]
  congr 2
  push_cast
  ring

/-- Exact adapter to the proved foundation mean-value polynomial, including interval translation. -/
theorem zetaLogBlock_eq_dirichletTime (N : ℕ) (σ t a u : ℝ) :
    zetaLogBlock N σ t (u + a) = RiemannZeta.GuthMaynard.dirichletTime N
      (fun n => ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * zetaTerm (t - a) n) u := by
  unfold zetaLogBlock RiemannZeta.GuthMaynard.dirichletTime
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1)
  have hphase : zetaTerm (-u) n = Complex.exp (-(I * (u : ℂ) * (Real.log n : ℂ))) := by
    rw [zetaTerm_eq_exp (-u) hn0]
    congr 1
    push_cast
    ring
  rw [show t - (u + a) = (t - a) + (-u) by ring, zetaTerm_add,
    hphase, mul_assoc]
  dsimp only
  rw [mul_assoc]

theorem norm_logPhaseCoeff (n : ℕ) (σ t : ℝ) :
    ‖((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * zetaTerm t n‖ =
      Real.log n * (n : ℝ) ^ (-σ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  rw [norm_mul, norm_zetaTerm t (Nat.pos_of_ne_zero hn), mul_one, Complex.norm_real,
    Real.norm_of_nonneg (mul_nonneg (Real.log_nonneg hn1) (Real.rpow_nonneg (Nat.cast_nonneg n) _))]

theorem continuous_zetaLogBlock (N : ℕ) (σ t : ℝ) : Continuous (zetaLogBlock N σ t) := by
  have h := RiemannZeta.GuthMaynard.continuous_dirichletTime N
    (fun n => ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * zetaTerm t n)
  apply h.congr
  intro y
  simpa only [add_zero, sub_zero] using (zetaLogBlock_eq_dirichletTime N σ t 0 y).symm

/-- Uniform shifted-interval mean square for the actual coefficient block.
No maximum, mean-value inequality or tail bound is taken as an assumption. -/
theorem integral_norm_sq_zetaLogBlock_le (N : ℕ) (σ t a b : ℝ)
    (hN : 0 < N) (hab : a ≤ b) :
    (∫ y : ℝ in a..b, ‖zetaLogBlock N σ t y‖ ^ 2) ≤
      (b - a + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        ∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2 := by
  have hshift := intervalIntegral.integral_comp_add_right
    (fun y : ℝ => ‖zetaLogBlock N σ t y‖ ^ 2) a (a := 0) (b := b - a)
  simp only [zero_add, sub_add_cancel] at hshift
  rw [← hshift]
  simp_rw [zetaLogBlock_eq_dirichletTime]
  have h := RiemannZeta.GuthMaynard.integral_norm_sq_dirichletTime_le N (b - a)
    (fun n => ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * zetaTerm (t - a) n) hN (sub_nonneg.mpr hab)
  simpa only [norm_logPhaseCoeff] using h

/-- A frequency interval separated from zero gains the square of its distance.
The only mean-square input is the already-proved continuous foundation theorem. -/
theorem integral_zetaLogBlock_quotient_le (N : ℕ) (σ t a b R : ℝ)
    (hN : 0 < N) (hσ : 0 < σ) (hab : a ≤ b) (hR : 0 < R)
    (hgap : ∀ y ∈ Set.Icc a b, R ≤ |y|) :
    (∫ y : ℝ in a..b, ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      (b - a + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        (∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2) / R ^ 2 := by
  have hquot : Continuous (fun y : ℝ => zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)) :=
    (continuous_zetaLogBlock N σ t).div (by fun_prop)
      (fun y => Complex.ne_zero_of_re_pos (by simpa using hσ))
  have hraw := (continuous_zetaLogBlock N σ t).norm.pow 2
  calc
    _ ≤ ∫ y : ℝ in a..b, ‖zetaLogBlock N σ t y‖ ^ 2 / R ^ 2 := by
      apply intervalIntegral.integral_mono_on hab
        ((hquot.norm.pow 2).intervalIntegrable a b) ((hraw.div_const (R ^ 2)).intervalIntegrable a b)
      intro y hy
      rw [norm_div, div_pow]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hR)
      have hgap₂ := pow_le_pow_left₀ hR.le (hgap y hy) 2
      rw [sq_abs] at hgap₂
      have hden : ‖(σ : ℂ) + (y : ℂ) * I‖ ^ 2 = σ ^ 2 + y ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [pow_two]
      rw [hden]
      nlinarith [sq_nonneg σ]
    _ = (∫ y : ℝ in a..b, ‖zetaLogBlock N σ t y‖ ^ 2) / R ^ 2 :=
      intervalIntegral.integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right (integral_norm_sq_zetaLogBlock_le N σ t a b hN hab)
      (sq_nonneg R)

/-- Positive dyadic frequency shell, at the exact derivative-series coefficients. -/
theorem integral_zetaLogBlock_positive_shell_le (N : ℕ) (σ t T : ℝ)
    (hN : 0 < N) (hσ : 0 < σ) (hT : 0 < T) :
    (∫ y : ℝ in T..2 * T, ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        (∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2) / T ^ 2 := by
  have h := integral_zetaLogBlock_quotient_le N σ t T (2 * T) T hN hσ (by linarith) hT
    (fun y hy => hy.1.trans (le_abs_self y))
  convert h using 1
  ring

/-- Negative dyadic shell; no sign restriction on the height or cancellation parameter. -/
theorem integral_zetaLogBlock_negative_shell_le (N : ℕ) (σ t T : ℝ)
    (hN : 0 < N) (hσ : 0 < σ) (hT : 0 < T) :
    (∫ y : ℝ in -(2 * T)..-T, ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        (∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2) / T ^ 2 := by
  have h := integral_zetaLogBlock_quotient_le N σ t (-(2 * T)) (-T) T hN hσ (by linarith) hT
    (fun y hy => (by linarith [hy.2] : T ≤ -y).trans (neg_le_abs y))
  convert h using 1
  ring

private theorem dyadic_frequency_tail {F : ℝ → ℝ} {K S T : ℝ}
    (hF : Continuous F) (hF0 : ∀ y, 0 ≤ F y) (hK : 0 ≤ K) (hS : 0 ≤ S) (hT : 0 < T)
    (hshell : ∀ U : ℝ, T ≤ U → (∫ y : ℝ in U..2 * U, F y) ≤ (U + K) * S / U ^ 2) :
    IntegrableOn F (Set.Ioi T) ∧ (∫ y in Set.Ioi T, F y) ≤ 2 * (T + K) * S / T ^ 2 := by
  let a : ℕ → ℝ := fun n => (2 : ℝ) ^ n * T
  let E : ℕ → Set ℝ := fun n => Set.Ioc (a n) (a (n + 1))
  let B : ℝ := (T + K) * S / T ^ 2
  have ha0 (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ham : Monotone a := fun m n hmn =>
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hmn) hT.le
  have hsucc (n : ℕ) : a (n + 1) = 2 * a n := by dsimp [a]; rw [pow_succ]; ring
  have hatop : Tendsto a atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).atTop_mul_const hT
  have hcover : (⋃ n : ℕ, E n) = Set.Ioi T := by
    simpa only [E, a, bot_eq_zero, pow_zero, one_mul, Order.succ_eq_add_one] using
      iUnion_Ioc_map_succ_eq_Ioi (fun n => ham (Nat.zero_le n)) (not_bddAbove_of_tendsto_atTop hatop)
  have hdisj : Pairwise (fun m n => Disjoint (E m) (E n)) :=
    ham.pairwise_disjoint_on_Ioc_succ
  have hbound (n : ℕ) : (∫ y in E n, F y) ≤ B * (1 / 2 : ℝ) ^ n := by
    have hp1 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hscale : (a n + K) ≤ (2 : ℝ) ^ n * (T + K) := by
      dsimp [a]
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1) hK]
    calc
      _ = ∫ y : ℝ in a n..2 * a n, F y := by
        rw [intervalIntegral.integral_of_le (by linarith [ha0 n])]
        simp only [E, hsucc]
      _ ≤ (a n + K) * S / (a n) ^ 2 := hshell (a n)
        (by simpa only [a, pow_zero, one_mul] using ham (Nat.zero_le n))
      _ ≤ ((2 : ℝ) ^ n * (T + K)) * S / (a n) ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hscale hS) (sq_nonneg _)
      _ = B * (1 / 2 : ℝ) ^ n := by
        dsimp [a, B]
        rw [div_pow, one_pow]
        field_simp
  have hgeom₀ : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num) using 1
    norm_num
  have hgeom := hgeom₀.mul_left B
  have hsummable : Summable (fun n : ℕ => ∫ y in E n, ‖F y‖) := by
    simp_rw [Real.norm_of_nonneg (hF0 _)]
    exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => hF0 y) hbound hgeom.summable
  have hintUnion : IntegrableOn F (⋃ n : ℕ, E n) :=
    integrableOn_iUnion_of_summable_integral_norm
      (fun n => (hF.intervalIntegrable (μ := volume) (a n) (a (n + 1))).1) hsummable
  have hsum := hasSum_integral_iUnion (fun _ => measurableSet_Ioc) hdisj hintUnion
  have hle := hasSum_le hbound hsum hgeom
  rw [hcover] at hintUnion hle
  refine ⟨hintUnion, hle.trans_eq ?_⟩
  dsimp [B]
  ring

/-- Full positive frequency tail of one actual coefficient block, with convergence proved
by summing disjoint dyadic shells and no loss depending on the height. -/
theorem zetaLogBlock_positive_tail (N : ℕ) (σ t T : ℝ)
    (hN : 0 < N) (hσ : 0 < σ) (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2)
      (Set.Ioi T) ∧
    (∫ y in Set.Ioi T, ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      2 * (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        (∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2) / T ^ 2 := by
  have hquot : Continuous (fun y : ℝ => zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)) :=
    (continuous_zetaLogBlock N σ t).div (by fun_prop)
      (fun y => Complex.ne_zero_of_re_pos (by simpa using hσ))
  exact dyadic_frequency_tail (hquot.norm.pow 2) (fun _ => sq_nonneg _) (by positivity)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) hT
      (fun U hU => integral_zetaLogBlock_positive_shell_le N σ t U hN hσ (hT.trans_le hU))

theorem zetaLogBlock_neg_frequency (N : ℕ) (σ t y : ℝ) :
    zetaLogBlock N σ t (-y) = star (zetaLogBlock N σ (-t) y) := by
  unfold zetaLogBlock
  change _ = (starRingEnd ℂ) _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [map_mul, Complex.conj_ofReal]
  change _ = ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * star (zetaTerm (-t - y) n)
  rw [← zetaTerm_neg]
  congr 2
  ring

theorem norm_zetaLogBlock_quotient_neg (N : ℕ) (σ t y : ℝ) :
    ‖zetaLogBlock N σ t (-y) / ((σ : ℂ) + (-y : ℝ) * I)‖ =
      ‖zetaLogBlock N σ (-t) y / ((σ : ℂ) + (y : ℂ) * I)‖ := by
  rw [norm_div, norm_div, zetaLogBlock_neg_frequency, norm_star]
  have hden : (σ : ℂ) + (-y : ℝ) * I = star ((σ : ℂ) + (y : ℂ) * I) := by
    change _ = (starRingEnd ℂ) _
    simp
  rw [hden, norm_star]

/-- Negative tail obtained through the proved real-coefficient conjugation, preserving both signs. -/
theorem zetaLogBlock_negative_tail (N : ℕ) (σ t T : ℝ)
    (hN : 0 < N) (hσ : 0 < σ) (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2)
      (Set.Iio (-T)) ∧
    (∫ y in Set.Iio (-T), ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      2 * (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        (∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2) / T ^ 2 := by
  have hpos := zetaLogBlock_positive_tail N σ (-t) T hN hσ hT
  constructor
  · have hint : IntegrableOn
        (fun y : ℝ => ‖zetaLogBlock N σ (-t) y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2)
          (Set.Ioi (-(-T))) := by simpa only [neg_neg] using hpos.1
    simpa only [norm_zetaLogBlock_quotient_neg, neg_neg] using hint.comp_neg_Iio
  · rw [← integral_Iic_eq_integral_Iio,
      ← integral_comp_neg_Ioi T (fun y : ℝ => ‖zetaLogBlock N σ t y /
        ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2)]
    simpa only [norm_zetaLogBlock_quotient_neg] using hpos.2

/-- The complete two-sided far-frequency tail of one actual block. Summation of infinitely
many coefficient blocks is a separate obligation; it is not presumed here. -/
theorem zetaLogBlock_far_tail (N : ℕ) (σ t T : ℝ)
    (hN : 0 < N) (hσ : 0 < σ) (hT : 0 < T) :
    IntegrableOn (fun y : ℝ => ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2)
      {y : ℝ | T < |y|} ∧
    (∫ y in {y : ℝ | T < |y|}, ‖zetaLogBlock N σ t y / ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      4 * (T + 2 * (5 * Real.pi + 1) * (N : ℝ)) *
        (∑ n ∈ Finset.Ioc N (2 * N), (Real.log n * (n : ℝ) ^ (-σ)) ^ 2) / T ^ 2 := by
  have hpos := zetaLogBlock_positive_tail N σ t T hN hσ hT
  have hneg := zetaLogBlock_negative_tail N σ t T hN hσ hT
  have hset : {y : ℝ | T < |y|} = Set.Iio (-T) ∪ Set.Ioi T := by
    ext y
    change T < |y| ↔ y < -T ∨ T < y
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    apply Set.disjoint_left.mpr
    intro y hy₁ hy₂
    change y < -T at hy₁
    change T < y at hy₂
    linarith
  rw [hset]
  refine ⟨hneg.1.union hpos.1, ?_⟩
  rw [setIntegral_union hdisj measurableSet_Ioi hneg.1 hpos.1]
  calc
    _ ≤ _ := add_le_add hneg.2 hpos.2
    _ = _ := by ring

/-- Increasing power ratios give the lower half of a logarithmic-frequency kernel row. -/
theorem sum_lower_power_ratios_le (n : ℕ) (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) :
    (∑ m ∈ Finset.Icc 1 n, ((m : ℝ) / n) ^ p) ≤ 1 + (n : ℝ) / (p + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmon : MonotoneOn (fun x : ℝ => x ^ p) (Set.Icc 0 n) :=
    fun x hx y _ hxy => Real.rpow_le_rpow hx.1 hxy hp
  have hsum : (∑ m ∈ Finset.Icc 1 n, (m : ℝ) ^ p) ≤
      (n : ℝ) ^ p + (n : ℝ) ^ (p + 1) / (p + 1) := by
    calc
      _ ≤ ∑ m ∈ Finset.range (n + 1), (m : ℝ) ^ p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          simp only [Finset.mem_Icc] at hm
          simp only [Finset.mem_range]
          omega
        · intro m _ _
          exact Real.rpow_nonneg (Nat.cast_nonneg m) p
      _ = (∑ m ∈ Finset.range n, (m : ℝ) ^ p) + (n : ℝ) ^ p := Finset.sum_range_succ _ _
      _ ≤ (∫ x : ℝ in 0..n, x ^ p) + (n : ℝ) ^ p := by
        apply add_le_add _ le_rfl
        simpa only [Nat.Ico_zero_eq_range, Nat.cast_zero] using
          MonotoneOn.sum_le_integral_Ico (f := fun x : ℝ => x ^ p) (Nat.zero_le n)
            (by simpa only [Nat.cast_zero] using hmon)
      _ = _ := by
        rw [integral_rpow (Or.inl (by linarith)), Real.zero_rpow (by linarith : p + 1 ≠ 0), sub_zero]
        ring
  simp_rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg n)]
  rw [← Finset.sum_div]
  calc
    _ ≤ ((n : ℝ) ^ p + (n : ℝ) ^ (p + 1) / (p + 1)) / (n : ℝ) ^ p :=
      div_le_div_of_nonneg_right hsum (Real.rpow_nonneg hnR.le _)
    _ = _ := by
      rw [Real.rpow_add hnR, Real.rpow_one]
      field_simp [(Real.rpow_pos_of_pos hnR p).ne', (show p + 1 ≠ 0 by linarith)]

/-- The upper half of the same row is controlled by a convergent power-tail integral. -/
theorem sum_upper_power_ratios_le (n M : ℕ) (hn : 0 < n) {p : ℝ} (hp : 1 < p) :
    (∑ m ∈ Finset.Ioc n M, ((n : ℝ) / m) ^ p) ≤ (n : ℝ) / (p - 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hnM : n ≤ M
  · have hanti : AntitoneOn (fun x : ℝ => x ^ (-p)) (Set.Icc n M) :=
      fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos (hnR.trans_le hx.1) hxy (by linarith)
    have hI : Finset.Ioc n M = Finset.Ico (n + 1) (M + 1) := by
      ext m
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have hsum : (∑ m ∈ Finset.Ioc n M, (m : ℝ) ^ (-p)) ≤
        ∫ x in Set.Ioi (n : ℝ), x ^ (-p) := by
      calc
        _ = ∑ m ∈ Finset.Ico n M, ((m + 1 : ℕ) : ℝ) ^ (-p) := by
          rw [hI, ← Finset.sum_Ico_add']
        _ ≤ ∫ x : ℝ in (n : ℝ)..M, x ^ (-p) :=
          AntitoneOn.sum_le_integral_Ico hnM hanti
        _ ≤ ∫ x in Set.Ioi (n : ℝ), x ^ (-p) := by
          rw [intervalIntegral.integral_of_le (by exact_mod_cast hnM)]
          apply setIntegral_mono_set (integrableOn_Ioi_rpow_of_lt (by linarith) hnR)
          · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
            exact Real.rpow_nonneg (hnR.trans hx).le _
          · exact Filter.Eventually.of_forall fun x hx => hx.1
    have hterms (m : ℕ) : ((n : ℝ) / m) ^ p = (n : ℝ) ^ p * (m : ℝ) ^ (-p) := by
      rw [Real.div_rpow (Nat.cast_nonneg n) (Nat.cast_nonneg m),
        Real.rpow_neg (Nat.cast_nonneg m), div_eq_mul_inv]
    simp_rw [hterms, ← Finset.mul_sum]
    calc
      _ ≤ (n : ℝ) ^ p * ∫ x in Set.Ioi (n : ℝ), x ^ (-p) :=
        mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hnR.le _)
      _ = _ := by
        rw [integral_Ioi_rpow_of_lt (by linarith) hnR, ← mul_div_assoc, mul_neg,
          ← Real.rpow_add hnR]
        rw [show p + (-p + 1) = 1 by ring, Real.rpow_one,
          show -p + 1 = -(p - 1) by ring, neg_div_neg_eq]
  · rw [Finset.Ioc_eq_empty_of_le (le_of_not_ge hnM)]
    simp only [Finset.sum_empty]
    positivity

/-- The Gram kernel obtained by Gaussian averaging of logarithmic frequencies. -/
def logGaussianKernel (T : ℝ) (m n : ℕ) : ℝ :=
  Real.exp (-((T / 2) * (Real.log m - Real.log n)) ^ 2)

theorem logGaussianKernel_nonneg (T : ℝ) (m n : ℕ) :
    0 ≤ logGaussianKernel T m n := (Real.exp_pos _).le

theorem logGaussianKernel_symm (T : ℝ) (m n : ℕ) :
    logGaussianKernel T m n = logGaussianKernel T n m := by
  unfold logGaussianKernel
  congr 1
  ring

/-- Completing the square controls a Gaussian row by power ratios. No spacing
or cancellation hypothesis is imposed on the coefficients. -/
theorem logGaussianKernel_le_power_ratio (T : ℝ) (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) :
    logGaussianKernel T m n ≤ Real.exp (1 / 4) * ((m : ℝ) / n) ^ (T / 2) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos (div_pos hmR hnR), ← Real.exp_add,
    Real.log_div hmR.ne' hnR.ne']
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg ((T / 2) * (Real.log m - Real.log n) + 1 / 2)]

/-- A uniform row bound, with the correct linear dependence on the coefficient
index. This avoids the loss from summing the norms of separate dyadic blocks. -/
theorem sum_logGaussianKernel_le (T : ℝ) (n M : ℕ) (hT : 4 ≤ T) (hn : 0 < n) :
    (∑ m ∈ Finset.Icc 1 M, logGaussianKernel T m n) ≤
      Real.exp (1 / 4) * (1 + 6 * (n : ℝ) / T) := by
  have hTpos : 0 < T := by linarith
  have hp : 1 < T / 2 := by linarith
  have hcover : Finset.Icc 1 (max n M) = Finset.Icc 1 n ∪ Finset.Ioc n (max n M) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 n) (Finset.Ioc n (max n M)) := by
    apply Finset.disjoint_left.mpr
    intro m hm₁ hm₂
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hm₁ hm₂
    omega
  have hlower : (∑ m ∈ Finset.Icc 1 n, logGaussianKernel T m n) ≤
      Real.exp (1 / 4) * (1 + (n : ℝ) / (T / 2 + 1)) := by
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 n, Real.exp (1 / 4) * ((m : ℝ) / n) ^ (T / 2) := by
        apply Finset.sum_le_sum
        intro m hm
        exact logGaussianKernel_le_power_ratio T m n (Finset.mem_Icc.mp hm).1 hn
      _ = _ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_lower_power_ratios_le n hn (by linarith))
        (Real.exp_pos _).le
  have hupper : (∑ m ∈ Finset.Ioc n (max n M), logGaussianKernel T m n) ≤
      Real.exp (1 / 4) * ((n : ℝ) / (T / 2 - 1)) := by
    calc
      _ ≤ ∑ m ∈ Finset.Ioc n (max n M),
          Real.exp (1 / 4) * ((n : ℝ) / m) ^ (T / 2) := by
        apply Finset.sum_le_sum
        intro m hm
        rw [logGaussianKernel_symm]
        exact logGaussianKernel_le_power_ratio T n m hn (hn.trans (Finset.mem_Ioc.mp hm).1)
      _ = _ := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_upper_power_ratios_le n (max n M) hn hp)
        (Real.exp_pos _).le
  have hdiv₁ : (n : ℝ) / (T / 2 + 1) ≤ 2 * n / T := by
    apply (div_le_div_iff₀ (by linarith) hTpos).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hdiv₂ : (n : ℝ) / (T / 2 - 1) ≤ 4 * n / T := by
    apply (div_le_div_iff₀ (by linarith) hTpos).mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sub_nonneg.mpr hT)]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 (max n M), logGaussianKernel T m n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hm).1,
          (Finset.mem_Icc.mp hm).2.trans (le_max_right n M)⟩
      · intro m _ _
        exact logGaussianKernel_nonneg T m n
    _ = _ := by rw [hcover, Finset.sum_union hdisj]
    _ ≤ _ := add_le_add hlower hupper
    _ = Real.exp (1 / 4) * (1 + (n : ℝ) / (T / 2 + 1) + (n : ℝ) / (T / 2 - 1)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      calc
        _ ≤ 1 + 2 * (n : ℝ) / T + 4 * n / T := by linarith
        _ = _ := by ring

/-- The symmetric Gaussian Gram form has the sharp index-weighted diagonal bound. -/
theorem sum_logGaussianKernel_mul_le (T : ℝ) (M : ℕ) (b : ℕ → ℝ) (hT : 4 ≤ T) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
      logGaussianKernel T m n * b m * b n) ≤
        Real.exp (1 / 4) * ∑ n ∈ Finset.Icc 1 M, (1 + 6 * (n : ℝ) / T) * (b n) ^ 2 := by
  have hsym : (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
      logGaussianKernel T m n * (b m) ^ 2) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        logGaussianKernel T m n * (b n) ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n _
    apply Finset.sum_congr rfl
    intro m _
    rw [logGaussianKernel_symm]
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (logGaussianKernel T m n * (b m) ^ 2 +
          logGaussianKernel T m n * (b n) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro m _
      apply Finset.sum_le_sum
      intro n _
      nlinarith [mul_nonneg (logGaussianKernel_nonneg T m n) (sq_nonneg (b m - b n))]
    _ = ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        logGaussianKernel T m n * (b n) ^ 2 := by
      simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
      rw [hsym]
      ring
    _ = ∑ n ∈ Finset.Icc 1 M,
        (∑ m ∈ Finset.Icc 1 M, logGaussianKernel T m n) * (b n) ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ ∑ n ∈ Finset.Icc 1 M,
        (Real.exp (1 / 4) * (1 + 6 * (n : ℝ) / T)) * (b n) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (sum_logGaussianKernel_le T n M hT (Finset.mem_Icc.mp hn).1) (sq_nonneg _)
    _ = _ := by simp_rw [mul_assoc, ← Finset.mul_sum]

/-- The Gaussian Fourier transform, normalized to the frequency convention used here. -/
theorem integral_gaussian_phase (v : ℝ) :
    (∫ u : ℝ, (Real.exp (-u ^ 2) : ℂ) * Complex.exp (I * (v : ℂ) * (u : ℂ))) =
      ((Real.sqrt Real.pi * Real.exp (-(v / 2) ^ 2) : ℝ) : ℂ) := by
  have hpi : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  have hexp (u : ℝ) : (Real.exp (-u ^ 2) : ℂ) = Complex.exp (-(1 : ℂ) * (u : ℂ) ^ 2) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  simp_rw [hexp, mul_comm (Complex.exp (-(1 : ℂ) * _))]
  rw [fourierIntegral_gaussian (by simp : 0 < (1 : ℂ).re), div_one, hpi,
    Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

theorem integrable_gaussian_phase (v : ℝ) :
    Integrable (fun u : ℝ => (Real.exp (-u ^ 2) : ℂ) *
      Complex.exp (I * (v : ℂ) * (u : ℂ))) := by
  have heq (u : ℝ) : (Real.exp (-u ^ 2) : ℂ) * Complex.exp (I * (v : ℂ) * (u : ℂ)) =
      Complex.exp (-(1 : ℂ) * (u : ℂ) ^ 2 + (I * (v : ℂ)) * (u : ℂ) + 0) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [heq]
  exact integrable_cexp_quadratic (by simp : 0 < (1 : ℂ).re) (I * (v : ℂ)) 0

/-- A finite initial segment of a Dirichlet series on the imaginary axis. -/
def logFrequencySum (M : ℕ) (a : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 M, a n * zetaTerm (-y) n

theorem continuous_logFrequencySum (M : ℕ) (a : ℕ → ℂ) :
    Continuous (logFrequencySum M a) := by
  unfold logFrequencySum
  apply continuous_finsetSum
  intro n hn
  simp_rw [zetaTerm_eq_exp _ (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)]
  fun_prop

theorem norm_logFrequencySum_le (M : ℕ) (a : ℕ → ℂ) (y : ℝ) :
    ‖logFrequencySum M a y‖ ≤ ∑ n ∈ Finset.Icc 1 M, ‖a n‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_zetaTerm _ (Finset.mem_Icc.mp hn).1, mul_one]

theorem integrable_gaussian_norm_logFrequencySum (M : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2) := by
  have hgauss : Integrable (fun u : ℝ => Real.exp (-u ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  apply (hgauss.mul_const ((∑ n ∈ Finset.Icc 1 M, ‖a n‖) ^ 2)).mono'
  · exact ((Real.continuous_exp.comp (continuous_id.pow 2).neg).mul
      (((continuous_logFrequencySum M a).comp (continuous_const.mul continuous_id)).norm.pow 2)).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_logFrequencySum_le M a (T * u)) 2

private theorem gaussian_logFrequencySum_gram (M : ℕ) (a : ℕ → ℂ) (T u : ℝ) :
    ((Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (a m * star (a n)) * ((Real.exp (-u ^ 2) : ℂ) *
          Complex.exp (I * ((T * (Real.log n - Real.log m) : ℝ) : ℂ) * (u : ℂ))) := by
  rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj']
  unfold logFrequencySum
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hphase : zetaTerm (-(T * u)) m * star (zetaTerm (-(T * u)) n) =
      Complex.exp (I * ((T * (Real.log n - Real.log m) : ℝ) : ℂ) * (u : ℂ)) := by
    rw [← zetaTerm_neg, neg_neg,
      zetaTerm_eq_exp _ (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1),
      zetaTerm_eq_exp _ (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hphase]
  simp only [starRingEnd_apply]
  ring

/-- Exact finite Gaussian Gram identity for the original logarithmic phases. -/
theorem integral_gaussian_logFrequencySum (M : ℕ) (a : ℕ → ℂ) (T : ℝ) :
    ((∫ u : ℝ, Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2 : ℝ) : ℂ) =
      (Real.sqrt Real.pi : ℂ) * ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (a m * star (a n)) * (logGaussianKernel T m n : ℂ) := by
  rw [← integral_complex_ofReal]
  simp_rw [gaussian_logFrequencySum_gram]
  have hint (m n : ℕ) : Integrable (fun u : ℝ => (a m * star (a n)) *
      ((Real.exp (-u ^ 2) : ℂ) *
        Complex.exp (I * ((T * (Real.log n - Real.log m) : ℝ) : ℂ) * (u : ℂ)))) :=
    (integrable_gaussian_phase _).const_mul _
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ (fun n _ => hint m n))]
  simp_rw [integral_finsetSum _ (fun n _ => hint _ n), integral_const_mul,
    integral_gaussian_phase, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  have hkernel : Real.exp (-(T * (Real.log n - Real.log m) / 2) ^ 2) =
      logGaussianKernel T m n := by
    unfold logGaussianKernel
    congr 1
    ring
  rw [hkernel]
  ring

theorem integral_gaussian_logFrequencySum_le (M : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 4 ≤ T) :
    (∫ u : ℝ, Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2) ≤
      Real.sqrt Real.pi * Real.exp (1 / 4) *
        ∑ n ∈ Finset.Icc 1 M, (1 + 6 * (n : ℝ) / T) * ‖a n‖ ^ 2 := by
  have hnonneg : 0 ≤ ∫ u : ℝ, Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2 :=
    integral_nonneg (fun u => by positivity)
  have hnorm : ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (a m * star (a n)) * (logGaussianKernel T m n : ℂ)‖ ≤
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        logGaussianKernel T m n * ‖a m‖ * ‖a n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro m _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n _
    rw [norm_mul, norm_mul, norm_star, Complex.norm_real,
      Real.norm_of_nonneg (logGaussianKernel_nonneg T m n)]
    exact le_of_eq (by ring)
  calc
    _ = ‖((∫ u : ℝ, Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hnonneg]
    _ = Real.sqrt Real.pi * ‖∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (a m * star (a n)) * (logGaussianKernel T m n : ℂ)‖ := by
      rw [integral_gaussian_logFrequencySum, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ Real.sqrt Real.pi * (Real.exp (1 / 4) *
        ∑ n ∈ Finset.Icc 1 M, (1 + 6 * (n : ℝ) / T) * ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left
        (hnorm.trans (sum_logGaussianKernel_mul_le T M (fun n => ‖a n‖) hT)) (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- A sharp index-weighted mean-square estimate for arbitrary finite initial
segments. The constant is absolute and independent of their length. -/
theorem integral_norm_sq_logFrequencySum_le (M : ℕ) (a : ℕ → ℂ) (T : ℝ) (hT : 4 ≤ T) :
    (∫ y : ℝ in 0..T, ‖logFrequencySum M a y‖ ^ 2) ≤
      Real.sqrt Real.pi * Real.exp (5 / 4) *
        ∑ n ∈ Finset.Icc 1 M, (T + 6 * (n : ℝ)) * ‖a n‖ ^ 2 := by
  have hTpos : 0 < T := by linarith
  have hcont : Continuous (fun u : ℝ => ‖logFrequencySum M a (T * u)‖ ^ 2) :=
    (((continuous_logFrequencySum M a).comp (continuous_const.mul continuous_id)).norm.pow 2)
  have hgcont : Continuous (fun u : ℝ => Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2) :=
    (Real.continuous_exp.comp (continuous_id.pow 2).neg).mul hcont
  have hlocal : (∫ u : ℝ in 0..1, ‖logFrequencySum M a (T * u)‖ ^ 2) ≤
      Real.exp 1 * ∫ u : ℝ, Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2 := by
    calc
      _ ≤ ∫ u : ℝ in 0..1,
          Real.exp 1 * (Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2) := by
        apply intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable 0 1)
          ((continuous_const.mul hgcont).intervalIntegrable 0 1)
        intro u hu
        have hw : 1 ≤ Real.exp 1 * Real.exp (-u ^ 2) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp_iff.mpr
          nlinarith [hu.1, hu.2]
        change ‖logFrequencySum M a (T * u)‖ ^ 2 ≤
          Real.exp 1 * (Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2)
        nlinarith [mul_nonneg (sub_nonneg.mpr hw) (sq_nonneg ‖logFrequencySum M a (T * u)‖)]
      _ = Real.exp 1 * ∫ u : ℝ in Set.Ioc 0 1,
          Real.exp (-u ^ 2) * ‖logFrequencySum M a (T * u)‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num)]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_le_integral (integrable_gaussian_norm_logFrequencySum M a T)
          (Filter.Eventually.of_forall (fun u => by positivity))) (Real.exp_pos _).le
  have hscale : T * (∫ u : ℝ in 0..1, ‖logFrequencySum M a (T * u)‖ ^ 2) =
      ∫ y : ℝ in 0..T, ‖logFrequencySum M a y‖ ^ 2 := by
    simpa only [smul_eq_mul, mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (fun y : ℝ => ‖logFrequencySum M a y‖ ^ 2)
        T (a := 0) (b := 1)
  rw [← hscale]
  calc
    _ ≤ T * (Real.exp 1 * (Real.sqrt Real.pi * Real.exp (1 / 4) *
        ∑ n ∈ Finset.Icc 1 M, (1 + 6 * (n : ℝ) / T) * ‖a n‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (hlocal.trans (mul_le_mul_of_nonneg_left
          (integral_gaussian_logFrequencySum_le M a T hT) (Real.exp_pos _).le)) hTpos.le
    _ = _ := by
      have hexp : Real.exp 1 * Real.exp (1 / 4) = Real.exp (5 / 4) := by
        rw [← Real.exp_add]
        congr 1
        norm_num
      have hsum : T * (∑ n ∈ Finset.Icc 1 M, (1 + 6 * (n : ℝ) / T) * ‖a n‖ ^ 2) =
          ∑ n ∈ Finset.Icc 1 M, (T + 6 * (n : ℝ)) * ‖a n‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        field_simp
      calc
        _ = Real.sqrt Real.pi * (Real.exp 1 * Real.exp (1 / 4)) *
            (T * (∑ n ∈ Finset.Icc 1 M, (1 + 6 * (n : ℝ) / T) * ‖a n‖ ^ 2)) := by ring
        _ = _ := by rw [hexp, hsum]

theorem logFrequencySum_eq_sum_range (M : ℕ) (a : ℕ → ℂ) (y : ℝ) :
    logFrequencySum M a y = ∑ n ∈ Finset.range (M + 1), a n * zetaTerm (-y) n := by
  have hset : insert 0 (Finset.Icc 1 M) = Finset.range (M + 1) := by
    ext n
    simp only [Finset.mem_insert, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [← hset, Finset.sum_insert (by simp)]
  simp only [zetaTerm_zero, mul_zero, zero_add, logFrequencySum]

theorem summable_logFrequencyTerms (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) (y : ℝ) :
    Summable (fun n => a n * zetaTerm (-y) n) := by
  apply ha.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [norm_mul, norm_zetaTerm _ (Nat.pos_of_ne_zero hn), mul_one]

theorem tendsto_logFrequencySum (a : ℕ → ℂ) (ha : Summable (fun n => ‖a n‖)) (y : ℝ) :
    Tendsto (fun M => logFrequencySum M a y) atTop
      (𝓝 (∑' n : ℕ, a n * zetaTerm (-y) n)) := by
  simp_rw [logFrequencySum_eq_sum_range]
  exact (summable_logFrequencyTerms a ha y).hasSum.tendsto_sum_nat.comp
    (tendsto_add_atTop_nat 1)

/-- Absolute convergence permits passage to the complete series without a
coefficient-block loss. The hypotheses concern only the coefficient sums. -/
theorem integral_norm_sq_tsum_logFrequency_le (a : ℕ → ℂ) (T : ℝ) (hT : 4 ≤ T)
    (ha : Summable (fun n => ‖a n‖))
    (hw : Summable (fun n : ℕ => (T + 6 * (n : ℝ)) * ‖a n‖ ^ 2)) :
    (∫ y : ℝ in 0..T, ‖∑' n : ℕ, a n * zetaTerm (-y) n‖ ^ 2) ≤
      Real.sqrt Real.pi * Real.exp (5 / 4) *
        ∑' n : ℕ, (T + 6 * (n : ℝ)) * ‖a n‖ ^ 2 := by
  have hTpos : 0 < T := by linarith
  have hlim : Tendsto (fun M => ∫ y : ℝ in Set.Ioc 0 T, ‖logFrequencySum M a y‖ ^ 2) atTop
      (𝓝 (∫ y : ℝ in Set.Ioc 0 T, ‖∑' n : ℕ, a n * zetaTerm (-y) n‖ ^ 2)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (∑' n : ℕ, ‖a n‖) ^ 2)
    · intro M
      exact ((continuous_logFrequencySum M a).norm.pow 2).aestronglyMeasurable
    · exact integrableOn_const (by simp) (by simp)
    · intro M
      filter_upwards with y
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_logFrequencySum_le M a y).trans
        (ha.sum_le_tsum (Finset.Icc 1 M) (fun n _ => norm_nonneg _))
    · filter_upwards with y
      exact ((tendsto_logFrequencySum a ha y).norm).pow 2
  rw [intervalIntegral.integral_of_le hTpos.le]
  apply le_of_tendsto hlim
  filter_upwards with M
  calc
    _ = ∫ y : ℝ in 0..T, ‖logFrequencySum M a y‖ ^ 2 :=
      (intervalIntegral.integral_of_le hTpos.le).symm
    _ ≤ _ := integral_norm_sq_logFrequencySum_le M a T hT
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hw.sum_le_tsum (Finset.Icc 1 M) (fun n _ => by positivity)) (by positivity)

theorem tsum_nat_rpow_neg_le {p : ℝ} (hp : 1 < p) :
    (∑' n : ℕ, (n : ℝ) ^ (-p)) ≤ 1 + 1 / (p - 1) := by
  apply Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
  intro M
  by_cases hM : M = 0
  · simp [hM]
    positivity
  have hcover : Finset.range M ⊆ {0, 1} ∪ Finset.Ioc 1 M := by
    intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Ioc 1 M) := by
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton, Finset.mem_Ioc]
    omega
  calc
    _ ≤ ∑ n ∈ {0, 1} ∪ Finset.Ioc 1 M, (n : ℝ) ^ (-p) :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover
        (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = 1 + ∑ n ∈ Finset.Ioc 1 M, ((1 : ℝ) / n) ^ p := by
      rw [Finset.sum_union hdisj]
      simp only [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1), Nat.cast_zero,
        Real.zero_rpow (by linarith : -p ≠ 0), Nat.cast_one, Real.one_rpow, zero_add]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      rw [one_div, Real.inv_rpow (Nat.cast_nonneg n), Real.rpow_neg (Nat.cast_nonneg n)]
    _ ≤ _ := add_le_add le_rfl (by simpa using sum_upper_power_ratios_le 1 M (by norm_num) hp)

/-- An explicit summable-power majorant for logarithmic coefficients supplies
both the ordinary and index-weighted square sums. -/
theorem log_sq_mul_rpow_le (n : ℕ) (q ε : ℝ) (hε : 0 < ε) :
    (Real.log n) ^ 2 * (n : ℝ) ^ q ≤ (n : ℝ) ^ (q + 2 * ε) / ε ^ 2 := by
  by_cases hn : n = 0
  · simp [hn]
    positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  calc
    _ ≤ ((n : ℝ) ^ ε / ε) ^ 2 * (n : ℝ) ^ q :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hlog (Real.log_le_rpow_div hnR.le hε) 2) (Real.rpow_nonneg hnR.le _)
    _ = _ := by
      rw [div_pow, ← Real.rpow_mul_natCast hnR.le, div_mul_eq_mul_div, ← Real.rpow_add hnR]
      congr 1
      congr 1
      push_cast
      ring

theorem summable_log_sq_mul_rpow {q ε : ℝ} (hε : 0 < ε) (hq : q + 2 * ε < -1) :
    Summable (fun n : ℕ => (Real.log n) ^ 2 * (n : ℝ) ^ q) := by
  apply ((Real.summable_nat_rpow.mpr hq).div_const (ε ^ 2)).of_nonneg_of_le
  · intro n
    positivity
  · intro n
    exact log_sq_mul_rpow_le n q ε hε

theorem tsum_log_sq_mul_rpow_le {q ε : ℝ} (hε : 0 < ε) (hq : q + 2 * ε < -1) :
    (∑' n : ℕ, (Real.log n) ^ 2 * (n : ℝ) ^ q) ≤
      (1 + 1 / (-(q + 2 * ε) - 1)) / ε ^ 2 := by
  calc
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (q + 2 * ε) / ε ^ 2 :=
      Summable.tsum_le_tsum (fun n => log_sq_mul_rpow_le n q ε hε)
        (summable_log_sq_mul_rpow hε hq) ((Real.summable_nat_rpow.mpr hq).div_const _)
    _ = (∑' n : ℕ, (n : ℝ) ^ (q + 2 * ε)) / ε ^ 2 := tsum_div_const
    _ ≤ _ := div_le_div_of_nonneg_right
      (by simpa only [neg_neg] using tsum_nat_rpow_neg_le (p := -(q + 2 * ε)) (by linarith))
      (sq_nonneg ε)

/-- The actual coefficients of the shifted zeta derivative on a fixed vertical line. -/
def zetaLogCoeff (σ t : ℝ) (n : ℕ) : ℂ :=
  ((Real.log n * (n : ℝ) ^ (-σ) : ℝ) : ℂ) * zetaTerm t n

theorem zetaLogCoeff_phase_eq_term (σ t y : ℝ) (n : ℕ) :
    zetaLogCoeff σ t n * zetaTerm (-y) n =
      LSeries.term (fun m => (Real.log m : ℂ) * zetaTerm t m) ((σ : ℂ) + (y : ℂ) * I) n := by
  by_cases hn : n = 0
  · simp [hn, zetaLogCoeff]
  have hcn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [zetaLogCoeff, mul_assoc, ← zetaTerm_add,
    LSeries.term_of_ne_zero hn, Complex.ofReal_mul,
    Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast,
    zetaTerm_eq_cpow _ hn, zetaTerm_eq_cpow _ hn, mul_div_assoc,
    ← Complex.cpow_sub _ _ hcn, mul_assoc, ← Complex.cpow_add _ _ hcn]
  congr 2
  push_cast
  ring

theorem zetaLogCoeff_eq_term (σ t : ℝ) (n : ℕ) :
    zetaLogCoeff σ t n = LSeries.term (fun m => (Real.log m : ℂ) * zetaTerm t m) (σ : ℂ) n := by
  by_cases hn : n = 0
  · simp [hn, zetaLogCoeff]
  simpa only [neg_zero, zetaTerm_eq_cpow _ hn, Complex.ofReal_zero, zero_mul,
    Complex.cpow_zero, mul_one, add_zero] using zetaLogCoeff_phase_eq_term σ t 0 n

theorem summable_norm_zetaLogCoeff (σ t : ℝ) (hσ : 1 < σ) :
    Summable (fun n => ‖zetaLogCoeff σ t n‖) := by
  have hab : LSeries.abscissaOfAbsConv (zetaTerm t) ≤ 1 :=
    LSeries.abscissaOfAbsConv_le_of_le_const ⟨1, fun n hn =>
      (norm_zetaTerm t (Nat.pos_of_ne_zero hn)).le⟩
  have hs : LSeries.abscissaOfAbsConv (zetaTerm t) < (σ : ℂ).re :=
    hab.trans_lt (by exact_mod_cast hσ)
  have hlog : LSeries.logMul (zetaTerm t) =
      (fun n : ℕ => (Real.log n : ℂ) * zetaTerm t n) := by
    funext n
    rw [LSeries.logMul, ← Complex.natCast_log]
  have hS := LSeriesSummable_logMul_of_lt_re hs
  rw [hlog] at hS
  simp_rw [zetaLogCoeff_eq_term]
  exact hS.norm

theorem tsum_zetaLogCoeff_phase (σ t y : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, zetaLogCoeff σ t n * zetaTerm (-y) n) =
      -deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) := by
  simp_rw [zetaLogCoeff_phase_eq_term]
  rw [← LSeries, LSeries_logZetaTerm t (by simpa)]
  congr 2
  push_cast
  ring

theorem norm_zetaLogCoeff_sq (σ t : ℝ) (n : ℕ) :
    ‖zetaLogCoeff σ t n‖ ^ 2 = (Real.log n) ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  rw [zetaLogCoeff, norm_logPhaseCoeff, mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  congr 1
  congr 1
  push_cast
  ring

theorem index_mul_norm_zetaLogCoeff_sq (σ t : ℝ) (n : ℕ) :
    (n : ℝ) * ‖zetaLogCoeff σ t n‖ ^ 2 =
      (Real.log n) ^ 2 * (n : ℝ) ^ (1 - 2 * σ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hpow : (n : ℝ) * (n : ℝ) ^ (-2 * σ) = (n : ℝ) ^ (1 - 2 * σ) := by
    nth_rw 1 [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hnR]
    congr 1
    ring
  rw [norm_zetaLogCoeff_sq]
  calc
    _ = (Real.log n) ^ 2 * ((n : ℝ) * (n : ℝ) ^ (-2 * σ)) := by ring
    _ = _ := by rw [hpow]

theorem summable_norm_zetaLogCoeff_sq (σ t : ℝ) (hσ : 1 < σ) :
    Summable (fun n => ‖zetaLogCoeff σ t n‖ ^ 2) := by
  simp_rw [norm_zetaLogCoeff_sq]
  exact summable_log_sq_mul_rpow (ε := 1 / 4) (by norm_num) (by linarith)

theorem summable_index_norm_zetaLogCoeff_sq (σ t : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n : ℝ) * ‖zetaLogCoeff σ t n‖ ^ 2) := by
  simp_rw [index_mul_norm_zetaLogCoeff_sq]
  exact summable_log_sq_mul_rpow (ε := (σ - 1) / 2) (by linarith) (by linarith)

theorem tsum_norm_zetaLogCoeff_sq_le (σ t : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, ‖zetaLogCoeff σ t n‖ ^ 2) ≤ 48 := by
  have hbase : (∑' n : ℕ, (Real.log n) ^ 2 * (n : ℝ) ^ (-2 : ℝ)) ≤ 48 := by
    convert tsum_log_sq_mul_rpow_le (q := -2) (ε := 1 / 4) (by norm_num) (by norm_num) using 1
    norm_num
  apply le_trans _ hbase
  apply Summable.tsum_le_tsum _ (summable_norm_zetaLogCoeff_sq σ t hσ)
    (summable_log_sq_mul_rpow (q := -2) (ε := 1 / 4) (by norm_num) (by norm_num))
  intro n
  rw [norm_zetaLogCoeff_sq]
  by_cases hn : n = 0
  · simp [hn]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    (by linarith)

theorem tsum_index_norm_zetaLogCoeff_sq_le (σ t : ℝ) (hσ : 1 < σ) (hσ₂ : σ ≤ 2) :
    (∑' n : ℕ, (n : ℝ) * ‖zetaLogCoeff σ t n‖ ^ 2) ≤ 8 / (σ - 1) ^ 3 := by
  simp_rw [index_mul_norm_zetaLogCoeff_sq]
  have h := tsum_log_sq_mul_rpow_le (q := 1 - 2 * σ) (ε := (σ - 1) / 2)
    (by linarith) (by linarith)
  apply h.trans
  have hσpos : 0 < σ - 1 := by linarith
  have hden : -(1 - 2 * σ + 2 * ((σ - 1) / 2)) - 1 = σ - 1 := by ring
  rw [hden]
  field_simp
  nlinarith [sq_nonneg (σ - 1), mul_nonneg (sq_nonneg (σ - 1)) (sub_nonneg.mpr hσ₂)]

/-- The sharp global mean square for the actual shifted zeta derivative. No
analytic mean-value or maximum bound is assumed. -/
theorem integral_zeta_deriv_sq_le (σ t T : ℝ) (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hT : 4 ≤ T) :
    (∫ y : ℝ in 0..T, ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I)‖ ^ 2) ≤
      48 * Real.sqrt Real.pi * Real.exp (5 / 4) * (T + 1 / (σ - 1) ^ 3) := by
  have hTpos : 0 < T := by linarith
  have hsum := summable_norm_zetaLogCoeff_sq σ t hσ
  have hindex := summable_index_norm_zetaLogCoeff_sq σ t hσ
  have hw : Summable (fun n : ℕ => (T + 6 * (n : ℝ)) * ‖zetaLogCoeff σ t n‖ ^ 2) := by
    convert (hsum.mul_left T).add (hindex.mul_left 6) using 1
    funext n
    ring
  have h := integral_norm_sq_tsum_logFrequency_le (zetaLogCoeff σ t) T hT
    (summable_norm_zetaLogCoeff σ t hσ) hw
  simp_rw [tsum_zetaLogCoeff_phase σ t _ hσ, norm_neg] at h
  have hweight : (∑' n : ℕ, (T + 6 * (n : ℝ)) * ‖zetaLogCoeff σ t n‖ ^ 2) ≤
      48 * T + 48 / (σ - 1) ^ 3 := by
    simp_rw [add_mul, mul_assoc]
    rw [Summable.tsum_add (hsum.mul_left T) (hindex.mul_left 6), tsum_mul_left, tsum_mul_left]
    calc
      _ ≤ T * 48 + 6 * (8 / (σ - 1) ^ 3) :=
        add_le_add (mul_le_mul_of_nonneg_left (tsum_norm_zetaLogCoeff_sq_le σ t hσ) hTpos.le)
          (mul_le_mul_of_nonneg_left (tsum_index_norm_zetaLogCoeff_sq_le σ t hσ hσ₂) (by norm_num))
      _ = _ := by ring
  calc
    _ ≤ _ := h
    _ ≤ Real.sqrt Real.pi * Real.exp (5 / 4) * (48 * T + 48 / (σ - 1) ^ 3) :=
      mul_le_mul_of_nonneg_left hweight (by positivity)
    _ = _ := by ring

theorem continuous_shifted_zeta_deriv (σ t : ℝ) (hσ : 1 < σ) :
    Continuous (fun y : ℝ => deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hz : (σ : ℂ) + ((y - t : ℝ) : ℂ) * I ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
      Complex.one_re] at hre
    linarith
  have harg : ContinuousAt (fun u : ℝ => (σ : ℂ) + ((u - t : ℝ) : ℂ) * I) y := by fun_prop
  exact ContinuousAt.comp (f := fun u : ℝ => (σ : ℂ) + ((u - t : ℝ) : ℂ) * I)
    (g := deriv riemannZeta) (analyticOn_riemannZeta _ hz).deriv.continuousAt harg

theorem integral_zeta_deriv_sq_shift_le (σ t a b : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hab : 4 ≤ b - a) :
    (∫ y : ℝ in a..b, ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I)‖ ^ 2) ≤
      48 * Real.sqrt Real.pi * Real.exp (5 / 4) * ((b - a) + 1 / (σ - 1) ^ 3) := by
  have hshift := intervalIntegral.integral_comp_add_right
    (fun y : ℝ => ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I)‖ ^ 2)
    a (a := 0) (b := b - a)
  simp only [zero_add, sub_add_cancel] at hshift
  rw [← hshift]
  have heq (u : ℝ) : u + a - t = u - (t - a) := by ring
  simp_rw [heq]
  exact integral_zeta_deriv_sq_le σ (t - a) (b - a) hσ hσ₂ hab

theorem integral_zeta_deriv_quotient_interval_le (σ t a b R : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hab : 4 ≤ b - a) (hR : 0 < R)
    (hgap : ∀ y ∈ Set.Icc a b, R ≤ |y|) :
    (∫ y : ℝ in a..b,
      ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      48 * Real.sqrt Real.pi * Real.exp (5 / 4) * ((b - a) + 1 / (σ - 1) ^ 3) / R ^ 2 := by
  have hab' : a ≤ b := by linarith
  have hraw := (continuous_shifted_zeta_deriv σ t hσ).norm.pow 2
  have hquot : Continuous (fun y : ℝ => deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)) :=
    (continuous_shifted_zeta_deriv σ t hσ).div (by fun_prop)
      (fun y => Complex.ne_zero_of_re_pos (by simp; linarith))
  calc
    _ ≤ ∫ y : ℝ in a..b,
        ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I)‖ ^ 2 / R ^ 2 := by
      apply intervalIntegral.integral_mono_on hab'
        ((hquot.norm.pow 2).intervalIntegrable a b) ((hraw.div_const (R ^ 2)).intervalIntegrable a b)
      intro y hy
      rw [norm_div, div_pow]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hR)
      have hgap₂ := pow_le_pow_left₀ hR.le (hgap y hy) 2
      rw [sq_abs] at hgap₂
      have hden : ‖(σ : ℂ) + (y : ℂ) * I‖ ^ 2 = σ ^ 2 + y ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp [pow_two]
      rw [hden]
      nlinarith [sq_nonneg σ]
    _ = (∫ y : ℝ in a..b,
        ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I)‖ ^ 2) / R ^ 2 :=
      intervalIntegral.integral_div _ _
    _ ≤ _ := div_le_div_of_nonneg_right
      (integral_zeta_deriv_sq_shift_le σ t a b hσ hσ₂ hab) (sq_nonneg R)

/-- The complete positive far-frequency tail, now for the full derivative rather
than a single coefficient block. -/
theorem zeta_deriv_positive_far_tail (σ t T : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hT : 4 ≤ T) :
    IntegrableOn (fun y : ℝ => ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) (Set.Ioi T) ∧
    (∫ y in Set.Ioi T, ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      96 * Real.sqrt Real.pi * Real.exp (5 / 4) * (T + 1 / (σ - 1) ^ 3) / T ^ 2 := by
  have hquot : Continuous (fun y : ℝ => deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)) :=
    (continuous_shifted_zeta_deriv σ t hσ).div (by fun_prop)
      (fun y => Complex.ne_zero_of_re_pos (by simp; linarith))
  have h := dyadic_frequency_tail (hquot.norm.pow 2) (fun _ => sq_nonneg _)
    (K := 1 / (σ - 1) ^ 3) (S := 48 * Real.sqrt Real.pi * Real.exp (5 / 4))
    (by positivity) (by positivity) (by linarith : 0 < T) (fun U hU => ?_)
  · refine ⟨h.1, h.2.trans_eq ?_⟩
    ring
  · have hshell := integral_zeta_deriv_quotient_interval_le σ t U (2 * U) U hσ hσ₂
      (by linarith) (by linarith) (fun y hy => hy.1.trans (le_abs_self y))
    convert hshell using 1
    ring

theorem zeta_deriv_negative_far_tail (σ t T : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hT : 4 ≤ T) :
    IntegrableOn (fun y : ℝ => ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) (Set.Iio (-T)) ∧
    (∫ y in Set.Iio (-T), ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      96 * Real.sqrt Real.pi * Real.exp (5 / 4) * (T + 1 / (σ - 1) ^ 3) / T ^ 2 := by
  let F : ℝ → ℝ := fun y => ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2
  have hquot : Continuous (fun y : ℝ => deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)) :=
    (continuous_shifted_zeta_deriv σ t hσ).div (by fun_prop)
      (fun y => Complex.ne_zero_of_re_pos (by simp; linarith))
  have hshell (U : ℝ) (hU : T ≤ U) :
      (∫ y : ℝ in U..2 * U, F (-y)) ≤
        (U + 1 / (σ - 1) ^ 3) * (48 * Real.sqrt Real.pi * Real.exp (5 / 4)) / U ^ 2 := by
    rw [intervalIntegral.integral_comp_neg]
    have h := integral_zeta_deriv_quotient_interval_le σ t (-(2 * U)) (-U) U hσ hσ₂
      (by linarith) (by linarith)
      (fun y hy => (by linarith [hy.2] : U ≤ -y).trans (neg_le_abs y))
    convert h using 1
    ring
  have h := dyadic_frequency_tail ((hquot.norm.pow 2).comp continuous_neg)
    (fun _ => sq_nonneg _) (by positivity) (by positivity) (by linarith : 0 < T) hshell
  constructor
  · have hint : IntegrableOn (fun y => F (-y)) (Set.Ioi (-(-T))) := by
      simpa only [neg_neg] using h.1
    simpa only [neg_neg] using hint.comp_neg_Iio
  · change (∫ y in Set.Iio (-T), F y) ≤ _
    rw [← integral_Iic_eq_integral_Iio, ← integral_comp_neg_Ioi T F]
    exact h.2.trans_eq (by ring)

/-- Sharp two-sided full-series far tail, uniform in the height twist. This is
the coefficient-assembly step missing from the individual-block estimates. -/
theorem zeta_deriv_far_tail (σ t T : ℝ)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (hT : 4 ≤ T) :
    IntegrableOn (fun y : ℝ => ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
      ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) {y : ℝ | T < |y|} ∧
    (∫ y in {y : ℝ | T < |y|},
      ‖deriv riemannZeta ((σ : ℂ) + ((y - t : ℝ) : ℂ) * I) /
        ((σ : ℂ) + (y : ℂ) * I)‖ ^ 2) ≤
      192 * Real.sqrt Real.pi * Real.exp (5 / 4) * (1 / T + 1 / ((σ - 1) ^ 3 * T ^ 2)) := by
  have hpos := zeta_deriv_positive_far_tail σ t T hσ hσ₂ hT
  have hneg := zeta_deriv_negative_far_tail σ t T hσ hσ₂ hT
  have hset : {y : ℝ | T < |y|} = Set.Iio (-T) ∪ Set.Ioi T := by
    ext y
    change T < |y| ↔ y < -T ∨ T < y
    rw [lt_abs]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (by linarith)
    · rintro (h | h)
      · exact Or.inr (by linarith)
      · exact Or.inl h
  have hdisj : Disjoint (Set.Iio (-T)) (Set.Ioi T) := by
    apply Set.disjoint_left.mpr
    intro y hy₁ hy₂
    change y < -T at hy₁
    change T < y at hy₂
    linarith
  rw [hset]
  refine ⟨hneg.1.union hpos.1, ?_⟩
  rw [setIntegral_union hdisj measurableSet_Ioi hneg.1 hpos.1]
  calc
    _ ≤ _ := add_le_add hneg.2 hpos.2
    _ = _ := by
      have hTpos : 0 < T := by linarith
      field_simp
      ring

end
end DongWangWangZhang2026
