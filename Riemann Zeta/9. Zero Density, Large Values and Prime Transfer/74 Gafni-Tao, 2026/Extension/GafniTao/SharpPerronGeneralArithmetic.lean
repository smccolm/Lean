import GafniTao.SharpPerronEndpointUniform
import GafniTao.SharpPerronArithmetic

/-!
# Endpoint-uniform arithmetic Perron estimate

The half-integral argument is upgraded to every real endpoint by separating
the at-most-two integers at distance less than one.  Those transition terms
use the direct logarithmic-height kernel bound; every remaining near-diagonal
term is compared to the already proved half-integral harmonic kernel.
-/

open scoped BigOperators

namespace GafniTao

private noncomputable def sharpPerronTransitionSet (x : ℝ) : Finset ℕ :=
  (Finset.range (2 * ⌊x⌋₊ + 2)).filter (fun n => |x - (n : ℝ)| < 1)

private noncomputable def sharpPerronGeneralHarmonicSet (x : ℝ) : Finset ℕ :=
  (Finset.range (2 * ⌊x⌋₊ + 2)).filter (fun n => 1 ≤ |x - (n : ℝ)|)

private theorem transitionSet_subset_pair {x : ℝ} (hx : 0 ≤ x) :
    sharpPerronTransitionSet x ⊆ {⌊x⌋₊, ⌊x⌋₊ + 1} := by
  intro n hn
  have hnear := (Finset.mem_filter.mp hn).2
  rw [abs_lt] at hnear
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx
  have hfloorUpper : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hnLower : ⌊x⌋₊ ≤ n := by
    by_contra h
    have hnlt : n < ⌊x⌋₊ := Nat.lt_of_not_ge h
    have hnSucc : n + 1 ≤ ⌊x⌋₊ := Nat.add_one_le_iff.mpr hnlt
    have hnreal : (n : ℝ) + 1 ≤ ((⌊x⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast hnSucc
    linarith
  have hnUpper : n ≤ ⌊x⌋₊ + 1 := by
    by_contra h
    have hnNat : ⌊x⌋₊ + 2 ≤ n := by omega
    have hnreal : ((⌊x⌋₊ : ℕ) : ℝ) + 2 ≤ (n : ℝ) := by
      exact_mod_cast hnNat
    linarith
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem transitionSet_card_le_two {x : ℝ} (hx : 0 ≤ x) :
    (sharpPerronTransitionSet x).card ≤ 2 := by
  calc
    _ ≤ ({⌊x⌋₊, ⌊x⌋₊ + 1} : Finset ℕ).card :=
      Finset.card_le_card (transitionSet_subset_pair hx)
    _ ≤ 2 := by simp

private theorem general_distance_to_halfPoint
    {x : ℝ} {n : ℕ} (hx : 0 ≤ x)
    (hfar : 1 ≤ |x - (n : ℝ)|) :
    1 / |x - (n : ℝ)| ≤
      2 * (1 / |sharpPerronHalfPoint x - (n : ℝ)|) := by
  have hhalfDist : |sharpPerronHalfPoint x - x| ≤ (1 / 2 : ℝ) := by
    rw [sharpPerronHalfPoint]
    have hfloor := Int.floor_le x
    have hupper := Int.lt_floor_add_one x
    rw [abs_le]
    constructor <;> linarith [Nat.floor_le hx, Nat.lt_floor_add_one x]
  have htriangle : |sharpPerronHalfPoint x - (n : ℝ)| ≤
      |sharpPerronHalfPoint x - x| + |x - (n : ℝ)| := by
    calc
      |sharpPerronHalfPoint x - (n : ℝ)| =
          |(sharpPerronHalfPoint x - x) + (x - (n : ℝ))| := by ring_nf
      _ ≤ |sharpPerronHalfPoint x - x| + |x - (n : ℝ)| := abs_add_le _ _
  have hcompare : |sharpPerronHalfPoint x - (n : ℝ)| ≤
      2 * |x - (n : ℝ)| := by
    calc
      _ ≤ |sharpPerronHalfPoint x - x| + |x - (n : ℝ)| := htriangle
      _ ≤ (1 / 2 : ℝ) + |x - (n : ℝ)| := by gcongr
      _ ≤ 2 * |x - (n : ℝ)| := by linarith
  have hxden : 0 < |x - (n : ℝ)| := lt_of_lt_of_le zero_lt_one hfar
  have hhalfden : 0 < |sharpPerronHalfPoint x - (n : ℝ)| :=
    abs_pos.mpr (by
      intro heq
      have hh := half_le_abs_sharpPerronHalfPoint_sub_natCast x n
      rw [heq, abs_zero] at hh
      norm_num at hh)
  rw [show 2 * (1 / |sharpPerronHalfPoint x - (n : ℝ)|) =
      2 / |sharpPerronHalfPoint x - (n : ℝ)| by ring]
  exact (div_le_div_iff₀ hxden hhalfden).2 (by simpa using hcompare)

private theorem sum_generalHarmonicSet_le {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ sharpPerronGeneralHarmonicSet x,
      1 / |x - (n : ℝ)|) ≤
        8 * (harmonic (⌊x⌋₊ + 1) : ℝ) := by
  calc
    _ ≤ ∑ n ∈ sharpPerronGeneralHarmonicSet x,
        2 * (1 / |sharpPerronHalfPoint x - (n : ℝ)|) := by
      apply Finset.sum_le_sum
      intro n hn
      exact general_distance_to_halfPoint hx (Finset.mem_filter.mp hn).2
    _ ≤ ∑ n ∈ Finset.range (2 * ⌊x⌋₊ + 2),
        2 * (1 / |sharpPerronHalfPoint x - (n : ℝ)|) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro n _ _
        positivity
    _ = 2 * (∑ n ∈ Finset.range (2 * ⌊x⌋₊ + 2),
        1 / |sharpPerronHalfPoint x - (n : ℝ)|) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (4 * (harmonic (⌊x⌋₊ + 1) : ℝ)) := by
      gcongr
      simpa only [sharpPerronHalfPoint] using
        sum_range_inv_abs_nat_add_half_le ⌊x⌋₊
    _ = 8 * (harmonic (⌊x⌋₊ + 1) : ℝ) := by ring

private theorem norm_vonMangoldt_general_cutoffError_le_additive
    {c T x : ℝ} {n : ℕ} (hc : 0 < c) (hT : 0 < T)
    (hx : 0 < x) (hn : 1 ≤ n) (hne : x ≠ (n : ℝ)) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel c T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronCutoff x n‖ ≤
      (ArithmeticFunction.vonMangoldt n * (x / (n : ℝ)) ^ c /
        (Real.pi * T)) *
        (max x (n : ℝ) / |x - (n : ℝ)|) := by
  rcases lt_or_gt_of_ne hne with hxn | hnx
  · rw [max_eq_right hxn.le, abs_of_nonpos (sub_nonpos.mpr hxn.le)]
    simpa only [neg_sub] using
      norm_vonMangoldt_cutoffError_le_additive_of_lt_natCast
        hc hT hx hn hxn
  · rw [max_eq_left hnx.le, abs_of_nonneg (sub_nonneg.mpr hnx.le)]
    exact norm_vonMangoldt_cutoffError_le_additive_of_natCast_lt
      hc hT hx hn hnx

private theorem norm_vonMangoldt_general_cutoffError_le_near
    {T x : ℝ} {n : ℕ} (hx : 2 ≤ x) (hT : 0 < T) (hn : 1 ≤ n)
    (hnLower : x / 2 < (n : ℝ)) (hnUpper : (n : ℝ) < 2 * x)
    (hfar : 1 ≤ |x - (n : ℝ)|) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel (sharpPerronAbscissa x) T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronCutoff x n‖ ≤
      (sharpPerronRatioBound * Real.log (2 * x) * (2 * x) /
          (Real.pi * T)) * (1 / |x - (n : ℝ)|) := by
  have hxPos : 0 < x := by linarith
  have hnPos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hne : x ≠ (n : ℝ) := by
    intro heq
    rw [heq, sub_self, abs_zero] at hfar
    norm_num at hfar
  have hcPos := sharpPerronAbscissa_pos (y := x) (by linarith)
  have hratio0 : 0 ≤ x / (n : ℝ) := (div_pos hxPos hnPos).le
  have hratio2 : x / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hnPos]
    linarith
  have hpow := rpow_sharpPerronAbscissa_le_ratioBound hx hratio0 hratio2
  have hLambda : ArithmeticFunction.vonMangoldt n ≤ Real.log (2 * x) :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hnPos hnUpper.le)
  have hmax : max x (n : ℝ) ≤ 2 * x := max_le (by linarith) hnUpper.le
  have hden : 0 < |x - (n : ℝ)| := lt_of_lt_of_le zero_lt_one hfar
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  refine (norm_vonMangoldt_general_cutoffError_le_additive
    hcPos hT hxPos hn hne).trans ?_
  have hnum : ArithmeticFunction.vonMangoldt n *
      (x / (n : ℝ)) ^ sharpPerronAbscissa x ≤
        sharpPerronRatioBound * Real.log (2 * x) := by
    calc
      _ ≤ Real.log (2 * x) * sharpPerronRatioBound :=
        mul_le_mul hLambda hpow (Real.rpow_nonneg hratio0 _)
          (Real.log_nonneg (by linarith))
      _ = _ := by ring
  calc
    _ ≤ (sharpPerronRatioBound * Real.log (2 * x) /
          (Real.pi * T)) * ((2 * x) / |x - (n : ℝ)|) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right hnum hpiT.le)
        (div_le_div_of_nonneg_right hmax hden.le)
        (div_nonneg (hxPos.le.trans (le_max_left _ _)) hden.le)
        (div_nonneg
          (mul_nonneg (le_trans (by norm_num) one_le_sharpPerronRatioBound)
            (Real.log_nonneg (by linarith))) hpiT.le)
    _ = (sharpPerronRatioBound * Real.log (2 * x) * (2 * x) /
          (Real.pi * T)) * (1 / |x - (n : ℝ)|) := by ring

private theorem norm_vonMangoldt_general_cutoffError_le_far
    {T x : ℝ} {n : ℕ} (hx : 2 ≤ x) (hT : 0 < T) (hn : 1 ≤ n)
    (hfar : (n : ℝ) ≤ x / 2 ∨ 2 * x ≤ (n : ℝ)) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronKernel (sharpPerronAbscissa x) T x n -
        (ArithmeticFunction.vonMangoldt n : ℂ) *
          sharpPerronCutoff x n‖ ≤
      (2 * x ^ sharpPerronAbscissa x / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          (n : ℝ) ^ sharpPerronAbscissa x) := by
  have hxPos : 0 < x := by linarith
  have hnPos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)
  have hne : x ≠ (n : ℝ) := by rcases hfar with h | h <;> linarith
  have hcPos := sharpPerronAbscissa_pos (y := x) (by linarith)
  have hfactor := max_div_abs_sub_le_two_of_far hxPos hnPos hfar
  refine (norm_vonMangoldt_general_cutoffError_le_additive
    hcPos hT hxPos hn hne).trans ?_
  calc
    _ ≤ (ArithmeticFunction.vonMangoldt n *
          (x / (n : ℝ)) ^ sharpPerronAbscissa x /
          (Real.pi * T)) * 2 := by
      exact mul_le_mul_of_nonneg_left hfactor
        (div_nonneg
          (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg (div_pos hxPos hnPos).le _))
          (mul_nonneg Real.pi_pos.le hT.le))
    _ = (2 * x ^ sharpPerronAbscissa x / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          (n : ℝ) ^ sharpPerronAbscissa x) := by
      rw [Real.div_rpow hxPos.le hnPos.le]
      ring

private noncomputable def sharpPerronTransitionWeight (x : ℝ) (n : ℕ) : ℝ :=
  if n ∈ sharpPerronTransitionSet x then 1 else 0

private noncomputable def sharpPerronGeneralHarmonicWeight (x : ℝ) (n : ℕ) : ℝ :=
  if n ∈ sharpPerronGeneralHarmonicSet x then
    1 / |x - (n : ℝ)| else 0

private theorem summable_transitionWeight (x : ℝ) :
    Summable (sharpPerronTransitionWeight x) := by
  apply summable_of_ne_finset_zero (s := sharpPerronTransitionSet x)
  intro n hn
  simp [sharpPerronTransitionWeight, hn]

private theorem summable_generalHarmonicWeight (x : ℝ) :
    Summable (sharpPerronGeneralHarmonicWeight x) := by
  apply summable_of_ne_finset_zero (s := sharpPerronGeneralHarmonicSet x)
  intro n hn
  simp [sharpPerronGeneralHarmonicWeight, hn]

private theorem tsum_transitionWeight_le_two {x : ℝ} (hx : 0 ≤ x) :
    (∑' n : ℕ, sharpPerronTransitionWeight x n) ≤ 2 := by
  rw [tsum_eq_sum (s := sharpPerronTransitionSet x)]
  · calc
      (∑ n ∈ sharpPerronTransitionSet x,
          sharpPerronTransitionWeight x n) =
          ∑ _n ∈ sharpPerronTransitionSet x, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        simp [sharpPerronTransitionWeight, hn]
      _ = ((sharpPerronTransitionSet x).card : ℝ) := by simp
      _ ≤ 2 := by exact_mod_cast transitionSet_card_le_two hx
  · intro n hn
    simp [sharpPerronTransitionWeight, hn]

private theorem tsum_generalHarmonicWeight_le {x : ℝ} (hx : 0 ≤ x) :
    (∑' n : ℕ, sharpPerronGeneralHarmonicWeight x n) ≤
      8 * (harmonic (⌊x⌋₊ + 1) : ℝ) := by
  rw [tsum_eq_sum (s := sharpPerronGeneralHarmonicSet x)]
  · simpa [sharpPerronGeneralHarmonicWeight] using sum_generalHarmonicSet_le hx
  · intro n hn
    simp [sharpPerronGeneralHarmonicWeight, hn]

private theorem resonant_mem_range {x : ℝ} {n : ℕ}
    (hn : (n : ℝ) < 2 * x) : n ∈ Finset.range (2 * ⌊x⌋₊ + 2) := by
  rw [Finset.mem_range]
  have hfloorUpper : x < ((⌊x⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one x
  have hreal : (n : ℝ) < ((2 * ⌊x⌋₊ + 2 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hreal

private theorem transitionWeight_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ sharpPerronTransitionWeight x n := by
  simp only [sharpPerronTransitionWeight]
  split_ifs <;> norm_num

private theorem generalHarmonicWeight_nonneg (x : ℝ) (n : ℕ) :
    0 ≤ sharpPerronGeneralHarmonicWeight x n := by
  simp only [sharpPerronGeneralHarmonicWeight]
  split_ifs <;> positivity

/-- Complete arbitrary-endpoint arithmetic estimate before absorbing the
explicit harmonic and Dirichlet-series factors into logarithms. -/
theorem norm_optimized_general_Perron_sub_psi_le_arithmetic
    {T x : ℝ} (hx : 2 ≤ x) (hT : 0 < T) :
    ‖(1 / (2 * Real.pi) : ℂ) *
          (∫ t in (-T)..T,
            (-deriv riemannZeta
                ((sharpPerronAbscissa x : ℂ) + (t : ℂ) * Complex.I) /
                riemannZeta
                  ((sharpPerronAbscissa x : ℂ) + (t : ℂ) * Complex.I)) *
              (x : ℂ) ^
                ((sharpPerronAbscissa x : ℂ) + (t : ℂ) * Complex.I) /
                ((sharpPerronAbscissa x : ℂ) + (t : ℂ) * Complex.I)) -
        (Chebyshev.psi x : ℂ)‖ ≤
      (Real.log (2 * x) *
          (sharpPerronRatioBound * (2 / Real.pi) *
            (Real.log (sharpPerronAbscissa x + T) -
              Real.log (sharpPerronAbscissa x)) + 1)) * 2 +
      (sharpPerronRatioBound * Real.log (2 * x) * (2 * x) /
          (Real.pi * T)) *
        (8 * (harmonic (⌊x⌋₊ + 1) : ℝ)) +
      (2 * x ^ sharpPerronAbscissa x / (Real.pi * T)) *
        (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
          (n : ℝ) ^ sharpPerronAbscissa x) := by
  let c := sharpPerronAbscissa x
  let K := Real.log (2 * x) *
    (sharpPerronRatioBound * (2 / Real.pi) *
      (Real.log (c + T) - Real.log c) + 1)
  let A := sharpPerronRatioBound * Real.log (2 * x) * (2 * x) /
    (Real.pi * T)
  let B := 2 * x ^ c / (Real.pi * T)
  let d : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c
  let e : ℕ → ℝ := fun n =>
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronKernel c T x n -
      (ArithmeticFunction.vonMangoldt n : ℂ) * sharpPerronCutoff x n‖
  let M : ℕ → ℝ := fun n => K * sharpPerronTransitionWeight x n +
    A * sharpPerronGeneralHarmonicWeight x n + B * d n
  have hxPos : 0 < x := by linarith
  have hcOne : 1 < c := one_lt_sharpPerronAbscissa (by linarith)
  have hcPos : 0 < c := zero_lt_one.trans hcOne
  have hK0 : 0 ≤ K := by
    dsimp [K]
    have hlogdiff : 0 ≤ Real.log (c + T) - Real.log c := by
      rw [sub_nonneg, Real.log_le_log_iff hcPos (by linarith)]
      linarith
    exact mul_nonneg (Real.log_nonneg (by linarith))
      (add_nonneg (mul_nonneg
        (mul_nonneg (le_trans (by norm_num) one_le_sharpPerronRatioBound)
          (by positivity)) hlogdiff)
        (by norm_num))
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact div_nonneg
      (mul_nonneg (mul_nonneg
        (le_trans (by norm_num) one_le_sharpPerronRatioBound)
        (Real.log_nonneg (by linarith))) (by positivity))
      (mul_nonneg Real.pi_pos.le hT.le)
  have hB0 : 0 ≤ B := by
    dsimp [B]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg hxPos.le _))
      (mul_nonneg Real.pi_pos.le hT.le)
  have hd0 : ∀ n, 0 ≤ d n := fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have heSummable : Summable e := by
    exact summable_norm_vonMangoldt_sharpPerron_cutoffError hcOne hxPos
  have hdSummable : Summable d := summable_vonMangoldt_div_nat_rpow hcOne
  have hMSummable : Summable M :=
    (((summable_transitionWeight x).mul_left K).add
      ((summable_generalHarmonicWeight x).mul_left A)).add
      (hdSummable.mul_left B)
  have hpoint : ∀ n, e n ≤ M n := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      dsimp [e, M, d]
      simp
      exact add_nonneg (mul_nonneg hK0 (transitionWeight_nonneg x 0))
        (mul_nonneg hA0 (generalHarmonicWeight_nonneg x 0))
    · have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      by_cases hres : x / 2 < (n : ℝ) ∧ (n : ℝ) < 2 * x
      · by_cases hnear : |x - (n : ℝ)| < 1
        · have hmemRange := resonant_mem_range hres.2
          have hmem : n ∈ sharpPerronTransitionSet x :=
            Finset.mem_filter.mpr ⟨hmemRange, hnear⟩
          have hterm := norm_vonMangoldt_cutoffError_le_transition
            hx hT.le hn hnear
          have hLambda := ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn)) hres.2.le)
          have htermK : e n ≤ K := by
            dsimp [e, K, c] at hterm ⊢
            exact hterm.trans (mul_le_mul_of_nonneg_right hLambda (by
              have hlogdiff : 0 ≤
                  Real.log (sharpPerronAbscissa x + T) -
                    Real.log (sharpPerronAbscissa x) := by
                rw [sub_nonneg, Real.log_le_log_iff
                  (sharpPerronAbscissa_pos (y := x) (by linarith)) (by positivity)]
                linarith
              exact add_nonneg
                (mul_nonneg
                  (mul_nonneg
                    (le_trans (by norm_num) one_le_sharpPerronRatioBound)
                    (div_nonneg (by norm_num) Real.pi_pos.le))
                  hlogdiff) (by norm_num)))
          dsimp [M]
          rw [sharpPerronTransitionWeight, if_pos hmem]
          have hrest : 0 ≤
              A * sharpPerronGeneralHarmonicWeight x n + B * d n :=
            add_nonneg (mul_nonneg hA0 (generalHarmonicWeight_nonneg x n))
              (mul_nonneg hB0 (hd0 n))
          exact htermK.trans (by
            simpa only [mul_one, add_assoc] using (le_add_of_nonneg_right hrest :
              K ≤ K + (A * sharpPerronGeneralHarmonicWeight x n + B * d n)))
        · have hfarDist : 1 ≤ |x - (n : ℝ)| := le_of_not_gt hnear
          have hmemRange := resonant_mem_range hres.2
          have hmem : n ∈ sharpPerronGeneralHarmonicSet x :=
            Finset.mem_filter.mpr ⟨hmemRange, hfarDist⟩
          have hterm := norm_vonMangoldt_general_cutoffError_le_near
            hx hT hn hres.1 hres.2 hfarDist
          dsimp [M]
          rw [sharpPerronGeneralHarmonicWeight, if_pos hmem]
          exact hterm.trans (le_add_of_nonneg_left
            (mul_nonneg hK0 (transitionWeight_nonneg x n))) |>.trans
            (le_add_of_nonneg_right (mul_nonneg hB0 (hd0 n)))
      · have hfar : (n : ℝ) ≤ x / 2 ∨ 2 * x ≤ (n : ℝ) := by
          by_cases hlow : (n : ℝ) ≤ x / 2
          · exact Or.inl hlow
          · exact Or.inr (le_of_not_gt (fun hu => hres ⟨lt_of_not_ge hlow, hu⟩))
        have hterm := norm_vonMangoldt_general_cutoffError_le_far hx hT hn hfar
        dsimp [M]
        exact hterm.trans (le_add_of_nonneg_left
          (add_nonneg (mul_nonneg hK0 (transitionWeight_nonneg x n))
            (mul_nonneg hA0 (generalHarmonicWeight_nonneg x n))))
  calc
    _ ≤ ∑' n : ℕ, e n :=
      norm_sharpPerron_logDerivative_sub_psi_le_tsum_termErrors hcOne hxPos
    _ ≤ ∑' n : ℕ, M n :=
      Summable.tsum_mono heSummable hMSummable hpoint
    _ = K * (∑' n : ℕ, sharpPerronTransitionWeight x n) +
          A * (∑' n : ℕ, sharpPerronGeneralHarmonicWeight x n) +
          B * (∑' n : ℕ, d n) := by
      rw [show M = fun n =>
        (K * sharpPerronTransitionWeight x n +
          A * sharpPerronGeneralHarmonicWeight x n) + B * d n from rfl,
        Summable.tsum_add
          (((summable_transitionWeight x).mul_left K).add
            ((summable_generalHarmonicWeight x).mul_left A))
          (hdSummable.mul_left B),
        Summable.tsum_add ((summable_transitionWeight x).mul_left K)
          ((summable_generalHarmonicWeight x).mul_left A),
        tsum_mul_left, tsum_mul_left, tsum_mul_left]
    _ ≤ K * 2 + A * (8 * (harmonic (⌊x⌋₊ + 1) : ℝ)) +
          B * (∑' n : ℕ, d n) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left
            (tsum_transitionWeight_le_two (by linarith [hx])) hK0)
          (mul_le_mul_of_nonneg_left
            (tsum_generalHarmonicWeight_le (by linarith [hx])) hA0))
        le_rfl
    _ = _ := rfl

end GafniTao
