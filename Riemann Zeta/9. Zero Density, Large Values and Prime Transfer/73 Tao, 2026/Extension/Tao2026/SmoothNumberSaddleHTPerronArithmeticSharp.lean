import Tao2026.SmoothNumberSaddleHTPerronArithmetic
import GafniTao.SharpPerronFarBounds

/-!
# Harmonic-strength arithmetic summation of the HT Perron error

The coarse integral-cutoff estimate is sharpened by retaining reciprocal
distance near `n=y`.  A comparison with the frozen half-integral harmonic
kernel bounds the whole near range by eight harmonic numbers.  Outside
`y/2<n<2y`, the additive-distance factor is at most two and the positive von
Mangoldt Dirichlet series controls the tail.
-/

open Filter Topology MeasureTheory Set Complex Finset
open scoped ArithmeticFunction.vonMangoldt BigOperators Interval

namespace Tao2026

noncomputable section

noncomputable def smoothSaddleHTPerronHarmonicSet (y : ℕ) : Finset ℕ :=
  (Finset.range (2 * y + 2)).filter
    (fun n => 1 ≤ |(y : ℝ) - (n : ℝ)|)

noncomputable def smoothSaddleHTPerronHarmonicWeight
    (y n : ℕ) : ℝ :=
  if n ∈ smoothSaddleHTPerronHarmonicSet y then
    1 / |(y : ℝ) - (n : ℝ)| else 0

theorem smoothSaddleHTPerronHarmonicWeight_nonneg (y n : ℕ) :
    0 ≤ smoothSaddleHTPerronHarmonicWeight y n := by
  unfold smoothSaddleHTPerronHarmonicWeight
  split_ifs <;> positivity

theorem summable_smoothSaddleHTPerronHarmonicWeight (y : ℕ) :
    Summable (smoothSaddleHTPerronHarmonicWeight y) := by
  apply summable_of_ne_finset_zero (s := smoothSaddleHTPerronHarmonicSet y)
  intro n hn
  simp [smoothSaddleHTPerronHarmonicWeight, hn]

private theorem smoothSaddleHT_distance_to_halfPoint
    {y n : ℕ} (hfar : 1 ≤ |(y : ℝ) - (n : ℝ)|) :
    1 / |(y : ℝ) - (n : ℝ)| ≤
      2 * (1 / |(y : ℝ) + 1 / 2 - (n : ℝ)|) := by
  have hhalfDist : |((y : ℝ) + 1 / 2) - (y : ℝ)| ≤ (1 / 2 : ℝ) := by
    norm_num
  have htriangle : |(y : ℝ) + 1 / 2 - (n : ℝ)| ≤
      |((y : ℝ) + 1 / 2) - (y : ℝ)| +
        |(y : ℝ) - (n : ℝ)| := by
    calc
      |(y : ℝ) + 1 / 2 - (n : ℝ)| =
          |(((y : ℝ) + 1 / 2) - (y : ℝ)) +
            ((y : ℝ) - (n : ℝ))| := by ring_nf
      _ ≤ |((y : ℝ) + 1 / 2) - (y : ℝ)| +
          |(y : ℝ) - (n : ℝ)| := abs_add_le _ _
  have hcompare : |(y : ℝ) + 1 / 2 - (n : ℝ)| ≤
      2 * |(y : ℝ) - (n : ℝ)| := by
    calc
      _ ≤ |((y : ℝ) + 1 / 2) - (y : ℝ)| +
          |(y : ℝ) - (n : ℝ)| := htriangle
      _ ≤ (1 / 2 : ℝ) + |(y : ℝ) - (n : ℝ)| := by gcongr
      _ ≤ 2 * |(y : ℝ) - (n : ℝ)| := by linarith
  have hden : 0 < |(y : ℝ) - (n : ℝ)| :=
    lt_of_lt_of_le zero_lt_one hfar
  have hhalfden : 0 < |(y : ℝ) + 1 / 2 - (n : ℝ)| := by
    have hne : (y : ℝ) + 1 / 2 ≠ (n : ℝ) := by
      intro heq
      have hreal : ((2 * y + 1 : ℕ) : ℝ) = ((2 * n : ℕ) : ℝ) := by
        push_cast
        linarith
      have hcast : (2 * y + 1 : ℕ) = 2 * n := by exact_mod_cast hreal
      omega
    exact abs_pos.mpr (sub_ne_zero.mpr hne)
  rw [show 2 * (1 / |(y : ℝ) + 1 / 2 - (n : ℝ)|) =
      2 / |(y : ℝ) + 1 / 2 - (n : ℝ)| by ring]
  exact (div_le_div_iff₀ hden hhalfden).2 (by simpa using hcompare)

theorem tsum_smoothSaddleHTPerronHarmonicWeight_le (y : ℕ) :
    (∑' n : ℕ, smoothSaddleHTPerronHarmonicWeight y n) ≤
      8 * (harmonic (y + 1) : ℝ) := by
  rw [tsum_eq_sum (s := smoothSaddleHTPerronHarmonicSet y)]
  · calc
      (∑ n ∈ smoothSaddleHTPerronHarmonicSet y,
          smoothSaddleHTPerronHarmonicWeight y n) =
        ∑ n ∈ smoothSaddleHTPerronHarmonicSet y,
          1 / |(y : ℝ) - (n : ℝ)| := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [smoothSaddleHTPerronHarmonicWeight, hn]
      _ ≤ ∑ n ∈ smoothSaddleHTPerronHarmonicSet y,
          2 * (1 / |(y : ℝ) + 1 / 2 - (n : ℝ)|) := by
            apply Finset.sum_le_sum
            intro n hn
            exact smoothSaddleHT_distance_to_halfPoint
              (Finset.mem_filter.mp hn).2
      _ ≤ ∑ n ∈ Finset.range (2 * y + 2),
          2 * (1 / |(y : ℝ) + 1 / 2 - (n : ℝ)|) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · exact Finset.filter_subset _ _
            · intro n _ _
              positivity
      _ = 2 * (∑ n ∈ Finset.range (2 * y + 2),
          1 / |(y : ℝ) + 1 / 2 - (n : ℝ)|) := by
            rw [Finset.mul_sum]
      _ ≤ 2 * (4 * (harmonic (y + 1) : ℝ)) := by
            gcongr
            exact GafniTao.sum_range_inv_abs_nat_add_half_le y
      _ = 8 * (harmonic (y + 1) : ℝ) := by ring
  · intro n hn
    have hne : n ∉ smoothSaddleHTPerronHarmonicSet y := hn
    simp [smoothSaddleHTPerronHarmonicWeight, hne]

theorem smoothSaddleHTPerronHarmonicWeight_eq_of_near
    {y n : ℕ} (hne : n ≠ y) (hnUpper : n < 2 * y) :
    smoothSaddleHTPerronHarmonicWeight y n =
      1 / |(y : ℝ) - (n : ℝ)| := by
  have hdist : (1 : ℝ) ≤ |(y : ℝ) - (n : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hny | hyn
    · rw [abs_of_nonneg]
      · have hd : 1 ≤ y - n := by omega
        rw [← Nat.cast_sub (Nat.le_of_lt hny)]
        exact_mod_cast hd
      · exact sub_nonneg.mpr (by exact_mod_cast (Nat.le_of_lt hny))
    · rw [abs_of_nonpos]
      · have hd : 1 ≤ n - y := by omega
        rw [neg_sub, ← Nat.cast_sub (Nat.le_of_lt hyn)]
        exact_mod_cast hd
      · exact sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_lt hyn))
  have hmem : n ∈ smoothSaddleHTPerronHarmonicSet y := by
    apply Finset.mem_filter.mpr
    constructor
    · rw [Finset.mem_range]
      omega
    · exact hdist
  simp [smoothSaddleHTPerronHarmonicWeight, hmem]

theorem smoothSaddleHTPerronTruncationMajorant_le_additive
    {y n : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T)
    (hn : 1 ≤ n) (hne : n ≠ y) :
    smoothSaddleHTPerronTruncationMajorant y T n ≤
      (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) /
        (Real.pi * T)) *
      (max (y : ℝ) (n : ℝ) / |(y : ℝ) - (n : ℝ)|) := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have hyPos : 0 < (y : ℝ) := by positivity
  have hnPos : 0 < (n : ℝ) := by positivity
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hfactor : 0 ≤ ArithmeticFunction.vonMangoldt n *
      (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) /
        (Real.pi * T) :=
    div_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (div_pos hyPos hnPos).le _)) hpiT.le
  rcases lt_or_gt_of_ne hne with hny | hyn
  · have hnyReal : (n : ℝ) < (y : ℝ) := by exact_mod_cast hny
    have hInv := GafniTao.one_div_log_div_le_div_sub_of_pos_of_lt
      hnPos hnyReal
    unfold smoothSaddleHTPerronTruncationMajorant
    rw [if_neg hn0, if_pos hny, max_eq_left hnyReal.le,
      abs_of_nonneg (sub_nonneg.mpr hnyReal.le)]
    calc
      ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
            (Real.pi * T * Real.log ((y : ℝ) / n))) =
        (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) /
            (Real.pi * T)) *
          (1 / Real.log ((y : ℝ) / n)) := by ring
      _ ≤ (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) /
            (Real.pi * T)) * ((y : ℝ) / ((y : ℝ) - n)) :=
        mul_le_mul_of_nonneg_left hInv hfactor
  · have hny : ¬n < y := by omega
    have hynReal : (y : ℝ) < (n : ℝ) := by exact_mod_cast hyn
    have hInv := GafniTao.one_div_neg_log_div_le_div_sub_of_pos_of_lt
      hyPos hynReal
    unfold smoothSaddleHTPerronTruncationMajorant
    rw [if_neg hn0, if_neg hny, if_neg hne,
      max_eq_right hynReal.le,
      abs_of_nonpos (sub_nonpos.mpr hynReal.le), neg_sub]
    calc
      ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
            (Real.pi * T * (-Real.log ((y : ℝ) / n)))) =
        (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) /
            (Real.pi * T)) *
          (1 / (-Real.log ((y : ℝ) / n))) := by ring
      _ ≤ (ArithmeticFunction.vonMangoldt n *
          (((y : ℝ) / n) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) /
            (Real.pi * T)) * ((n : ℝ) / ((n : ℝ) - y)) :=
        mul_le_mul_of_nonneg_left hInv hfactor

theorem smoothSaddleHTPerronTruncationMajorant_le_near
    {y n : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T)
    (hn : 1 ≤ n) (hne : n ≠ y)
    (hnLower : (y : ℝ) / 2 < n) (hnUpper : (n : ℝ) < 2 * y) :
    smoothSaddleHTPerronTruncationMajorant y T n ≤
      (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
          (Real.pi * T)) *
        smoothSaddleHTPerronHarmonicWeight y n := by
  let c := GafniTao.sharpPerronAbscissa (y : ℝ)
  have hyPos : 0 < (y : ℝ) := by positivity
  have hnPos : 0 < (n : ℝ) := by positivity
  have hratio0 : 0 ≤ (y : ℝ) / n := (div_pos hyPos hnPos).le
  have hratio2 : (y : ℝ) / n ≤ 2 := by
    rw [div_le_iff₀ hnPos]
    linarith
  have hyReal : (2 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have hpow := GafniTao.rpow_sharpPerronAbscissa_le_ratioBound
    hyReal hratio0 hratio2
  have hLambda : ArithmeticFunction.vonMangoldt n ≤ Real.log (2 * y) :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hnPos hnUpper.le)
  have hmax : max (y : ℝ) (n : ℝ) ≤ 2 * y :=
    max_le (by linarith) hnUpper.le
  have hdist : (1 : ℝ) ≤ |(y : ℝ) - (n : ℝ)| := by
    rcases lt_or_gt_of_ne hne with hny | hyn
    · have hnyReal : (n : ℝ) ≤ (y : ℝ) := by exact_mod_cast hny.le
      rw [abs_of_nonneg (sub_nonneg.mpr hnyReal)]
      have hd : 1 ≤ y - n := by omega
      rw [← Nat.cast_sub (Nat.le_of_lt hny)]
      exact_mod_cast hd
    · have hynReal : (y : ℝ) ≤ (n : ℝ) := by exact_mod_cast hyn.le
      rw [abs_of_nonpos (sub_nonpos.mpr hynReal), neg_sub]
      have hd : 1 ≤ n - y := by omega
      rw [← Nat.cast_sub (Nat.le_of_lt hyn)]
      exact_mod_cast hd
  have hden : 0 < |(y : ℝ) - (n : ℝ)| := zero_lt_one.trans_le hdist
  have hpiT : 0 < Real.pi * T := mul_pos Real.pi_pos hT
  have hnum : ArithmeticFunction.vonMangoldt n *
      ((y : ℝ) / n) ^ c ≤
        GafniTao.sharpPerronRatioBound * Real.log (2 * y) := by
    calc
      _ ≤ Real.log (2 * y) * GafniTao.sharpPerronRatioBound :=
        mul_le_mul hLambda hpow (Real.rpow_nonneg hratio0 _)
          (Real.log_nonneg (by linarith))
      _ = _ := by ring
  have hweight := smoothSaddleHTPerronHarmonicWeight_eq_of_near hne
    (by exact_mod_cast hnUpper)
  refine (smoothSaddleHTPerronTruncationMajorant_le_additive
    hy hT hn hne).trans ?_
  rw [hweight]
  calc
    (ArithmeticFunction.vonMangoldt n * ((y : ℝ) / n) ^ c /
        (Real.pi * T)) *
        (max (y : ℝ) (n : ℝ) / |(y : ℝ) - (n : ℝ)|) ≤
      (GafniTao.sharpPerronRatioBound * Real.log (2 * y) /
        (Real.pi * T)) *
        ((2 * y) / |(y : ℝ) - (n : ℝ)|) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right hnum hpiT.le)
        (div_le_div_of_nonneg_right hmax hden.le)
        (div_nonneg (by positivity) hden.le)
        (div_nonneg
          (mul_nonneg
            (le_trans (by norm_num) GafniTao.one_le_sharpPerronRatioBound)
            (Real.log_nonneg (by linarith))) hpiT.le)
    _ = (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
          (Real.pi * T)) *
        (1 / |(y : ℝ) - (n : ℝ)|) := by ring

theorem smoothSaddleHTPerronTruncationMajorant_le_far
    {y n : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T)
    (hn : 1 ≤ n)
    (hfar : (n : ℝ) ≤ (y : ℝ) / 2 ∨ 2 * (y : ℝ) ≤ n) :
    smoothSaddleHTPerronTruncationMajorant y T n ≤
      (2 * (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
          (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          (n : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) := by
  let c := GafniTao.sharpPerronAbscissa (y : ℝ)
  have hyPos : 0 < (y : ℝ) := by positivity
  have hnPos : 0 < (n : ℝ) := by positivity
  have hne : n ≠ y := by
    intro heq
    subst n
    rcases hfar with h | h <;> nlinarith
  have hfactor := GafniTao.max_div_abs_sub_le_two_of_far
    hyPos hnPos hfar
  have hbase : 0 ≤ ArithmeticFunction.vonMangoldt n *
      ((y : ℝ) / n) ^ c / (Real.pi * T) :=
    div_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (div_pos hyPos hnPos).le _))
      (mul_nonneg Real.pi_pos.le hT.le)
  refine (smoothSaddleHTPerronTruncationMajorant_le_additive
    hy hT hn hne).trans ?_
  calc
    (ArithmeticFunction.vonMangoldt n * ((y : ℝ) / n) ^ c /
        (Real.pi * T)) *
        (max (y : ℝ) (n : ℝ) / |(y : ℝ) - (n : ℝ)|) ≤
      (ArithmeticFunction.vonMangoldt n * ((y : ℝ) / n) ^ c /
        (Real.pi * T)) * 2 :=
          mul_le_mul_of_nonneg_left hfactor hbase
    _ = (2 * (y : ℝ) ^ c / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c) := by
      rw [Real.div_rpow hyPos.le hnPos.le]
      ring

/-- The endpoint, harmonic near range, and Dirichlet far range form one
summable pointwise majorant. -/
theorem smoothSaddleHTPerronTruncationMajorant_le_sharp_components
    {y : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T) (n : ℕ) :
    smoothSaddleHTPerronTruncationMajorant y T n ≤
      smoothSaddleHTPerronEndpointWeight y n +
        (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
            (Real.pi * T)) *
          smoothSaddleHTPerronHarmonicWeight y n +
        (2 * (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
            (Real.pi * T)) *
          (ArithmeticFunction.vonMangoldt n /
            (n : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) := by
  let A := GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
    (Real.pi * T)
  let B := 2 * (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
    (Real.pi * T)
  let d : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n /
    (n : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    have htwoY : (1 : ℝ) ≤ 2 * (y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * y by omega)
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (le_trans (by norm_num) GafniTao.one_le_sharpPerronRatioBound)
          (Real.log_nonneg htwoY)) (by positivity))
      (mul_nonneg Real.pi_pos.le hT.le)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hd : ∀ n, 0 ≤ d n := fun n => by
    dsimp [d]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  by_cases hn0 : n = 0
  · subst n
    have hyne : (0 : ℕ) ≠ y := by omega
    have hM0 : smoothSaddleHTPerronTruncationMajorant y T 0 = 0 := by
      simp [smoothSaddleHTPerronTruncationMajorant]
    rw [hM0]
    change 0 ≤ smoothSaddleHTPerronEndpointWeight y 0 +
      A * smoothSaddleHTPerronHarmonicWeight y 0 + B * d 0
    exact add_nonneg
      (add_nonneg (smoothSaddleHTPerronEndpointWeight_nonneg y 0)
        (mul_nonneg hA (smoothSaddleHTPerronHarmonicWeight_nonneg y 0)))
      (mul_nonneg hB (hd 0))
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  by_cases hne : n = y
  · subst n
    have hy0 : y ≠ 0 := by omega
    have hM : smoothSaddleHTPerronTruncationMajorant y T y =
        ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) := by
      simp [smoothSaddleHTPerronTruncationMajorant, hy0]
    have hE : smoothSaddleHTPerronEndpointWeight y y =
        ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) := by
      simp [smoothSaddleHTPerronEndpointWeight]
    rw [hM, hE]
    change ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) ≤
      ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
        A * smoothSaddleHTPerronHarmonicWeight y y + B * d y
    linarith [mul_nonneg hA (smoothSaddleHTPerronHarmonicWeight_nonneg y y),
      mul_nonneg hB (hd y)]
  · by_cases hres : (y : ℝ) / 2 < n ∧ (n : ℝ) < 2 * y
    · have hnear := smoothSaddleHTPerronTruncationMajorant_le_near
        hy hT hn hne hres.1 hres.2
      have hE0 : smoothSaddleHTPerronEndpointWeight y n = 0 := by
        simp [smoothSaddleHTPerronEndpointWeight, hne]
      rw [hE0]
      change smoothSaddleHTPerronTruncationMajorant y T n ≤
        0 + A * smoothSaddleHTPerronHarmonicWeight y n + B * d n
      calc
        _ ≤ A * smoothSaddleHTPerronHarmonicWeight y n := by
          simpa [A] using hnear
        _ ≤ 0 + A * smoothSaddleHTPerronHarmonicWeight y n + B * d n := by
          linarith [mul_nonneg hB (hd n)]
    · have hfar : (n : ℝ) ≤ (y : ℝ) / 2 ∨ 2 * (y : ℝ) ≤ n := by
        by_cases hlow : (n : ℝ) ≤ (y : ℝ) / 2
        · exact Or.inl hlow
        · exact Or.inr (le_of_not_gt (fun hu => hres ⟨lt_of_not_ge hlow, hu⟩))
      have htail := smoothSaddleHTPerronTruncationMajorant_le_far
        hy hT hn hfar
      have hE0 : smoothSaddleHTPerronEndpointWeight y n = 0 := by
        simp [smoothSaddleHTPerronEndpointWeight, hne]
      rw [hE0]
      change smoothSaddleHTPerronTruncationMajorant y T n ≤
        0 + A * smoothSaddleHTPerronHarmonicWeight y n + B * d n
      calc
        _ ≤ B * d n := by simpa [B, d] using htail
        _ ≤ 0 + A * smoothSaddleHTPerronHarmonicWeight y n + B * d n := by
          linarith [mul_nonneg hA
            (smoothSaddleHTPerronHarmonicWeight_nonneg y n)]

/-- Harmonic-strength arithmetic estimate for the complete scalar
truncation majorant. -/
theorem tsum_smoothSaddleHTPerronTruncationMajorant_le_sharp_arithmetic
    {y : ℕ} {T : ℝ} (hy : 2 ≤ y) (hT : 0 < T) :
    ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n ≤
      ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
        (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
            (Real.pi * T)) * (8 * (harmonic (y + 1) : ℝ)) +
        (2 * (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
            (Real.pi * T)) *
          (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
            (n : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) := by
  let c := GafniTao.sharpPerronAbscissa (y : ℝ)
  let A := GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
    (Real.pi * T)
  let B := 2 * (y : ℝ) ^ c / (Real.pi * T)
  let d : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ c
  have hc : 1 < c := GafniTao.one_lt_sharpPerronAbscissa
    (by exact_mod_cast (show 1 < y by omega))
  have hd : Summable d := GafniTao.summable_vonMangoldt_div_nat_rpow hc
  have he := summable_smoothSaddleHTPerronEndpointWeight y
  have hw := summable_smoothSaddleHTPerronHarmonicWeight y
  have hm := summable_smoothSaddleHTPerronTruncationMajorant hy hT
  have hA : 0 ≤ A := by
    dsimp [A]
    have htwoY : (1 : ℝ) ≤ 2 * (y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * y by omega)
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (le_trans (by norm_num) GafniTao.one_le_sharpPerronRatioBound)
          (Real.log_nonneg htwoY)) (by positivity))
      (mul_nonneg Real.pi_pos.le hT.le)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hright : Summable (fun n =>
      smoothSaddleHTPerronEndpointWeight y n +
        A * smoothSaddleHTPerronHarmonicWeight y n + B * d n) :=
    (he.add (hw.mul_left A)).add (hd.mul_left B)
  calc
    ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n ≤
        ∑' n : ℕ, (smoothSaddleHTPerronEndpointWeight y n +
          A * smoothSaddleHTPerronHarmonicWeight y n + B * d n) :=
      Summable.tsum_mono hm hright (fun n => by
        simpa [A, B, d, c] using
          smoothSaddleHTPerronTruncationMajorant_le_sharp_components
            hy hT n)
    _ = (∑' n : ℕ, smoothSaddleHTPerronEndpointWeight y n) +
          A * (∑' n : ℕ, smoothSaddleHTPerronHarmonicWeight y n) +
          B * (∑' n : ℕ, d n) := by
      rw [Summable.tsum_add (he.add (hw.mul_left A)) (hd.mul_left B),
        Summable.tsum_add he (hw.mul_left A), tsum_mul_left, tsum_mul_left]
    _ ≤ ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
          A * (8 * (harmonic (y + 1) : ℝ)) +
          B * (∑' n : ℕ, d n) := by
      rw [tsum_smoothSaddleHTPerronEndpointWeight]
      gcongr
      exact tsum_smoothSaddleHTPerronHarmonicWeight_le y
    _ = _ := rfl

/-- Fully explicit harmonic-strength bound. -/
theorem exists_tsum_smoothSaddleHTPerronTruncationMajorant_le_sharp_explicit :
    ∃ C₀ ≥ 0, ∀ (y : ℕ) (T : ℝ), 2 ≤ y → 0 < T →
      ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n ≤
        ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
          (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
              (Real.pi * T)) *
            (8 * (1 + Real.log (y + 1))) +
          (2 * (Real.exp 1 * y) / (Real.pi * T)) *
            (Real.log y + C₀) := by
  obtain ⟨C₀, hC₀, hseries⟩ :=
    GafniTao.exists_tsum_vonMangoldt_optimized_le
  refine ⟨C₀, hC₀, fun y T hy hT => ?_⟩
  have hbase :=
    tsum_smoothSaddleHTPerronTruncationMajorant_le_sharp_arithmetic hy hT
  have hharm : ((harmonic (y + 1) : ℚ) : ℝ) ≤
      1 + Real.log (y + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (harmonic_le_one_add_log (y + 1))
  have hseriesY := hseries (y : ℝ)
    (by exact_mod_cast (show 1 < y by omega))
  have hnearCoef : 0 ≤
      GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
        (Real.pi * T) := by
    have htwoY : (1 : ℝ) ≤ 2 * (y : ℝ) := by
      exact_mod_cast (show 1 ≤ 2 * y by omega)
    exact div_nonneg
      (mul_nonneg
        (mul_nonneg
          (le_trans (by norm_num) GafniTao.one_le_sharpPerronRatioBound)
          (Real.log_nonneg htwoY)) (by positivity))
      (mul_nonneg Real.pi_pos.le hT.le)
  have hfarCoef : 0 ≤ 2 *
      (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
        (Real.pi * T) := by positivity
  calc
    ∑' n : ℕ, smoothSaddleHTPerronTruncationMajorant y T n ≤
        ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
          (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
              (Real.pi * T)) * (8 * (harmonic (y + 1) : ℝ)) +
          (2 * (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
              (Real.pi * T)) *
            (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
              (n : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ)) := hbase
    _ ≤ ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
          (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
              (Real.pi * T)) * (8 * (1 + Real.log (y + 1))) +
          (2 * (y : ℝ) ^ GafniTao.sharpPerronAbscissa (y : ℝ) /
              (Real.pi * T)) * (Real.log y + C₀) := by
      gcongr
    _ = _ := by
      rw [GafniTao.rpow_sharpPerronAbscissa
        (by exact_mod_cast (show 1 < y by omega))]

/-- Harmonic-strength truncation estimate at the source-selected HT height. -/
theorem exists_norm_smoothSaddleHTContourTruncationError_le_sharp_explicit :
    ∃ C₀ ≥ 0, ∀ (y : ℕ) (beta ε t : ℝ), 2 ≤ y → 0 < beta →
      ‖smoothSaddleHTContourTruncationError y beta ε t‖ ≤
        (y : ℝ) ^ (beta - 1) *
          (ArithmeticFunction.vonMangoldt y * (3 / 2 : ℝ) +
            (GafniTao.sharpPerronRatioBound * Real.log (2 * y) * (2 * y) /
                (Real.pi * smoothSaddleHTContourHeight y ε)) *
              (8 * (1 + Real.log (y + 1))) +
            (2 * (Real.exp 1 * y) /
                (Real.pi * smoothSaddleHTContourHeight y ε)) *
              (Real.log y + C₀)) := by
  obtain ⟨C₀, hC₀, hmajorant⟩ :=
    exists_tsum_smoothSaddleHTPerronTruncationMajorant_le_sharp_explicit
  refine ⟨C₀, hC₀, fun y beta ε t hy hbeta => ?_⟩
  have hfirst :=
    norm_smoothSaddleHTContourTruncationError_le_tsum_majorant
      (ε := ε) (t := t) hy hbeta
  have hsum := hmajorant y (smoothSaddleHTContourHeight y ε) hy
    (smoothSaddleHTContourHeight_pos y ε)
  exact hfirst.trans (mul_le_mul_of_nonneg_left hsum
    (Real.rpow_nonneg (by positivity : 0 ≤ (y : ℝ)) _))

end

end Tao2026
