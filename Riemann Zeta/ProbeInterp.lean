import RiemannZeta.GuthMaynard.DFIErrorOptimization

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

theorem test_gcd_interp (A q : ℕ) (hA : 0 < A) (hq : 0 < q)
    (delta : ℝ) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    (Nat.gcd A q : ℝ) ≤
      (A : ℝ) ^ delta * (q : ℝ) ^ (1 - delta) := by
  have hg : 0 < Nat.gcd A q := Nat.gcd_pos_of_pos_left q hA
  have hgA : Nat.gcd A q ≤ A := Nat.gcd_le_left q hA
  have hgq : Nat.gcd A q ≤ q := Nat.gcd_le_right A hq
  have hgR : (0 : ℝ) < Nat.gcd A q := by exact_mod_cast hg
  calc
    (Nat.gcd A q : ℝ) =
        (Nat.gcd A q : ℝ) ^ delta *
          (Nat.gcd A q : ℝ) ^ (1 - delta) := by
      rw [← Real.rpow_add hgR]
      norm_num
    _ ≤ (A : ℝ) ^ delta * (q : ℝ) ^ (1 - delta) := by
      apply mul_le_mul
      · exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast hgA) hd0
      · exact Real.rpow_le_rpow (by positivity)
          (by exact_mod_cast hgq) (sub_nonneg.mpr hd1)
      · positivity
      · positivity

theorem test_pointwise
    (a b h q : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    [NeZero q] (delta : ℝ) (hd0 : 0 ≤ delta) (hd1 : delta ≤ 1) :
    ‖(((a : ℂ) * b)⁻¹) * dfiEquation27ArithmeticCoefficient a b h q‖ ≤
      (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (∑ d ∈ h.divisors,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
  have hq : 0 < q := NeZero.pos q
  have hA : 0 < a * b := Nat.mul_pos ha hb
  have hg := test_gcd_interp (a * b) q hA hq delta hd0 hd1
  rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast,
    Complex.norm_natCast]
  rw [dfiEquation27ArithmeticCoefficient_eq]
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow,
    Complex.norm_natCast]
  have hram := norm_ramanujanSum_le_sum_divisors_filter_dvd q h hh.ne'
  let A : ℝ := (a : ℝ) * b
  have hAcast : 0 < A := by dsimp [A]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hAinv : A⁻¹ = A ^ (-(1 : ℝ)) := by
    rw [Real.rpow_neg hAcast.le, Real.rpow_one]
  have hscalar :
      (((a : ℝ) * b)⁻¹) *
          ((((a * b : ℕ) : ℝ) ^ delta * (q : ℝ) ^ (1 - delta)) /
            (q : ℝ) ^ 2) =
        (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
          (q : ℝ) ^ (-(1 + delta)) := by
    push_cast
    change A⁻¹ * (A ^ delta * (q : ℝ) ^ (1 - delta) /
      (q : ℝ) ^ 2) = A ^ (-1 + delta) * (q : ℝ) ^ (-(1 + delta))
    rw [hAinv, show (q : ℝ) ^ 2 = (q : ℝ) ^ (2 : ℝ) by norm_num,
      div_eq_mul_inv, ← Real.rpow_neg hqR.le]
    calc
      A ^ (-(1 : ℝ)) *
          (A ^ delta * q ^ (1 - delta) * q ^ (-(2 : ℝ))) =
        (A ^ (-(1 : ℝ)) * A ^ delta) *
          (q ^ (1 - delta) * q ^ (-(2 : ℝ))) := by ring
      _ = A ^ (-(1 : ℝ) + delta) *
          q ^ ((1 - delta) + -(2 : ℝ)) := by
        rw [← Real.rpow_add hAcast, ← Real.rpow_add hqR]
      _ = _ := by
        congr 1
        all_goals ring
  calc
    (((a : ℝ) * b)⁻¹) *
        (((Nat.gcd (a * b) q : ℝ) / (q : ℝ) ^ 2) *
          ‖ramanujanSum q h‖) ≤
      (((a : ℝ) * b)⁻¹) *
        ((((a * b : ℕ) : ℝ) ^ delta * (q : ℝ) ^ (1 - delta)) /
          (q : ℝ) ^ 2 *
          (∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0)) := by
      gcongr
    _ = (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (∑ d ∈ h.divisors,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
      rw [show (((a : ℝ) * b)⁻¹) *
          ((((a * b : ℕ) : ℝ) ^ delta * (q : ℝ) ^ (1 - delta)) /
            (q : ℝ) ^ 2 *
            (∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0)) =
          ((((a : ℝ) * b)⁻¹) *
            ((((a * b : ℕ) : ℝ) ^ delta * (q : ℝ) ^ (1 - delta)) /
              (q : ℝ) ^ 2)) *
            (∑ d ∈ h.divisors, if d ∣ q then (d : ℝ) else 0) by ring,
        hscalar]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdq : d ∣ q
      · simp only [hdq, if_true]
        rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
        ring
      · simp [hdq]

theorem test_sparse_tail (K L d : ℕ) (hd : 0 < d)
    (delta : ℝ) (hdelta : 0 < delta) :
    (∑ q ∈ Finset.Ioo K L,
        if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) ≤
      ((K + 1 : ℕ) : ℝ) ^ (-delta) *
        ((harmonic L : ℚ) : ℝ) := by
  rw [← Finset.sum_filter]
  calc
    ∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
        (d : ℝ) / (q : ℝ) ^ (1 + delta) ≤
      ∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
        ((K + 1 : ℕ) : ℝ) ^ (-delta) *
          (1 / ((q / d : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqIoo := Finset.mem_Ioo.mp (Finset.mem_filter.mp hq).1
      have hdq := (Finset.mem_filter.mp hq).2
      have hqPos : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hqIoo.1
      have hKq : ((K + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hqIoo.1
      have hKpos : (0 : ℝ) < (K + 1 : ℕ) := by positivity
      have hqPosR : (0 : ℝ) < q := by exact_mod_cast hqPos
      have hdPosR : (0 : ℝ) < d := by exact_mod_cast hd
      have hquot : (q : ℝ) / d = (q / d : ℕ) := by
        rw [Nat.cast_div hdq hdPosR.ne']
      have hpow : (q : ℝ) ^ (-delta) ≤
          ((K + 1 : ℕ) : ℝ) ^ (-delta) :=
        Real.rpow_le_rpow_of_nonpos hKpos hKq (neg_nonpos.mpr hdelta.le)
      calc
        (d : ℝ) / (q : ℝ) ^ (1 + delta) =
            (q : ℝ) ^ (-delta) * ((d : ℝ) / q) := by
          rw [div_eq_mul_inv, ← Real.rpow_neg hqPosR.le]
          rw [show (q : ℝ) ^ (-(1 + delta)) =
              (q : ℝ) ^ (-delta) * (q : ℝ) ^ (-(1 : ℝ)) by
            rw [← Real.rpow_add hqPosR]
            congr 1
            ring]
          have hqnegone : (q : ℝ) ^ (-(1 : ℝ)) = (q : ℝ)⁻¹ := by
            rw [Real.rpow_neg hqPosR.le, Real.rpow_one]
          rw [hqnegone]
          ring
        _ ≤ ((K + 1 : ℕ) : ℝ) ^ (-delta) * ((d : ℝ) / q) := by
          gcongr
        _ = ((K + 1 : ℕ) : ℝ) ^ (-delta) *
            (1 / ((q : ℝ) / d)) := by field_simp
        _ = ((K + 1 : ℕ) : ℝ) ^ (-delta) *
            (1 / ((q / d : ℕ) : ℝ)) := by rw [hquot]
    _ = ((K + 1 : ℕ) : ℝ) ^ (-delta) *
        (∑ q ∈ (Finset.Ioo K L).filter (d ∣ ·),
          (1 / ((q / d : ℕ) : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ ((K + 1 : ℕ) : ℝ) ^ (-delta) *
        ((harmonic L : ℚ) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (sum_Ioo_filter_dvd_one_div_quotient_le_harmonic K L d hd)
        (Real.rpow_nonneg (by positivity) _)

theorem test_sum_interpolated
    (a b h K L : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (∑ q ∈ Finset.Ioo K L,
        ‖(((a : ℂ) * b)⁻¹) *
          dfiEquation27ArithmeticCoefficient a b h q‖) ≤
      (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (h.divisors.card : ℝ) *
        (((K + 1 : ℕ) : ℝ) ^ (-delta) *
          ((harmonic L : ℚ) : ℝ)) := by
  let A : ℝ := (((a * b : ℕ) : ℝ) ^ (-1 + delta))
  let B : ℝ := ((K + 1 : ℕ) : ℝ) ^ (-delta) *
    ((harmonic L : ℚ) : ℝ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hEach : ∀ d ∈ h.divisors,
      (∑ q ∈ Finset.Ioo K L,
        if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) ≤ B := by
    intro d hdmem
    have hd : 0 < d := Nat.pos_of_mem_divisors hdmem
    simpa only [B] using test_sparse_tail K L d hd delta hdelta0
  calc
    (∑ q ∈ Finset.Ioo K L,
        ‖(((a : ℂ) * b)⁻¹) *
          dfiEquation27ArithmeticCoefficient a b h q‖) ≤
      ∑ q ∈ Finset.Ioo K L, A *
        (∑ d ∈ h.divisors,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqpos : 0 < q :=
        lt_of_le_of_lt (Nat.zero_le K) (Finset.mem_Ioo.mp hq).1
      letI : NeZero q := ⟨hqpos.ne'⟩
      simpa only [A] using
        test_pointwise a b h q ha hb hh delta hdelta0.le hdelta1
    _ = A * (∑ d ∈ h.divisors,
        ∑ q ∈ Finset.Ioo K L,
          if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
      calc
        (∑ q ∈ Finset.Ioo K L, A *
            (∑ d ∈ h.divisors,
              if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0)) =
          ∑ q ∈ Finset.Ioo K L, ∑ d ∈ h.divisors,
            A * (if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.mul_sum]
        _ = ∑ d ∈ h.divisors, ∑ q ∈ Finset.Ioo K L,
            A * (if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
          rw [Finset.sum_comm]
        _ = A * (∑ d ∈ h.divisors,
            ∑ q ∈ Finset.Ioo K L,
              if d ∣ q then (d : ℝ) / (q : ℝ) ^ (1 + delta) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mul_sum]
    _ ≤ A * (∑ _d ∈ h.divisors, B) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun d hd => hEach d hd) hA
    _ = (((a * b : ℕ) : ℝ) ^ (-1 + delta)) *
        (h.divisors.card : ℝ) *
        (((K + 1 : ℕ) : ℝ) ^ (-delta) *
          ((harmonic L : ℚ) : ℝ)) := by
      simp only [A, B, Finset.sum_const, nsmul_eq_mul]
      ring

end RiemannZeta.GuthMaynard
