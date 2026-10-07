import Dubon2026.RieszDirichletInterchange
import Dubon2026.RieszSecondSum

/-! # The exact Perron integral for literal second Riesz sums -/

namespace Dubon2026

open Complex MeasureTheory

noncomputable section

/-- The actual cutoff series is supported on the precise positive-index floor interval. -/
theorem rieszMellinCutoff_nat_mul_inv_eq_zero {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : n ∉ Finset.Icc 1 ⌊x⌋₊) :
    rieszMellinCutoff ((n : ℝ) * x⁻¹) = 0 := by
  by_cases hn0 : n = 0
  · simp [hn0, rieszMellinCutoff]
  · have hnx : ⌊x⌋₊ < n := by
      have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      simpa only [Finset.mem_Icc, hn1, true_and, not_le] using hn
    have hxn : x < (n : ℝ) := Nat.lt_of_floor_lt hnx
    apply Set.indicator_of_notMem (s := Set.Ioc (0 : ℝ) 1)
    intro h
    have hh : (n : ℝ) ≤ x := by
      have := (div_le_iff₀ hx).mp (show (n : ℝ) / x ≤ 1 by simpa only [div_eq_mul_inv] using h.2)
      simpa using this
    linarith

/-- On its exact positive support, the dilated cutoff is the literal quadratic Riesz weight. -/
theorem rieszMellinCutoff_nat_mul_inv_weight {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : n ∈ Finset.Icc 1 ⌊x⌋₊) :
    (x : ℂ) ^ 2 * rieszMellinCutoff ((n : ℝ) * x⁻¹) = ((x : ℂ) - n) ^ 2 / 2 := by
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hnx : (n : ℝ) ≤ x := (Nat.le_floor_iff' hn0).mp (Finset.mem_Icc.mp hn).2
  have hm : (n : ℝ) * x⁻¹ ∈ Set.Ioc (0 : ℝ) 1 := by
    refine ⟨mul_pos hnpos (inv_pos.mpr hx), ?_⟩
    simpa only [div_eq_mul_inv] using (div_le_one hx).mpr hnx
  rw [rieszMellinCutoff, Set.indicator_of_mem hm]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hx.ne']

/-- Absolute convergence gives the exact Perron formula for the genuine finite quadratic sum. -/
theorem rieszPerron_formula {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    {a : ℕ → ℂ} (ha : LSeriesSummable a σ) :
    (x : ℂ) ^ 2 * mellinInv σ (fun s => LSeries a s * rieszMellinSymbol s) x⁻¹ =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * ((x : ℂ) - n) ^ 2 / 2 := by
  rw [mellinInv_LSeries_riesz hσ (inv_pos.mpr hx) ha]
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊)
    (fun n hn => by rw [rieszMellinCutoff_nat_mul_inv_eq_zero hx hn, mul_zero])]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← mul_assoc, mul_comm ((x : ℂ) ^ 2) (a n), mul_assoc,
    rieszMellinCutoff_nat_mul_inv_weight hx hn]
  ring

/-- The exact inverse integral equals the actual real second Riesz sum used in the unsmoothing bounds. -/
theorem rieszSecondSum_eq_perron {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x)
    {a : ℕ → ℝ} (ha : LSeriesSummable (fun n => (a n : ℂ)) σ) :
    (rieszSecondSum a x : ℂ) =
      (x : ℂ) ^ 2 * mellinInv σ
        (fun s => LSeries (fun n => (a n : ℂ)) s * rieszMellinSymbol s) x⁻¹ := by
  rw [rieszPerron_formula hσ hx ha, rieszSecondSum_eq]
  push_cast
  rfl

end
end Dubon2026
