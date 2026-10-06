import Dubon2026.BinomialZeros
import Dubon2026.BinomialMeasure
import Mathlib.Topology.Algebra.Order.Field

/-! # The normalization example's multiplicity-weighted zero-density limit -/

namespace Dubon2026

open Filter Set
open scoped Topology BigOperators

noncomputable section

/-- Exact integer indices for the open symmetric height cutoff. -/
def binomialZeroIndices (κ T : ℝ) : Finset ℤ :=
  Finset.Ioo ⌊-κ * T / (2 * Real.pi) - 1 / 2⌋ ⌈κ * T / (2 * Real.pi) - 1 / 2⌉

theorem mem_binomialZeroIndices {κ : ℝ} (hκ : 0 < κ) (T : ℝ) (m : ℤ) :
    m ∈ binomialZeroIndices κ T ↔ |(binomialZero κ m).im| < T := by
  rw [binomialZeroIndices, Finset.mem_Ioo, Int.floor_lt, Int.lt_ceil, binomialZero_im, abs_lt]
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [lt_div_iff₀ hκ, div_lt_iff₀ hκ]
  constructor
  · rintro ⟨hl, hu⟩
    have hl' : -κ * T / (2 * Real.pi) < (m : ℝ) + 1 / 2 := by linarith
    have hu' : (m : ℝ) + 1 / 2 < κ * T / (2 * Real.pi) := by linarith
    rw [div_lt_iff₀ hp] at hl'
    rw [lt_div_iff₀ hp] at hu'
    constructor <;> nlinarith
  · rintro ⟨hl, hu⟩
    have hl' : -κ * T / (2 * Real.pi) < (m : ℝ) + 1 / 2 := by
      rw [div_lt_iff₀ hp]
      nlinarith
    have hu' : (m : ℝ) + 1 / 2 < κ * T / (2 * Real.pi) := by
      rw [lt_div_iff₀ hp]
      nlinarith
    constructor <;> linarith

/-- The finite set of actual zeros under the height cutoff, via the proved lattice parametrization. -/
def binomialZerosFinset (κ T : ℝ) : Finset ℂ :=
  (binomialZeroIndices κ T).image (binomialZero κ)

theorem mem_binomialZerosFinset {κ : ℝ} (hκ : 0 < κ) (T : ℝ) (s : ℂ) :
    s ∈ binomialZerosFinset κ T ↔ |s.im| < T ∧ binomialDirichlet κ s = 0 := by
  classical
  rw [binomialZerosFinset, Finset.mem_image]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨(mem_binomialZeroIndices hκ T m).mp hm,
      (binomialDirichlet_zero_iff hκ.ne' _).mpr ⟨m, rfl⟩⟩
  · rintro ⟨ht, hz⟩
    obtain ⟨m, rfl⟩ := (binomialDirichlet_zero_iff hκ.ne' s).mp hz
    exact ⟨m, (mem_binomialZeroIndices hκ T m).mpr ht, rfl⟩

/-- Count the genuine zeros with analytic multiplicities, without a density assumption. -/
def binomialVerticalZeroCount (κ T : ℝ) : ℕ :=
  ∑ s ∈ binomialZerosFinset κ T, analyticOrderNatAt (binomialDirichlet κ) s

theorem binomialVerticalZeroCount_eq_card {κ : ℝ} (hκ : 0 < κ) (T : ℝ) :
    binomialVerticalZeroCount κ T = (binomialZeroIndices κ T).card := by
  classical
  unfold binomialVerticalZeroCount
  have he : (∑ s ∈ binomialZerosFinset κ T, analyticOrderNatAt (binomialDirichlet κ) s) =
      ∑ _s ∈ binomialZerosFinset κ T, (1 : ℕ) := by
    apply Finset.sum_congr rfl
    intro s hs
    exact analyticOrderNatAt_binomial_zero hκ.ne' ((mem_binomialZerosFinset hκ T s).mp hs).2
  rw [he, Finset.sum_const, smul_eq_mul, mul_one, binomialZerosFinset,
    Finset.card_image_of_injective _ (binomialZero_injective hκ.ne')]

theorem abs_integer_open_interval_card_sub_length {a b : ℝ} (hab : a < b) :
    |((Finset.Ioo ⌊a⌋ ⌈b⌉).card : ℝ) - (b - a)| ≤ 1 := by
  have hi := Int.floor_lt_ceil_of_lt hab
  have hc : ((Finset.Ioo ⌊a⌋ ⌈b⌉).card : ℝ) = (⌈b⌉ : ℝ) - (⌊a⌋ : ℝ) - 1 := by
    exact_mod_cast Int.card_Ioo_of_lt ⌊a⌋ ⌈b⌉ hi
  rw [hc, abs_le]
  have hfa := Int.floor_le a
  have haf := Int.sub_one_lt_floor a
  have hbc := Int.le_ceil b
  have hcb := Int.ceil_lt_add_one b
  constructor <;> linarith

theorem binomialVerticalZeroCount_error {κ : ℝ} (hκ : 0 < κ) {T : ℝ} (hT : 0 < T) :
    |(binomialVerticalZeroCount κ T : ℝ) - κ * T / Real.pi| ≤ 1 := by
  rw [binomialVerticalZeroCount_eq_card hκ]
  have hp : 0 < κ * T / (2 * Real.pi) := by positivity
  have hh := abs_integer_open_interval_card_sub_length
    (show -κ * T / (2 * Real.pi) - 1 / 2 < κ * T / (2 * Real.pi) - 1 / 2 by
      rw [neg_mul, neg_div]
      linarith)
  have he : κ * T / (2 * Real.pi) - 1 / 2 - (-κ * T / (2 * Real.pi) - 1 / 2) =
      κ * T / Real.pi := by ring
  rw [he] at hh
  exact hh

theorem tendsto_binomialVerticalZeroCount {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun T : ℝ => (binomialVerticalZeroCount κ T : ℝ) / (2 * T)) atTop
      (𝓝 (κ / (2 * Real.pi))) := by
  have hz : Tendsto (fun T : ℝ => (binomialVerticalZeroCount κ T : ℝ) / (2 * T) -
      κ / (2 * Real.pi)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' ?_
      ((tendsto_id.const_mul_atTop (show (0 : ℝ) < 2 by norm_num)).const_div_atTop 1)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T ht
    have hp : 0 < T := by linarith
    have he : (binomialVerticalZeroCount κ T : ℝ) / (2 * T) - κ / (2 * Real.pi) =
        ((binomialVerticalZeroCount κ T : ℝ) - κ * T / Real.pi) / (2 * T) := by
      field_simp
    rw [he, Real.norm_eq_abs, abs_div, abs_of_pos (mul_pos (by norm_num) hp)]
    exact div_le_div_of_nonneg_right (binomialVerticalZeroCount_error hκ hp) (by positivity)
  simpa only [sub_add_cancel, zero_add] using hz.add_const (κ / (2 * Real.pi))

/-- The literal open-strip count, retaining analytic multiplicities. -/
def binomialStripZeroCount (κ l u T : ℝ) : ℕ :=
  ∑ s ∈ (binomialZerosFinset κ T).filter (fun s => l < s.re ∧ s.re < u),
    analyticOrderNatAt (binomialDirichlet κ) s

theorem binomialStripZeroCount_eq {κ : ℝ} (hκ : 0 < κ) (l u T : ℝ) :
    binomialStripZeroCount κ l u T =
      if l < 0 ∧ 0 < u then binomialVerticalZeroCount κ T else 0 := by
  classical
  have hr (s : ℂ) (hs : s ∈ binomialZerosFinset κ T) : s.re = 0 := by
    obtain ⟨m, rfl⟩ := (binomialDirichlet_zero_iff hκ.ne' s).mp
      ((mem_binomialZerosFinset hκ T s).mp hs).2
    exact binomialZero_re κ m
  by_cases h : l < 0 ∧ 0 < u
  · have he : (binomialZerosFinset κ T).filter (fun s => l < s.re ∧ s.re < u) =
        binomialZerosFinset κ T := by
      apply Finset.filter_eq_self.mpr
      intro s hs
      rwa [hr s hs]
    simp only [binomialStripZeroCount, he, if_pos h, binomialVerticalZeroCount]
  · have he : (binomialZerosFinset κ T).filter (fun s => l < s.re ∧ s.re < u) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs
      rwa [hr s hs]
    simp only [binomialStripZeroCount, he, Finset.sum_empty, if_neg h]

theorem tendsto_binomialStripZeroCount {κ : ℝ} (hκ : 0 < κ) (l u : ℝ) :
    Tendsto (fun T : ℝ => (binomialStripZeroCount κ l u T : ℝ) / (2 * T)) atTop
      (𝓝 (if l < 0 ∧ 0 < u then κ / (2 * Real.pi) else 0)) := by
  by_cases h : l < 0 ∧ 0 < u
  · simpa only [binomialStripZeroCount_eq hκ, if_pos h] using tendsto_binomialVerticalZeroCount hκ
  · simpa only [binomialStripZeroCount_eq hκ, if_neg h, Nat.cast_zero, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))

theorem binomial_open_strip_frequency {κ : ℝ} (hκ : 0 < κ) (l u : ℝ) :
    Tendsto (fun T : ℝ => (binomialStripZeroCount κ l u T : ℝ) / (2 * T)) atTop
      (𝓝 (((ENNReal.ofReal (1 / (2 * Real.pi)) • binomialJessenMeasure hκ)
        (Ioo l u)).toReal)) := by
  rw [scaled_binomialJessenMeasure_eq_dirac, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.dirac_apply' _ measurableSet_Ioo]
  have hp : 0 ≤ κ / (2 * Real.pi) := by positivity
  by_cases h : l < 0 ∧ 0 < u <;>
    simpa [Set.indicator_apply, h, ENNReal.toReal_ofReal hp] using
      tendsto_binomialStripZeroCount hκ l u

end

end Dubon2026
