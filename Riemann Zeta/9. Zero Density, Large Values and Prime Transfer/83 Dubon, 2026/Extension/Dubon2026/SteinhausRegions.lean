import Dubon2026.SteinhausRegionBounds
import Dubon2026.SteinhausNormalization

/-! # The paper's region cutoffs for the actual normalized coefficient vector -/

namespace Dubon2026

open MeasureTheory Set
open scoped BigOperators

theorem exists_besselJ0_comparable_gap {K R : ℝ} (hK : 1 ≤ K) (hR : 1 ≤ R) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ u ∈ Icc (1 / K ^ 2) (R * K ^ 2), |besselJ0 u| ≤ ρ := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hK2 : 1 ≤ K ^ 2 := by nlinarith
  apply exists_besselJ0_compact_gap (by positivity)
  calc
    1 / K ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hK0)).2 hK2
    _ ≤ R * K ^ 2 := by nlinarith

theorem comparable_argument_small {c K m r : ℝ} (hK : 0 < K) (hm : 0 < m)
    (hc : 0 ≤ c) (hcupper : c ≤ K / Real.sqrt m) (hr : 0 ≤ r)
    (hrupper : r ≤ Real.sqrt m / K) : |c * r| ≤ 1 := by
  rw [abs_of_nonneg (mul_nonneg hc hr)]
  calc
    c * r ≤ (K / Real.sqrt m) * (Real.sqrt m / K) :=
      mul_le_mul hcupper hrupper hr (by positivity)
    _ = 1 := by field_simp

theorem comparable_argument_middle {c K R m r : ℝ} (hK : 0 < K) (hm : 0 < m)
    (hclower : 1 / (K * Real.sqrt m) ≤ c)
    (hcupper : c ≤ K / Real.sqrt m) (hrlower : Real.sqrt m / K ≤ r)
    (hrupper : r ≤ R * K * Real.sqrt m) : c * r ∈ Icc (1 / K ^ 2) (R * K ^ 2) := by
  have hr : 0 ≤ r := (by positivity : 0 ≤ Real.sqrt m / K).trans hrlower
  have hc : 0 ≤ c := (by positivity : 0 ≤ 1 / (K * Real.sqrt m)).trans hclower
  constructor
  · calc
      1 / K ^ 2 = (1 / (K * Real.sqrt m)) * (Real.sqrt m / K) := by field_simp
      _ ≤ c * r := mul_le_mul hclower hrlower (by positivity) (by positivity)
  · calc
      c * r ≤ (K / Real.sqrt m) * (R * K * Real.sqrt m) :=
        mul_le_mul hcupper hrupper hr (by positivity)
      _ = R * K ^ 2 := by field_simp

theorem comparable_argument_tail {K R m r : ℝ} (hK : 0 < K) (hm : 0 < m)
    (hR : 1 ≤ R) (hr : R * K * Real.sqrt m ≤ r) :
    1 ≤ (1 / (K * Real.sqrt m)) * r := by
  calc
    1 ≤ R := hR
    _ = (1 / (K * Real.sqrt m)) * (R * K * Real.sqrt m) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hr (by positivity)

theorem normalized_steinhaus_three_regions {ι : Type*} [Fintype ι] [Nonempty ι]
    (b : ι → ℝ) (hb : ∀ i, 0 < b i) {K R ρ : ℝ} (hK : 1 ≤ K) (hR : 1 ≤ R)
    (hcomp : steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K)
    (hgap : ∀ u ∈ Icc (1 / K ^ 2) (R * K ^ 2), |besselJ0 u| ≤ ρ) (ξ : ℂ) :
    let c := normalizedSteinhausCoefficients b
    let m : ℝ := Fintype.card ι
    (‖ξ‖ ≤ Real.sqrt m / K →
      ‖charFun (steinhausLaw c) ξ‖ ≤ Real.exp (-‖ξ‖ ^ 2 / Real.pi ^ 2)) ∧
    (Real.sqrt m / K ≤ ‖ξ‖ → ‖ξ‖ ≤ R * K * Real.sqrt m →
      ‖charFun (steinhausLaw c) ξ‖ ≤ ρ ^ Fintype.card ι) ∧
    (R * K * Real.sqrt m ≤ ‖ξ‖ →
      ‖charFun (steinhausLaw c) ξ‖ ≤
        ((4 + 1 / Real.pi) / Real.sqrt ((1 / (K * Real.sqrt m)) * ‖ξ‖)) ^ Fintype.card ι) := by
  let c := normalizedSteinhausCoefficients b
  have hc : ∀ i, 0 ≤ c i := fun i => (normalizedSteinhausCoefficients_pos b hb i).le
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hm : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hbnd := normalizedSteinhausCoefficients_bounds b hb hK
    (steinhaus_pairwise_of_max_min b hb hK hcomp)
  refine ⟨?_, ?_, ?_⟩
  · intro hr
    apply norm_charFun_steinhaus_small c hc ξ (sum_normalizedSteinhausCoefficients_sq b hb)
    intro i
    exact comparable_argument_small hK0 hm (hc i) (hbnd i).2 (norm_nonneg ξ) hr
  · intro hl hu
    rw [norm_charFun_steinhausLaw c hc]
    exact bessel_product_compact_bound c ‖ξ‖ ρ (1 / K ^ 2) (R * K ^ 2) hgap
      (fun i => comparable_argument_middle hK0 hm (hbnd i).1 (hbnd i).2 hl hu)
  · intro hr
    have hr0 : 0 < ‖ξ‖ := (by positivity : 0 < R * K * Real.sqrt (Fintype.card ι)).trans_le hr
    rw [norm_charFun_steinhausLaw c hc]
    exact bessel_product_tail_bound c (by positivity) hr0 (fun i => (hbnd i).1)
      (comparable_argument_tail hK0 hm hR hr)

end Dubon2026
