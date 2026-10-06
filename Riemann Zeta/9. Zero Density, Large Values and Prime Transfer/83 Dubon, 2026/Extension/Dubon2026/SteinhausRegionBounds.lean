import Dubon2026.SteinhausLaw
import Dubon2026.BesselDecay
import Mathlib.Topology.Order.Compact

/-! # Pointwise bounds for the three characteristic-function regions -/

namespace Dubon2026

open MeasureTheory Set
open scoped BigOperators

theorem exists_besselJ0_compact_gap {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ u ∈ Icc a b, |besselJ0 u| ≤ ρ := by
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hab)
    continuous_besselJ0.abs.continuousOn
  exact ⟨|besselJ0 u|, abs_nonneg _, abs_besselJ0_lt_one (ha.trans_le hu.1).ne', hmax⟩

theorem bessel_product_gaussian {ι : Type*} [Fintype ι] (c : ι → ℝ) (r : ℝ)
    (henergy : ∑ i, c i ^ 2 = 1) (hsmall : ∀ i, |c i * r| ≤ 1) :
    (∏ i, |besselJ0 (c i * r)|) ≤ Real.exp (-r ^ 2 / Real.pi ^ 2) := by
  calc
    _ ≤ ∏ i, Real.exp (-(c i * r) ^ 2 / Real.pi ^ 2) :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => abs_besselJ0_le_gaussian (hsmall i))
    _ = Real.exp (∑ i, -(c i * r) ^ 2 / Real.pi ^ 2) := (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      calc
        _ = (-r ^ 2 / Real.pi ^ 2) * ∑ i, c i ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [henergy, mul_one]

theorem norm_charFun_steinhaus_small {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (ξ : ℂ)
    (henergy : ∑ i, c i ^ 2 = 1) (hsmall : ∀ i, |c i * ‖ξ‖| ≤ 1) :
    ‖charFun (steinhausLaw c) ξ‖ ≤ Real.exp (-‖ξ‖ ^ 2 / Real.pi ^ 2) := by
  rw [norm_charFun_steinhausLaw c hc]
  exact bessel_product_gaussian c ‖ξ‖ henergy hsmall

theorem bessel_product_compact_bound {ι : Type*} [Fintype ι] (c : ι → ℝ) (r ρ a b : ℝ)
    (hgap : ∀ u ∈ Icc a b, |besselJ0 u| ≤ ρ) (hargs : ∀ i, c i * r ∈ Icc a b) :
    (∏ i, |besselJ0 (c i * r)|) ≤ ρ ^ Fintype.card ι := by
  calc
    _ ≤ ∏ _i : ι, ρ :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hgap _ (hargs i))
    _ = _ := by simp

theorem bessel_product_tail_bound {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {r a : ℝ} (ha : 0 < a) (hr : 0 < r) (hc : ∀ i, a ≤ c i) (har : 1 ≤ a * r) :
    (∏ i, |besselJ0 (c i * r)|) ≤
      ((4 + 1 / Real.pi) / Real.sqrt (a * r)) ^ Fintype.card ι := by
  have hpoint (i : ι) : |besselJ0 (c i * r)| ≤ (4 + 1 / Real.pi) / Real.sqrt (a * r) := by
    have hai : a * r ≤ c i * r := mul_le_mul_of_nonneg_right (hc i) hr.le
    exact (abs_besselJ0_le_inv_sqrt (har.trans hai)).trans
      (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.2 (mul_pos ha hr))
        (Real.sqrt_le_sqrt hai))
  calc
    _ ≤ ∏ _i : ι, (4 + 1 / Real.pi) / Real.sqrt (a * r) :=
      Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hpoint i)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ]

end Dubon2026
