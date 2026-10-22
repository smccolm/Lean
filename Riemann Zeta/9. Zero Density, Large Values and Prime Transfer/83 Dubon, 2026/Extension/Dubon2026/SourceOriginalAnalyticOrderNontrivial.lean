import Dubon2026.SourceOriginalAnalyticOrder

/-! DUB-17/18 -> genuine normalized analytic places. The original
transcendental j-coordinate makes the proved meromorphic order map
nontrivial at every complex point. At a pole use its inverse; otherwise
subtract its finite limit. The resulting nonzero original element has
strictly positive finite order. This discharges the nontrivial-valuation
input without assuming an analytic place or a local j-ramification bound.
Adapted from the exists_mu_pos argument in anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_complexPlaceDictionary.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology

theorem exists_originalAnalyticOrder_pos (N : ℕ) [NeZero N] (τ : ℍ) :
    ∃ x : modularFunctionFieldOver N ℂ,
      0 < originalAnalyticOrder N τ x ∧ originalAnalyticOrder N τ x ≠ ⊤ := by
  have hjc : ∀ c : ℂ, jOver N ℂ ≠ algebraMap ℂ (modularFunctionFieldOver N ℂ) c := by
    intro c he
    apply transcendental_jOver N ℂ
    rw [he]
    exact isAlgebraic_algebraMap c
  have hj0 : jOver N ℂ ≠ 0 := by simpa only [map_zero] using hjc 0
  have hjt := originalAnalyticOrder_ne_top N τ hj0
  by_cases hneg : originalAnalyticOrder N τ (jOver N ℂ) < 0
  · refine ⟨(jOver N ℂ)⁻¹, ?_, originalAnalyticOrder_ne_top N τ (inv_ne_zero hj0)⟩
    have hsum : originalAnalyticOrder N τ (jOver N ℂ)⁻¹ +
        originalAnalyticOrder N τ (jOver N ℂ) = 0 := by
      rw [← originalAnalyticOrder_mul, inv_mul_cancel₀ hj0, originalAnalyticOrder_one]
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hjt
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
      (originalAnalyticOrder_ne_top N τ (inv_ne_zero hj0))
    rw [← hm, ← hn, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hsum
    rw [← hm, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hneg
    rw [← hn, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    omega
  · rw [not_lt] at hneg
    obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg
      (meromorphicAt_original_realize N (jOver N ℂ) τ)).mpr hneg
    refine ⟨jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c, ?_,
      originalAnalyticOrder_ne_top N τ (sub_ne_zero.mpr (hjc c))⟩
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (meromorphicAt_original_realize N _ τ)).mp
    have hlim : Tendsto
        ((fun z : ℂ => realize N (jOver N ℂ : LaurentSeries ℂ) (ofComplex z)) + fun _ => -c)
        (𝓝[≠] (τ : ℂ)) (𝓝 0) := by
      simpa using hc.add (tendsto_const_nhds (x := -c))
    refine hlim.congr' ?_
    have he : jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) c =
        jOver N ℂ + algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c) := by
      rw [map_neg, sub_eq_add_neg]
    rw [he]
    exact ((original_realize_add_eventuallyEq N (jOver N ℂ)
      (algebraMap ℂ (modularFunctionFieldOver N ℂ) (-c)) τ).trans
        (EventuallyEq.rfl.add (Eventually.of_forall fun z => realize_algebraMap N (-c) (ofComplex z)))).symm

end
end Dubon2026.SourceFunctionField
