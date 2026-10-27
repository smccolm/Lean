import Dubon2026.SourceGammaOneAnalyticOrder

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> genuine
normalized analytic places. The existing transcendental j coordinate
proves nontriviality of the actual order map. No local ramification
profile or place dictionary is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter
open scoped Topology

theorem exists_analyticOrder_pos {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hT : ModularGroup.T ∈ Γ) (τ : ℍ) :
    ∃ x : functionFieldOver Γ ℂ,
      0 < analyticOrder Γ τ x ∧ analyticOrder Γ τ x ≠ ⊤ := by
  have hjc : ∀ c : ℂ, jCoordinateOver Γ ℂ ≠ algebraMap ℂ (functionFieldOver Γ ℂ) c := by
    intro c he
    apply transcendental_jCoordinateOver Γ ℂ
    rw [he]
    exact isAlgebraic_algebraMap c
  have hj0 : jCoordinateOver Γ ℂ ≠ 0 := by simpa only [map_zero] using hjc 0
  have hjt := analyticOrder_ne_top hT τ hj0
  by_cases hneg : analyticOrder Γ τ (jCoordinateOver Γ ℂ) < 0
  · refine ⟨(jCoordinateOver Γ ℂ)⁻¹, ?_, analyticOrder_ne_top hT τ (inv_ne_zero hj0)⟩
    have hsum : analyticOrder Γ τ (jCoordinateOver Γ ℂ)⁻¹ +
        analyticOrder Γ τ (jCoordinateOver Γ ℂ) = 0 := by
      rw [← analyticOrder_mul hT, inv_mul_cancel₀ hj0, analyticOrder_one hT]
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hjt
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
      (analyticOrder_ne_top hT τ (inv_ne_zero hj0))
    rw [← hm, ← hn, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_eq_coe] at hsum
    rw [← hm, ← WithTop.coe_zero, WithTop.coe_lt_coe] at hneg
    rw [← hn, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    omega
  · rw [not_lt] at hneg
    obtain ⟨c, hc⟩ := (tendsto_nhds_iff_meromorphicOrderAt_nonneg
      (meromorphicAt_realize hT (jCoordinateOver Γ ℂ) τ)).mpr hneg
    refine ⟨jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c, ?_,
      analyticOrder_ne_top hT τ (sub_ne_zero.mpr (hjc c))⟩
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (meromorphicAt_realize hT _ τ)).mp
    have hlim : Tendsto
        ((fun z : ℂ => realize Γ (jCoordinateOver Γ ℂ : LaurentSeries ℂ) (ofComplex z)) + fun _ => -c)
        (𝓝[≠] (τ : ℂ)) (𝓝 0) := by
      simpa using hc.add (tendsto_const_nhds (x := -c))
    refine hlim.congr' ?_
    have he : jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c =
        jCoordinateOver Γ ℂ + algebraMap ℂ (functionFieldOver Γ ℂ) (-c) := by
      rw [map_neg, sub_eq_add_neg]
    rw [he]
    exact ((realize_add_eventuallyEq hT (jCoordinateOver Γ ℂ)
      (algebraMap ℂ (functionFieldOver Γ ℂ) (-c)) τ).trans
        (EventuallyEq.rfl.add (Eventually.of_forall fun z => realize_algebraMap hT (-c) (ofComplex z)))).symm

end
end Dubon2026.SourceFunctionField.GammaOne
