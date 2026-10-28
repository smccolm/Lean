import Dubon2026.SourceCuspVanishingOrder
import Mathlib.Analysis.Meromorphic.NormalForm

/-! DUB17/18 -> actual Gamma1 Picard/H1 -> principal-divisor converse ->
actual meromorphic construction -> cusp decay of a coefficient with interior
poles. Positive cusp order suffices. Native meromorphic normalization and
the first derivative bound give O(q), then the exact q-parameter norm gives
exponential decay. No global holomorphy hypothesis is introduced. -/
namespace Dubon2026.SourceMeromorphicCuspDecay
noncomputable section
open UpperHalfPlane Filter
open scoped Topology

theorem exp_decay_of_cusp_order_pos {F : ℍ → ℂ} {h : ℝ}
    (hh : 0 < h) (hper : Function.Periodic (F ∘ ofComplex) h)
    (hm : MeromorphicAt (cuspFunction h F) 0)
    (ho : 0 < meromorphicOrderAt (cuspFunction h F) 0) :
    F =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im / h) := by
  let G := toMeromorphicNFAt (cuspFunction h F) 0
  have he : cuspFunction h F =ᶠ[𝓝[≠] (0 : ℂ)] G := hm.eq_nhdsNE_toMeromorphicNFAt
  have hNF : MeromorphicNFAt G 0 := meromorphicNFAt_toMeromorphicNFAt
  have hGo : 0 < meromorphicOrderAt G 0 := by
    rw [meromorphicOrderAt_congr he.symm]
    exact ho
  have hGa : AnalyticAt ℂ G 0 :=
    hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hGo.le
  have hG0 : G 0 = 0 :=
    tendsto_nhds_unique (hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_zero_of_meromorphicOrderAt_pos hGo)
  have hOG : G =O[𝓝[≠] (0 : ℂ)] fun z : ℂ => z := by
    simpa only [hG0, sub_zero] using
      (hGa.differentiableAt.isBigO_sub.mono nhdsWithin_le_nhds)
  have hOF : cuspFunction h F =O[𝓝[≠] (0 : ℂ)] fun z : ℂ => z :=
    hOG.congr' he.symm Filter.EventuallyEq.rfl
  have hq := (Function.Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty
  have hO := (hOF.comp_tendsto hq).norm_right
  simpa only [Function.comp_def, Function.Periodic.norm_qParam,
    eq_cuspFunction _ hh.ne' hper] using hO

end
end Dubon2026.SourceMeromorphicCuspDecay
