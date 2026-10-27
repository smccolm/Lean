import Dubon2026.SourceMeromorphicCuspPoleClearing

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> cusp stability. Vanishing at infinity is exactly positive meromorphic
cusp order for an actual holomorphic periodic function. This reuses native
meromorphic order and limit theorems instead of a separate coefficient
threshold engine. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField Filter
open scoped Topology Manifold

theorem isZeroAtImInfty_iff_cusp_order_pos {h : ℝ} {F : ℍ → ℂ}
    (hh : 0 < h) (hf : MDiff F) (hper : Function.Periodic (F ∘ ofComplex) h) :
    IsZeroAtImInfty F ↔ 0 < meromorphicOrderAt (cuspFunction h F) 0 := by
  constructor
  · intro hz
    have ha := analyticAt_cuspFunction_zero hh hper hf hz.isBoundedAtImInfty
    apply (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
    have ht := (ha.continuousAt.continuousWithinAt (s := ({0}ᶜ : Set ℂ))).tendsto
    rw [hz.cuspFunction_apply_zero hh] at ht
    exact ht
  · intro ho
    have ht := (tendsto_zero_of_meromorphicOrderAt_pos ho).comp
      ((Function.Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty)
    change Tendsto F atImInfty (𝓝 0)
    convert ht using 1
    funext τ
    exact (eq_cuspFunction τ hh.ne' hper).symm

end
end Dubon2026.SourceFricke