import Dubon2026.SourceCurveRationalChartValues
import Mathlib.Analysis.Meromorphic.Order

/-! DUB-17/18 -> auxiliary cover chart compatibility -> local reading orders.
This is the exact order/regularity property supplied by the actual cover
parameter theorem. It derives nearby regularity and order-one uniformizer
differences; it does not assume overlap compatibility. -/
namespace Dubon2026.SourceCurve.AnalyticChart
noncomputable section
open Filter
open scoped Topology
variable {EE : Type*} [Field EE] [Algebra ℂ EE]

/-- Exact order and regularity of the actual rational evaluation along a specified place family. -/
def Orders (hv : ∀ P : Place ℂ EE, Function.Bijective (algebraMap ℂ P.ResidueField)) (γ : ℂ → Place ℂ EE) (U : Set ℂ) : Prop :=
  ∀ z ∈ U, ∀ f : EE, f ≠ 0 →
    MeromorphicAt (fun t => (γ t).rationalEval (hv (γ t)) f) z ∧
    meromorphicOrderAt (fun t => (γ t).rationalEval (hv (γ t)) f) z = (γ z).ord f ∧
    (f ∈ (γ z).toValuationSubring → AnalyticAt ℂ (fun t => (γ t).rationalEval (hv (γ t)) f) z)

variable {hv : ∀ P : Place ℂ EE, Function.Bijective (algebraMap ℂ P.ResidueField)} {γ : ℂ → Place ℂ EE}
variable {U : Set ℂ} {z : ℂ}

theorem Orders.analyticAt (h : Orders hv γ U) (hz : z ∈ U) {f : EE}
    (hf : f ∈ (γ z).toValuationSubring) : AnalyticAt ℂ (fun t => (γ t).rationalEval (hv (γ t)) f) z := by
  by_cases hf0 : f = 0
  · subst f
    simp only [Place.rationalEval_zero]
    exact analyticAt_const
  exact (h z hz f hf0).2.2 hf

theorem Orders.eventually_mem (h : Orders hv γ U) (hU : U ∈ 𝓝 z)
    {f : EE} (hf : f ∈ (γ z).toValuationSubring) :
    ∀ᶠ u in 𝓝 z, f ∈ (γ u).toValuationSubring := by
  by_cases hf0 : f = 0
  · subst f
    exact Eventually.of_forall fun u => zero_mem (γ u).toValuationSubring
  filter_upwards [(h.analyticAt (mem_of_mem_nhds hU) hf).eventually_analyticAt, hU] with u hu huU
  have hn := hu.meromorphicOrderAt_nonneg
  rw [(h u huU f hf0).2.1] at hn
  exact (γ u).mem_of_ord_nonneg (by exact_mod_cast hn)

theorem Orders.meromorphicOrderAt_sub_const (h : Orders hv γ U) (hU : U ∈ 𝓝 z)
    {f : EE} (hf : f ∈ (γ z).toValuationSubring) (c : ℂ)
    (hfc : f - algebraMap ℂ EE c ≠ 0) :
    meromorphicOrderAt (fun u => (γ u).rationalEval (hv (γ u)) f - c) z =
      ((γ z).ord (f - algebraMap ℂ EE c) : WithTop ℤ) := by
  rw [← (h z (mem_of_mem_nhds hU) _ hfc).2.1]
  apply meromorphicOrderAt_congr
  exact ((h.eventually_mem hU hf).mono fun u hu =>
    ((γ u).rationalEval_sub_algebraMap (hv (γ u)) hu c).symm).filter_mono nhdsWithin_le_nhds

theorem Orders.uniformizer_sub_order (h : Orders hv γ U) (hU : U ∈ 𝓝 z)
    (v : Place ℂ EE)
    (heval : ∀ u ∈ U, (γ u).rationalEval (hv (γ u)) v.uniformizer = u) :
    (γ z).ord (v.uniformizer - algebraMap ℂ EE z) = 1 := by
  have he : (fun u => (γ u).rationalEval (hv (γ u)) v.uniformizer) =ᶠ[𝓝 z] id := by
    filter_upwards [hU] with u hu
    exact heval u hu
  have ha : AnalyticAt ℂ (fun u => (γ u).rationalEval (hv (γ u)) v.uniformizer) z :=
    analyticAt_id.congr he.symm
  have hmem : v.uniformizer ∈ (γ z).toValuationSubring := by
    have hn := ha.meromorphicOrderAt_nonneg
    rw [(h z (mem_of_mem_nhds hU) _ v.uniformizer_ne_zero).2.1] at hn
    exact (γ z).mem_of_ord_nonneg (by exact_mod_cast hn)
  have hfc : v.uniformizer - algebraMap ℂ EE z ≠ 0 := by
    intro h0
    have hvord := v.ord_uniformizer
    rw [sub_eq_zero.mp h0, v.ord_algebraMap] at hvord
    exact zero_ne_one hvord

  have ho := h.meromorphicOrderAt_sub_const hU hmem z hfc
  have he' : (fun u => (γ u).rationalEval (hv (γ u)) v.uniformizer - z) =ᶠ[𝓝[≠] z]
      (fun u : ℂ => u - z) := (he.mono fun u hu => congrArg (fun a => a - z) hu).filter_mono nhdsWithin_le_nhds
  rw [meromorphicOrderAt_congr he', meromorphicOrderAt_id_sub_const] at ho
  exact WithTop.coe_injective ho.symm

end
end Dubon2026.SourceCurve.AnalyticChart
