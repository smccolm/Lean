import Dubon2026.SourceCurveAnalyticChartOrders

/-! DUB-17/18 -> auxiliary cover chart compatibility -> uniformizer transition.
Adapt the existing original-curve comparison to the actual cover residue map.
The data contain normalized reading orders and a shared place, not equality
of chart branches. Repeated uniformizer division will establish that equality.
The original comparison was adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex. -/
namespace Dubon2026.SourceCurve.AnalyticChart
noncomputable section
open Filter
open scoped Topology
variable {EE : Type*} [Field EE] [Algebra ℂ EE]

/-- Two actual place families with proved local normalized-order properties at a common place. -/
structure ComparisonData (hv : ∀ P : Place ℂ EE, Function.Bijective (algebraMap ℂ P.ResidueField)) where
  /-- The first actual actual place family. -/
  γ : ℂ → Place ℂ EE
  /-- The second actual actual place family. -/
  γ' : ℂ → Place ℂ EE
  /-- The actual place whose uniformizer gives the first coordinate. -/
  v : Place ℂ EE
  /-- The first parameter domain. -/
  U : Set ℂ
  /-- The second parameter domain. -/
  U' : Set ℂ
  /-- The first coordinate of the common actual place. -/
  z₀ : ℂ
  /-- The second coordinate of the common actual place. -/
  z₀' : ℂ
  hU : U ∈ 𝓝 z₀
  hU' : U' ∈ 𝓝 z₀'
  h₀ : γ' z₀' = γ z₀
  ht : ∀ z ∈ U, (γ z).ord (v.uniformizer - algebraMap ℂ _ z) = 1
  hγ : Orders hv γ U
  hγ' : Orders hv γ' U'

namespace ComparisonData
variable {hv : ∀ P : Place ℂ EE, Function.Bijective (algebraMap ℂ P.ResidueField)} (S : ComparisonData hv)

/-- The actual uniformizer value in the second actual place family. -/
def transition (u : ℂ) : ℂ := (S.γ' u).rationalEval (hv (S.γ' u)) S.v.uniformizer

/-- The difference of the actual two residue-value functions under the transition candidate. -/
def difference (f : EE) (u : ℂ) : ℂ :=
  (S.γ' u).rationalEval (hv (S.γ' u)) f - (S.γ (S.transition u)).rationalEval (hv (S.γ (S.transition u))) f

theorem sub_ne_zero : S.v.uniformizer - algebraMap ℂ EE S.z₀ ≠ 0 := by
  intro h
  have ht := S.ht S.z₀ (mem_of_mem_nhds S.hU)
  rw [h, (S.γ S.z₀).ord_zero] at ht
  exact zero_ne_one ht

theorem uniformizer_mem : S.v.uniformizer ∈ (S.γ S.z₀).toValuationSubring := by
  have hm : S.v.uniformizer - algebraMap ℂ EE S.z₀ ∈
      (S.γ S.z₀).toValuationSubring :=
    (S.γ S.z₀).mem_of_ord_nonneg (by rw [S.ht S.z₀ (mem_of_mem_nhds S.hU)]; norm_num)
  simpa only [sub_add_cancel] using add_mem hm ((S.γ S.z₀).algebraMap_mem' S.z₀)

theorem transition_self : S.transition S.z₀' = S.z₀ := by
  simp only [transition, S.h₀]
  exact (S.γ S.z₀).rationalEval_eq_of_ord_sub_pos (hv (S.γ S.z₀)) S.v.uniformizer S.z₀
    (by rw [S.ht S.z₀ (mem_of_mem_nhds S.hU)]; norm_num)

theorem analyticAt_transition : AnalyticAt ℂ S.transition S.z₀' :=
  S.hγ'.analyticAt (mem_of_mem_nhds S.hU') (by rw [S.h₀]; exact S.uniformizer_mem)

theorem tendsto_transition : Tendsto S.transition (𝓝 S.z₀') (𝓝 S.z₀) := by
  simpa only [S.transition_self] using S.analyticAt_transition.continuousAt.tendsto

theorem order_transition : meromorphicOrderAt (fun u => S.transition u - S.z₀) S.z₀' = (1 : ℤ) := by
  have h := S.hγ'.meromorphicOrderAt_sub_const S.hU'
    (by rw [S.h₀]; exact S.uniformizer_mem) S.z₀ S.sub_ne_zero
  rw [S.h₀, S.ht S.z₀ (mem_of_mem_nhds S.hU)] at h
  exact h

theorem eventually_mem' {f : EE}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∀ᶠ u in 𝓝 S.z₀', f ∈ (S.γ' u).toValuationSubring :=
  S.hγ'.eventually_mem S.hU' (by rw [S.h₀]; exact hf)

theorem eventually_mem {f : EE}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∀ᶠ u in 𝓝 S.z₀', f ∈ (S.γ (S.transition u)).toValuationSubring :=
  S.tendsto_transition.eventually (S.hγ.eventually_mem S.hU hf)

theorem analyticAt_difference {f : EE}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) : AnalyticAt ℂ (S.difference f) S.z₀' := by
  have h1 := S.hγ'.analyticAt (mem_of_mem_nhds S.hU') (S.h₀ ▸ hf)
  have h2 : AnalyticAt ℂ (fun u => (S.γ u).rationalEval (hv (S.γ u)) f) (S.transition S.z₀') := by
    rw [S.transition_self]
    exact S.hγ.analyticAt (mem_of_mem_nhds S.hU) hf
  exact h1.sub (h2.comp S.analyticAt_transition)

theorem decomp {f : EE} (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∃ f₁ ∈ (S.γ S.z₀).toValuationSubring,
      f = algebraMap ℂ _ ((S.γ S.z₀).rationalEval (hv (S.γ S.z₀)) f) +
        (S.v.uniformizer - algebraMap ℂ _ S.z₀) * f₁ := by
  let c := (S.γ S.z₀).rationalEval (hv (S.γ S.z₀)) f
  refine ⟨(f - algebraMap ℂ _ c) / (S.v.uniformizer - algebraMap ℂ _ S.z₀), ?_, ?_⟩
  · by_cases hfc : f - algebraMap ℂ EE c = 0
    · rw [hfc, zero_div]
      exact zero_mem _
    have hpos : 0 < (S.γ S.z₀).ord (f - algebraMap ℂ _ c) := by
      apply ((S.γ S.z₀).rationalEval_eq_zero_iff_ord_pos (hv (S.γ S.z₀))
        (sub_mem hf ((S.γ S.z₀).algebraMap_mem' c)) hfc).mp
      rw [(S.γ S.z₀).rationalEval_sub_algebraMap (hv (S.γ S.z₀)) hf c]
      exact sub_self c
    apply (S.γ S.z₀).mem_of_ord_nonneg
    rw [div_eq_mul_inv, (S.γ S.z₀).ord_mul hfc (inv_ne_zero S.sub_ne_zero),
      (S.γ S.z₀).ord_inv, S.ht S.z₀ (mem_of_mem_nhds S.hU)]
    omega
  · rw [mul_div_cancel₀ _ S.sub_ne_zero]
    ring

end ComparisonData
end
end Dubon2026.SourceCurve.AnalyticChart
