import Dubon2026.SourceOriginalChartEvaluation

/-! DUB-17/18 -> original torsion cardinality -> compatibility of
actual complex-place parameters. The inputs are the pointwise order and
regularity properties constructed for the original parameter families.
They imply that evaluation of the other uniformizer is an analytic
transition candidate with order one. Local compatibility is still to be
proved from this data, and is not a field of the data structure.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Filter SourceCurve
open scoped Topology

theorem originalPlaceEval_decomp (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    {t f : modularFunctionFieldOver N ℂ}
    (ht : t ∈ v.toValuationSubring) (hf : f ∈ v.toValuationSubring) (c z : ℂ) :
    originalPlaceEval N ℂ v (algebraMap ℂ _ c + (t - algebraMap ℂ _ z) * f) =
      c + (originalPlaceEval N ℂ v t - z) * originalPlaceEval N ℂ v f := by
  rw [originalPlaceEval_of_mem N ℂ v
    (add_mem (v.algebraMap_mem' c) (mul_mem (sub_mem ht (v.algebraMap_mem' z)) hf)),
    originalPlaceEval_of_mem N ℂ v ht, originalPlaceEval_of_mem N ℂ v hf]
  change originalPlaceRegularEval N ℂ v
    (algebraMap ℂ v.toValuationSubring c +
      (⟨t, ht⟩ - algebraMap ℂ v.toValuationSubring z) * ⟨f, hf⟩) = _
  rw [map_add, map_mul, map_sub, originalPlaceRegularEval_algebraMap,
    originalPlaceRegularEval_algebraMap]

namespace OriginalChart

/-- Two original place families with proved local normalized-order properties at a common place. -/
structure ComparisonData (N : ℕ) [NeZero N] where
  /-- The first actual original place family. -/
  γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)
  /-- The second actual original place family. -/
  γ' : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)
  /-- The original place whose uniformizer gives the first coordinate. -/
  v : Place ℂ (modularFunctionFieldOver N ℂ)
  /-- The first parameter domain. -/
  U : Set ℂ
  /-- The second parameter domain. -/
  U' : Set ℂ
  /-- The first coordinate of the common original place. -/
  z₀ : ℂ
  /-- The second coordinate of the common original place. -/
  z₀' : ℂ
  hU : U ∈ 𝓝 z₀
  hU' : U' ∈ 𝓝 z₀'
  h₀ : γ' z₀' = γ z₀
  ht : ∀ z ∈ U, (γ z).ord (v.uniformizer - algebraMap ℂ _ z) = 1
  hγ : Orders N γ U
  hγ' : Orders N γ' U'

namespace ComparisonData
variable {N : ℕ} [NeZero N] (S : ComparisonData N)

/-- The actual uniformizer value in the second original place family. -/
def transition (u : ℂ) : ℂ := originalPlaceEval N ℂ (S.γ' u) S.v.uniformizer

/-- The difference of the actual two residue-value functions under the transition candidate. -/
def difference (f : modularFunctionFieldOver N ℂ) (u : ℂ) : ℂ :=
  originalPlaceEval N ℂ (S.γ' u) f - originalPlaceEval N ℂ (S.γ (S.transition u)) f

theorem sub_ne_zero : S.v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) S.z₀ ≠ 0 := by
  intro h
  have ht := S.ht S.z₀ (mem_of_mem_nhds S.hU)
  rw [h, (S.γ S.z₀).ord_zero] at ht
  exact zero_ne_one ht

theorem uniformizer_mem : S.v.uniformizer ∈ (S.γ S.z₀).toValuationSubring := by
  have hm : S.v.uniformizer - algebraMap ℂ (modularFunctionFieldOver N ℂ) S.z₀ ∈
      (S.γ S.z₀).toValuationSubring :=
    (S.γ S.z₀).mem_of_ord_nonneg (by rw [S.ht S.z₀ (mem_of_mem_nhds S.hU)]; norm_num)
  simpa only [sub_add_cancel] using add_mem hm ((S.γ S.z₀).algebraMap_mem' S.z₀)

theorem transition_self : S.transition S.z₀' = S.z₀ := by
  rw [transition, S.h₀]
  exact originalPlaceEval_eq_of_ord_sub_pos N ℂ (S.γ S.z₀) S.v.uniformizer S.z₀
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

theorem eventually_mem' {f : modularFunctionFieldOver N ℂ}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∀ᶠ u in 𝓝 S.z₀', f ∈ (S.γ' u).toValuationSubring :=
  S.hγ'.eventually_mem S.hU' (by rw [S.h₀]; exact hf)

theorem eventually_mem {f : modularFunctionFieldOver N ℂ}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∀ᶠ u in 𝓝 S.z₀', f ∈ (S.γ (S.transition u)).toValuationSubring :=
  S.tendsto_transition.eventually (S.hγ.eventually_mem S.hU hf)

theorem analyticAt_difference {f : modularFunctionFieldOver N ℂ}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) : AnalyticAt ℂ (S.difference f) S.z₀' := by
  have h1 := S.hγ'.analyticAt (mem_of_mem_nhds S.hU') (S.h₀ ▸ hf)
  have h2 : AnalyticAt ℂ (fun u => originalPlaceEval N ℂ (S.γ u) f) (S.transition S.z₀') := by
    rw [S.transition_self]
    exact S.hγ.analyticAt (mem_of_mem_nhds S.hU) hf
  exact h1.sub (h2.comp S.analyticAt_transition)

theorem decomp {f : modularFunctionFieldOver N ℂ} (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∃ f₁ ∈ (S.γ S.z₀).toValuationSubring,
      f = algebraMap ℂ _ (originalPlaceEval N ℂ (S.γ S.z₀) f) +
        (S.v.uniformizer - algebraMap ℂ _ S.z₀) * f₁ := by
  let c := originalPlaceEval N ℂ (S.γ S.z₀) f
  refine ⟨(f - algebraMap ℂ _ c) / (S.v.uniformizer - algebraMap ℂ _ S.z₀), ?_, ?_⟩
  · by_cases hfc : f - algebraMap ℂ (modularFunctionFieldOver N ℂ) c = 0
    · rw [hfc, zero_div]
      exact zero_mem _
    have hpos : 0 < (S.γ S.z₀).ord (f - algebraMap ℂ _ c) := by
      apply (originalPlaceEval_eq_zero_iff_ord_pos N ℂ (S.γ S.z₀)
        (sub_mem hf ((S.γ S.z₀).algebraMap_mem' c)) hfc).mp
      rw [originalPlaceEval_sub_algebraMap N ℂ (S.γ S.z₀) hf c]
      exact sub_self c
    apply (S.γ S.z₀).mem_of_ord_nonneg
    rw [div_eq_mul_inv, (S.γ S.z₀).ord_mul hfc (inv_ne_zero S.sub_ne_zero),
      (S.γ S.z₀).ord_inv, S.ht S.z₀ (mem_of_mem_nhds S.hU)]
    omega
  · rw [mul_div_cancel₀ _ S.sub_ne_zero]
    ring

end ComparisonData
end OriginalChart
end
end Dubon2026.SourceFunctionField
