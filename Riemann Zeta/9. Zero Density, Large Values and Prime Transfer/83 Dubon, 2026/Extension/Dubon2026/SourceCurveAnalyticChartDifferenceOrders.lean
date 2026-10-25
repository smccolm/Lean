import Dubon2026.SourceCurveAnalyticChartComparison

/-! DUB-17/18 -> auxiliary cover Abel comparison -> chart branch compatibility.
Adapt the existing original-curve uniformizer-division and meromorphic
identity argument to the actual cover residue evaluation and place orders.
The original proof was adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_localParam_eventually_eq_comp_evalAt_complex. -/
namespace Dubon2026.SourceCurve.AnalyticChart.ComparisonData
noncomputable section
open Filter
open scoped Topology
variable {EE : Type*} [Field EE] [Algebra ℂ EE]
variable {hv : ∀ P : Place ℂ EE, Function.Bijective (algebraMap ℂ P.ResidueField)}
variable (S : ComparisonData hv)

theorem difference_step {f : EE}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∃ f₁ ∈ (S.γ S.z₀).toValuationSubring,
      S.difference f =ᶠ[𝓝 S.z₀'] fun u => (S.transition u - S.z₀) * S.difference f₁ u := by
  obtain ⟨f₁, hf₁, hdec⟩ := S.decomp hf
  refine ⟨f₁, hf₁, ?_⟩
  filter_upwards [S.eventually_mem' S.uniformizer_mem, S.eventually_mem' hf₁,
    S.eventually_mem S.uniformizer_mem, S.eventually_mem hf₁,
    S.tendsto_transition.eventually S.hU] with u ht' hf₁' ht hf₁u hhu
  have hval : (S.γ (S.transition u)).rationalEval (hv (S.γ (S.transition u))) S.v.uniformizer = S.transition u :=
    (S.γ (S.transition u)).rationalEval_eq_of_ord_sub_pos (hv (S.γ (S.transition u))) S.v.uniformizer _
      (by rw [S.ht _ hhu]; norm_num)
  unfold difference
  conv_lhs => rw [hdec]
  rw [(S.γ' u).rationalEval_decomp (hv (S.γ' u)) ht' hf₁',
    (S.γ (S.transition u)).rationalEval_decomp (hv (S.γ (S.transition u))) ht hf₁u, hval]
  unfold transition
  ring

theorem le_difference_order (m : ℕ) : ∀ {f : EE},
    f ∈ (S.γ S.z₀).toValuationSubring →
      ((m : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (S.difference f) S.z₀' := by
  induction m with
  | zero =>
    intro f hf
    simpa only [Nat.cast_zero, Int.cast_zero] using (S.analyticAt_difference hf).meromorphicOrderAt_nonneg
  | succ m ih =>
    intro f hf
    obtain ⟨f₁, hf₁, heq⟩ := S.difference_step hf
    rw [meromorphicOrderAt_congr (heq.filter_mono nhdsWithin_le_nhds)]
    change (((m + 1 : ℕ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt ((fun u => S.transition u - S.z₀) * S.difference f₁) S.z₀'
    have hmer : MeromorphicAt (fun u => S.transition u - S.z₀) S.z₀' :=
      (S.analyticAt_transition.sub analyticAt_const).meromorphicAt
    rw [meromorphicOrderAt_mul hmer
      (S.analyticAt_difference hf₁).meromorphicAt, S.order_transition]
    calc (((m + 1 : ℕ) : ℤ) : WithTop ℤ) = 1 + ((m : ℤ) : WithTop ℤ) := by
           push_cast
           rw [add_comm]
         _ ≤ 1 + meromorphicOrderAt (S.difference f₁) S.z₀' := by
           rw [add_comm 1, add_comm 1]
           exact add_le_add_left (ih hf₁) 1

theorem difference_order_top_of_mem {f : EE}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    meromorphicOrderAt (S.difference f) S.z₀' = ⊤ := by
  by_contra hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have h := S.le_difference_order (m.toNat + 1) hf
  rw [← hm, WithTop.coe_le_coe] at h
  omega

theorem eventuallyEq_of_mem {f : EE}
    (hf : f ∈ (S.γ S.z₀).toValuationSubring) :
    ∀ᶠ u in 𝓝[≠] S.z₀', (S.γ' u).rationalEval (hv (S.γ' u)) f =
      (S.γ (S.transition u)).rationalEval (hv (S.γ (S.transition u))) f :=
  (meromorphicOrderAt_eq_top_iff.mp (S.difference_order_top_of_mem hf)).mono fun _ hu => sub_eq_zero.mp hu

theorem eventuallyEq (f : EE) :
    ∀ᶠ u in 𝓝[≠] S.z₀', (S.γ' u).rationalEval (hv (S.γ' u)) f =
      (S.γ (S.transition u)).rationalEval (hv (S.γ (S.transition u))) f := by
  rcases (S.γ S.z₀).toValuationSubring.mem_or_inv_mem f with hf | hf
  · exact S.eventuallyEq_of_mem hf
  · have h := S.eventuallyEq_of_mem hf
    simpa only [Place.rationalEval_inv, inv_inj] using h

theorem difference_order_top (f : EE) :
    meromorphicOrderAt (S.difference f) S.z₀' = ⊤ :=
  meromorphicOrderAt_eq_top_iff.mpr ((S.eventuallyEq f).mono fun _ hu => sub_eq_zero.mpr hu)

end
end Dubon2026.SourceCurve.AnalyticChart.ComparisonData
