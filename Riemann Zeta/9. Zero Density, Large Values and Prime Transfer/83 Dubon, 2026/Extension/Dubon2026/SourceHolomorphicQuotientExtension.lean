import Dubon2026.SourceOriginalAnalyticJFibers
import Mathlib.Analysis.Complex.RemovableSingularity

/-! DUB-17/18 -> finite-place exhaustion -> bounded original functions
integral over C[j] -> clearing their cusp poles -> holomorphic quotient
extension on the upper half-plane. Native removable singularities extend
the locally bounded actual quotient, and continuity proves the exact
multiplicative identity even at zeros of its denominator. The original
modular-ratio consumer supplies the isolated-zero and boundedness inputs.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_forall_isBoundedUnder_realize.
-/
namespace Dubon2026.SourceFunctionField.HolomorphicQuotient
noncomputable section
open UpperHalfPlane Filter Function Complex
open scoped MatrixGroups Topology Manifold

theorem eq_of_eq_off_zeros {h u v : ℍ → ℂ}
    (hh : ∀ c : ℂ, 0 < c.im → ∀ᶠ z in 𝓝[≠] c, h (ofComplex z) ≠ 0)
    (hu : Continuous u) (hv : Continuous v) (huv : ∀ τ, h τ ≠ 0 → u τ = v τ) : u = v := by
  funext τ
  have hcu : ContinuousAt (u ∘ ofComplex) (τ : ℂ) :=
    hu.continuousAt.comp_of_eq (mdifferentiableAt_ofComplex τ.im_pos).continuousAt (ofComplex_apply τ)
  have hcv : ContinuousAt (v ∘ ofComplex) (τ : ℂ) :=
    hv.continuousAt.comp_of_eq (mdifferentiableAt_ofComplex τ.im_pos).continuousAt (ofComplex_apply τ)
  have hev : (u ∘ ofComplex) =ᶠ[𝓝[≠] (τ : ℂ)] (v ∘ ofComplex) :=
    (hh τ τ.im_pos).mono fun z hz => huv _ hz
  have := tendsto_nhds_unique_of_eventuallyEq (hcu.tendsto.mono_left nhdsWithin_le_nhds)
    (hcv.tendsto.mono_left nhdsWithin_le_nhds) hev
  simpa only [comp_apply, ofComplex_apply] using this

theorem exists_mdifferentiable_mul_eq {g h : ℍ → ℂ} (hg : MDiff g) (hh : MDiff h)
    (hh0 : ∀ c : ℂ, 0 < c.im → ∀ᶠ z in 𝓝[≠] c, h (ofComplex z) ≠ 0)
    (hb : ∀ τ : ℍ, ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (τ : ℂ), ‖g (ofComplex z) / h (ofComplex z)‖ ≤ M) :
    ∃ F₀ : ℍ → ℂ, MDiff F₀ ∧ ∀ τ, F₀ τ * h τ = g τ := by
  set φ : ℂ → ℂ := fun z => g (ofComplex z) / h (ofComplex z) with hφ
  set ψ : ℂ → ℂ := fun c => limUnder (𝓝[≠] c) φ with hψ

  have hA : ∀ c : ℂ, ∀ hc : 0 < c.im, h (ofComplex c) ≠ 0 → DifferentiableAt ℂ φ c := by
    intro c hc hne
    have hg' : DifferentiableAt ℂ (g ∘ ofComplex) c := mdifferentiableAt_iff.mp (hg ⟨c, hc⟩)
    have hh' : DifferentiableAt ℂ (h ∘ ofComplex) c := mdifferentiableAt_iff.mp (hh ⟨c, hc⟩)
    exact hg'.div hh' hne

  have hB : ∀ c : ℂ, 0 < c.im → h (ofComplex c) ≠ 0 → ψ c = φ c := fun c hc hne =>
    ((hA c hc hne).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq

  have hC : DifferentiableOn ℂ ψ {z : ℂ | 0 < z.im} := by
    intro c hc
    have hc' : 0 < c.im := hc
    obtain ⟨M, hM⟩ := hb ⟨c, hc'⟩
    have hev : ∀ᶠ z in 𝓝[≠] c, h (ofComplex z) ≠ 0 ∧ ‖φ z‖ ≤ M ∧ 0 < z.im :=
      (hh0 c hc').and (hM.and (mem_nhdsWithin_of_mem_nhds
        (isOpen_upperHalfPlaneSet.mem_nhds hc')))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    have hd : DifferentiableOn ℂ φ (Metric.ball c ε \ {c}) := fun z hz =>
      (hA z (hball z hz.1 hz.2).2.2 (hball z hz.1 hz.2).1).differentiableWithinAt
    have hbdd : BddAbove (norm ∘ φ '' (Metric.ball c ε \ {c})) := by
      refine ⟨M, ?_⟩
      rintro _ ⟨z, hz, rfl⟩
      exact (hball z hz.1 hz.2).2.1
    have R := Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds c hε)
      hd hbdd
    have heq : Set.EqOn ψ (update φ c (limUnder (𝓝[≠] c) φ)) (Metric.ball c ε) := by
      intro z hz
      by_cases hzc : z = c
      · subst hzc; simp [hψ]
      · rw [update_of_ne hzc]
        exact hB z (hball z hz hzc).2.2 (hball z hz hzc).1
    have hψs : DifferentiableOn ℂ ψ (Metric.ball c ε) := R.congr heq
    exact (hψs.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)))
      |>.differentiableWithinAt

  refine ⟨fun τ => ψ τ, ?_, ?_⟩
  · refine UpperHalfPlane.mdifferentiable_iff.mpr (hC.congr fun z hz => ?_)
    have hz' : 0 < z.im := hz
    simp only [comp_apply, ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_mk]
  · have hF : MDiff (fun τ : ℍ => ψ τ) := by
      refine UpperHalfPlane.mdifferentiable_iff.mpr (hC.congr fun z hz => ?_)
      have hz' : 0 < z.im := hz
      simp only [comp_apply, ofComplex_apply_of_im_pos hz', UpperHalfPlane.coe_mk]
    have key := eq_of_eq_off_zeros (u := fun τ => ψ τ * h τ) (v := g) hh0
      (hF.continuous.mul hh.continuous) hg.continuous (fun τ hτ => by
        have h1 : h (ofComplex (τ : ℂ)) ≠ 0 := by rwa [ofComplex_apply]
        have := hB τ τ.im_pos h1
        simp only [this, hφ, ofComplex_apply]
        exact div_mul_cancel₀ _ hτ)
    exact fun τ => congrFun key τ


end
end Dubon2026.SourceFunctionField.HolomorphicQuotient
