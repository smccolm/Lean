import Dubon2026.SourceCurveConvergentDiscResidues
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! DUB-17/18 -> auxiliary cover analytic charts -> invert the actual uniformizer.
Reuse the original cusp inverse-function argument with actual rational residue
evaluation. A local analytic coordinate with nonzero derivative reparametrizes
the place family injectively and preserves all normalized meromorphic orders. -/
namespace Dubon2026.SourceCurve.AnalyticDisc
noncomputable section
open Filter Metric
open scoped Topology

theorem exists_parameter_of_evaluation_family {E : Type*} [Field E] [Algebra ℂ E]
    (hv : ∀ P : Place ℂ E, Function.Bijective (algebraMap ℂ P.ResidueField))
    (w : Place ℂ E) (T : ℂ → ℂ) (hT : AnalyticAt ℂ T 0) (hT0 : T 0 = 0)
    (hd : deriv T 0 ≠ 0) {δ : ℝ} (hδ : 0 < δ) (γ₀ : ℂ → Place ℂ E)
    (hγ₀ : γ₀ 0 = w)
    (hcoord : ∀ z ∈ ball 0 δ, (γ₀ z).rationalEval (hv (γ₀ z)) w.uniformizer = T z)
    (horders : ∀ z ∈ ball 0 δ, ∀ a : E, a ≠ 0 →
      MeromorphicAt (fun t => (γ₀ t).rationalEval (hv (γ₀ t)) a) z ∧
      meromorphicOrderAt (fun t => (γ₀ t).rationalEval (hv (γ₀ t)) a) z =
        ((γ₀ z).ord a : WithTop ℤ) ∧
      (a ∈ (γ₀ z).toValuationSubring →
        AnalyticAt ℂ (fun t => (γ₀ t).rationalEval (hv (γ₀ t)) a) z)) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ E), 0 < ρ ∧ γ 0 = w ∧ Set.InjOn γ (ball 0 ρ) ∧
      (∀ z ∈ ball 0 ρ, (γ z).rationalEval (hv (γ z)) w.uniformizer = z) ∧
      ∀ z ∈ ball 0 ρ, ∀ a : E, a ≠ 0 →
        MeromorphicAt (fun t => (γ t).rationalEval (hv (γ t)) a) z ∧
        meromorphicOrderAt (fun t => (γ t).rationalEval (hv (γ t)) a) z =
          ((γ z).ord a : WithTop ℤ) ∧
        (a ∈ (γ z).toValuationSubring →
          AnalyticAt ℂ (fun t => (γ t).rationalEval (hv (γ t)) a) z) := by
  let r := hT.hasStrictDerivAt.localInverse T (deriv T 0) 0 hd
  have ha : AnalyticAt ℂ r 0 := by simpa only [hT0] using hT.analyticAt_localInverse hd
  have hr0 : r 0 = 0 := by
    simpa only [hT0] using
      (HasStrictDerivAt.eventually_left_inverse hT.hasStrictDerivAt hd).self_of_nhds
  have hdr : HasStrictDerivAt r (deriv T 0)⁻¹ 0 := by
    simpa only [hT0] using hT.hasStrictDerivAt.to_localInverse hd
  have hdr0 : deriv r 0 ≠ 0 := by rw [hdr.hasDerivAt.deriv]; exact inv_ne_zero hd
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), T (r z) = z := by
    simpa only [hT0] using HasStrictDerivAt.eventually_right_inverse hT.hasStrictDerivAt hd
  have hrange : ∀ᶠ z in 𝓝 (0 : ℂ), r z ∈ ball 0 δ := by
    apply ha.continuousAt.eventually
    rw [hr0]
    exact ball_mem_nhds 0 hδ
  have hderiv : ∀ᶠ z in 𝓝 (0 : ℂ), deriv r z ≠ 0 :=
    ha.deriv.continuousAt.eventually (isOpen_ne.mem_nhds hdr0)
  obtain ⟨ρ, hρ, hρall⟩ := Metric.eventually_nhds_iff_ball.mp
    (he.and (hrange.and (ha.eventually_analyticAt.and hderiv)))
  let γ : ℂ → Place ℂ E := fun z => γ₀ (r z)
  have heval (z : ℂ) (hz : z ∈ ball 0 ρ) :
      (γ z).rationalEval (hv (γ z)) w.uniformizer = z :=
    (hcoord (r z) (hρall z hz).2.1).trans (hρall z hz).1
  refine ⟨ρ, γ, hρ, ?_, ?_, heval, ?_⟩
  · change γ₀ (r 0) = _
    rw [hr0, hγ₀]
  · intro z hz u hu hzu
    calc z = (γ z).rationalEval (hv (γ z)) w.uniformizer := (heval z hz).symm
         _ = (γ u).rationalEval (hv (γ u)) w.uniformizer :=
           congrArg (fun P => P.rationalEval (hv P) w.uniformizer) hzu
         _ = u := heval u hu
  · intro z hz a ha0
    obtain ⟨_, hrangez, haz, hdrz⟩ := hρall z hz
    obtain ⟨hm, ho, han⟩ := horders (r z) hrangez a ha0
    refine ⟨hm.comp_analyticAt haz, ?_, fun h => (han h).comp haz⟩
    change meromorphicOrderAt ((fun t => (γ₀ t).rationalEval (hv (γ₀ t)) a) ∘ r) z = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero haz hdrz]
    exact ho

end
end Dubon2026.SourceCurve.AnalyticDisc
