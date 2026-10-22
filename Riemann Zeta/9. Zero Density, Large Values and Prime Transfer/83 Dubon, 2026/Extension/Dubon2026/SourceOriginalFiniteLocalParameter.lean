import Dubon2026.SourceOriginalRamifiedMeromorphicOrder
import Dubon2026.SourceOriginalFinitePlaceExhaustion

/-! DUB-17/18 -> original torsion cardinality -> complex place charts.
The genuine original uniformizer has order one on the descended family,
even at elliptic points. Native analytic inversion makes that uniformizer
the parameter itself and proves local injectivity of the literal place
family. Finite-place exhaustion supplies this construction for every
original place where j is regular. The exact order comparison is proved
at the center for all nonzero functions; compatibility throughout a chart,
cusp charts and global Abel--Jacobi comparison remain required.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter SourceCurve
open scoped Topology

private theorem deriv_ne_zero_of_order_one {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (horder : meromorphicOrderAt F a = (1 : ℤ)) :
    deriv F a ≠ 0 := by
  obtain ⟨g, hg, hg0, he⟩ := (meromorphicOrderAt_eq_int_iff hF.meromorphicAt).mp horder
  have he' : F =ᶠ[𝓝[≠] a] (fun z => (z - a) * g z) := by
    simpa only [zpow_one, smul_eq_mul] using he
  have ha : AnalyticAt ℂ (fun z => (z - a) * g z) a :=
    (analyticAt_id.sub analyticAt_const).mul hg
  have he'' := (hF.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE ha.continuousAt).mp he'
  have hd : HasDerivAt (fun z => (z - a) * g z) (g a) a := by
    simpa only [id_eq, sub_self, one_mul, zero_mul, add_zero, Pi.mul_apply] using
      ((hasDerivAt_id a).sub_const a).mul hg.differentiableAt.hasDerivAt
  rw [he''.deriv_eq, hd.deriv]
  exact hg0

theorem original_analytic_place_local_parameter (N : ℕ) [NeZero N] (τ : ℍ) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < ρ ∧ γ 0 = originalAnalyticPlace N τ ∧ Set.InjOn γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ,
        originalPlaceEval N ℂ (γ z) (originalAnalyticPlace N τ).uniformizer = z) ∧
      ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun z => originalPlaceEval N ℂ (γ z) f) 0 ∧
        meromorphicOrderAt (fun z => originalPlaceEval N ℂ (γ z) f) 0 =
          ((originalAnalyticPlace N τ).ord f : WithTop ℤ) := by
  let v := originalAnalyticPlace N τ
  let T : ℂ → ℂ := fun z => originalPlaceEval N ℂ (originalRamifiedPlace N τ z) v.uniformizer
  have hmem : v.uniformizer ∈ v.toValuationSubring :=
    v.mem_of_ord_nonneg (by rw [v.ord_uniformizer]; norm_num)
  have hT : AnalyticAt ℂ T 0 := (originalRamifiedPlace_regular_analytic N τ v.uniformizer hmem).1
  have hT0 : T 0 = 0 := by
    dsimp only [T]
    rw [originalRamifiedPlace_zero]
    apply (originalPlaceEval_eq_zero_iff_ord_pos N ℂ v hmem v.uniformizer_ne_zero).mpr
    rw [v.ord_uniformizer]
    norm_num
  have hd : deriv T 0 ≠ 0 := by
    apply deriv_ne_zero_of_order_one hT
    rw [originalRamifiedPlace_meromorphicOrderAt N τ v.uniformizer v.uniformizer_ne_zero,
      v.ord_uniformizer]
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
  obtain ⟨ρ, hρ, hρeq⟩ := Metric.eventually_nhds_iff_ball.mp he
  let γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ) := fun z => originalRamifiedPlace N τ (r z)
  refine ⟨ρ, γ, hρ, ?_, ?_, hρeq, ?_⟩
  · change originalRamifiedPlace N τ (r 0) = _
    rw [hr0, originalRamifiedPlace_zero]
  · intro z hz w hw heq
    calc z = originalPlaceEval N ℂ (γ z) v.uniformizer := (hρeq z hz).symm
         _ = originalPlaceEval N ℂ (γ w) v.uniformizer := congrArg (fun P => originalPlaceEval N ℂ P v.uniformizer) heq
         _ = w := hρeq w hw
  · intro f hf
    let F : ℂ → ℂ := fun z => originalPlaceEval N ℂ (originalRamifiedPlace N τ z) f
    have hm : MeromorphicAt F (r 0) := by
      rw [hr0]
      exact meromorphicAt_originalRamifiedPlace_eval N τ f
    refine ⟨hm.comp_analyticAt ha, ?_⟩
    change meromorphicOrderAt (F ∘ r) 0 = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero ha hdr0, hr0]
    exact originalRamifiedPlace_meromorphicOrderAt N τ f hf

theorem original_finite_place_local_parameter (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (hv : jOver N ℂ ∈ v.toValuationSubring) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < ρ ∧ γ 0 = v ∧ Set.InjOn γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, originalPlaceEval N ℂ (γ z) v.uniformizer = z) ∧
      ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun z => originalPlaceEval N ℂ (γ z) f) 0 ∧
        meromorphicOrderAt (fun z => originalPlaceEval N ℂ (γ z) f) 0 = (v.ord f : WithTop ℤ) := by
  obtain ⟨τ, rfl⟩ := exists_original_analytic_place_eq N v hv
  exact original_analytic_place_local_parameter N τ

end
end Dubon2026.SourceFunctionField
