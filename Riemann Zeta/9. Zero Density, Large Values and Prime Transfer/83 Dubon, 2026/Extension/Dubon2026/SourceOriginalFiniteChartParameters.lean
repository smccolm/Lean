import Dubon2026.SourceOriginalRamifiedChartOrders
import Dubon2026.SourceOriginalFinitePlaceExhaustion

/-! DUB-17/18 -> original torsion cardinality -> actual complex-place
charts. Invert the actual original uniformizer on the descended family.
One radius gives local injectivity, uniformizer evaluation equal to the
parameter and normalized orders and regular analyticity at every point
for all original functions. Cusp charts and transition/global comparisons
remain required before the complex Abel-Jacobi theorem applies.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter SourceCurve
open scoped Topology

private theorem deriv_ne_zero_of_order_one {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (ho : meromorphicOrderAt F a = (1 : ℤ)) : deriv F a ≠ 0 := by
  have ha : analyticOrderAt F a = (1 : ℕ∞) := by
    apply WithTop.map_injective (Nat.cast_injective (R := ℤ))
    change (analyticOrderAt F a).map (Nat.cast : ℕ → ℤ) = (1 : ℕ∞).map (Nat.cast : ℕ → ℤ)
    rw [← hF.meromorphicOrderAt_eq, ho]
    rfl
  exact hF.deriv.analyticOrderAt_eq_zero.mp
    (analyticOrderAt_deriv_of_pos hF (n := 0) (by simpa only [Nat.cast_zero, zero_add] using ha))

theorem original_analytic_place_chart_parameter (N : ℕ) [NeZero N] (τ : ℍ) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < ρ ∧ γ 0 = originalAnalyticPlace N τ ∧ Set.InjOn γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ,
        originalPlaceEval N ℂ (γ z) (originalAnalyticPlace N τ).uniformizer = z) ∧
      ∀ z ∈ Metric.ball 0 ρ, ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun t => originalPlaceEval N ℂ (γ t) f) z ∧
        meromorphicOrderAt (fun t => originalPlaceEval N ℂ (γ t) f) z = (γ z).ord f ∧
        (f ∈ (γ z).toValuationSubring → AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (γ t) f) z) := by
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
  obtain ⟨δ, hδ, hδorders⟩ := originalRamifiedPlace_chart_orders N τ
  have hrange : ∀ᶠ z in 𝓝 (0 : ℂ), r z ∈ Metric.ball 0 δ := by
    apply ha.continuousAt.eventually
    rw [hr0]
    exact Metric.ball_mem_nhds 0 hδ
  have hderiv : ∀ᶠ z in 𝓝 (0 : ℂ), deriv r z ≠ 0 :=
    ha.deriv.continuousAt.eventually (isOpen_ne.mem_nhds hdr0)
  obtain ⟨ρ, hρ, hρall⟩ := Metric.eventually_nhds_iff_ball.mp
    (he.and (hrange.and (ha.eventually_analyticAt.and hderiv)))
  let γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ) := fun z => originalRamifiedPlace N τ (r z)
  refine ⟨ρ, γ, hρ, ?_, ?_, ?_, ?_⟩
  · change originalRamifiedPlace N τ (r 0) = _
    rw [hr0, originalRamifiedPlace_zero]
  · intro z hz w hw heq
    calc z = originalPlaceEval N ℂ (γ z) v.uniformizer := (hρall z hz).1.symm
         _ = originalPlaceEval N ℂ (γ w) v.uniformizer := congrArg (fun P => originalPlaceEval N ℂ P v.uniformizer) heq
         _ = w := (hρall w hw).1
  · intro z hz
    exact (hρall z hz).1
  · intro z hz f hf
    obtain ⟨_, hrangez, haz, hdrz⟩ := hρall z hz
    obtain ⟨hm, ho, han⟩ := hδorders (r z) hrangez f hf
    refine ⟨hm.comp_analyticAt haz, ?_, fun h => (han h).comp haz⟩
    change meromorphicOrderAt ((fun t => originalPlaceEval N ℂ (originalRamifiedPlace N τ t) f) ∘ r) z = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero haz hdrz]
    exact ho

theorem original_finite_place_chart_parameter (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (hv : jOver N ℂ ∈ v.toValuationSubring) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < ρ ∧ γ 0 = v ∧ Set.InjOn γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, originalPlaceEval N ℂ (γ z) v.uniformizer = z) ∧
      ∀ z ∈ Metric.ball 0 ρ, ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun t => originalPlaceEval N ℂ (γ t) f) z ∧
        meromorphicOrderAt (fun t => originalPlaceEval N ℂ (γ t) f) z = (γ z).ord f ∧
        (f ∈ (γ z).toValuationSubring → AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (γ t) f) z) := by
  obtain ⟨τ, rfl⟩ := exists_original_analytic_place_eq N v hv
  exact original_analytic_place_chart_parameter N τ

end
end Dubon2026.SourceFunctionField
