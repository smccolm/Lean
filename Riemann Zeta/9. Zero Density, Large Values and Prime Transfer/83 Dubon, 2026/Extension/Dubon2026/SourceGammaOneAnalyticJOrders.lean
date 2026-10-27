import Dubon2026.SourceGammaOneAnalyticPlaces
import Dubon2026.SourceGammaOneJRealization

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> finite
holomorphy. Identify the actual j-j(tau) germ and its positive normalized
order, then reuse the existing exact analytic derivative-order identity.
This uses no classification of finite places or elliptic stabilizers. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter SourceCurve
open scoped Topology
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
  (hT : ModularGroup.T ∈ Γ)
include hT

theorem analyticOrder_j_sub (τ : ℍ) (c : ℂ) :
    analyticOrder Γ τ
      (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c) =
      meromorphicOrderAt (fun z : ℂ => JMultiplicity.jf (ofComplex z) - c) (τ : ℂ) := by
  unfold analyticOrder
  apply meromorphicOrderAt_congr
  have he : jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) c =
      jCoordinateOver Γ ℂ + algebraMap ℂ (functionFieldOver Γ ℂ) (-c) := by
    rw [map_neg, sub_eq_add_neg]
  rw [he]
  filter_upwards [realize_add_eventuallyEq hT (jCoordinateOver Γ ℂ)
    (algebraMap ℂ (functionFieldOver Γ ℂ) (-c)) τ] with z hz
  have hconst : realize Γ
      ((algebraMap ℂ (functionFieldOver Γ ℂ) (-c) : functionFieldOver Γ ℂ) :
        LaurentSeries ℂ) (ofComplex z) = -c := realize_algebraMap hT (-c) (ofComplex z)
  simpa only [realize_jCoordinateOver hT, hconst, Pi.add_apply, sub_eq_add_neg] using hz

theorem analyticPlace_j_sub_pos (τ : ℍ) :
    0 < (analyticPlace hT τ).ord (jCoordinateOver Γ ℂ -
      algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) := by
  have hx : jCoordinateOver Γ ℂ -
      algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ) ≠ 0 :=
    Place.transcendental_sub_algebraMap_ne_zero (transcendental_jCoordinateOver Γ ℂ) _
  have ha := JMultiplicity.analyticAt_comp JMultiplicity.mdifferentiable_jf τ
  have hs := ha.sub (analyticAt_const (v := JMultiplicity.jf τ))
  have hp : 0 < analyticOrder Γ τ (jCoordinateOver Γ ℂ -
      algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) := by
    rw [analyticOrder_j_sub hT]
    apply (tendsto_zero_iff_meromorphicOrderAt_pos hs.meromorphicAt).mp
    simpa only [Pi.sub_apply, Function.comp_apply, ofComplex_apply, sub_self] using
      hs.continuousAt.tendsto.mono_left
        (show 𝓝[≠] (τ : ℂ) ≤ 𝓝 (τ : ℂ) from nhdsWithin_le_nhds)
  rw [analyticPlace_order hT τ _ hx] at hp
  have hp' : 0 < (analyticRamification hT τ : ℤ) *
      (analyticPlace hT τ).ord (jCoordinateOver Γ ℂ -
        algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) := by
    exact_mod_cast hp
  nlinarith [Int.natCast_nonneg (analyticRamification hT τ)]

theorem analytic_derivative_order (τ : ℍ) :
    meromorphicOrderAt (deriv (JMultiplicity.jf ∘ ofComplex)) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) * (analyticPlace hT τ).ord
        (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) - 1 : ℤ) :
          WithTop ℤ) := by
  have hx : jCoordinateOver Γ ℂ -
      algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ) ≠ 0 :=
    Place.transcendental_sub_algebraMap_ne_zero (transcendental_jCoordinateOver Γ ℂ) _
  have h := meromorphicOrderAt_deriv_jf_add_one τ
  rw [← analyticOrder_j_sub hT τ, analyticPlace_order hT τ _ hx] at h
  cases ho : meromorphicOrderAt (deriv (JMultiplicity.jf ∘ ofComplex)) (τ : ℂ) with
  | top => simp only [ho, top_add, WithTop.top_ne_coe] at h
  | coe n =>
    rw [ho] at h
    have hi : n + 1 = (analyticRamification hT τ : ℤ) * (analyticPlace hT τ).ord
        (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) (JMultiplicity.jf τ)) := by
      exact_mod_cast h
    congr 1
    omega

end
end Dubon2026.SourceFunctionField.GammaOne
