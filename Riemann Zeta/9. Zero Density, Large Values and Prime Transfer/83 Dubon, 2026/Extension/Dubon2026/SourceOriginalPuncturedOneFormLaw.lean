import Dubon2026.SourceOriginalChartOneFormLaw

/-! DUB-17/18 -> raw reciprocity -> simple-pole cell coefficients.
Finite differential support gives regularity on a punctured neighborhood.
The already proved pointwise one-form law therefore holds on a punctured
original chart, even when its center is a pole. No simple-pole restriction is
needed for this coordinate identity; that restriction enters the residue model.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology Manifold
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology placeChartedSpace
local notation "F" => modularFunctionFieldOver N ℂ

theorem eventually_differentialCoeff_mem_punctured (v : Place ℂ F) (θ : Ω[F⁄ℂ]) :
    ∀ᶠ w in 𝓝[≠] v, w.differentialCoeff θ ∈ w.toValuationSubring := by
  letI := place_t2Space N
  haveI : ∀ w : Place ℂ F, w.DCoordGenerates := original_place_dCoordGenerates N ℂ
  haveI : Nontrivial Ω[F⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  by_cases h0 : θ = 0
  · subst θ
    exact Eventually.of_forall fun w => by rw [w.differentialCoeff_zero]; exact zero_mem _
  have hfin : {w : Place ℂ F | w.ordDifferential θ < 0}.Finite :=
    (finite_original_differential_support N ℂ h0).subset fun _ hw => ne_of_lt hw
  filter_upwards [nhdsNE_le_cofinite v hfin.compl_mem_cofinite] with w hw
  exact w.mem_of_ord_nonneg (not_lt.mp hw)

theorem placeFamily_tendsto_punctured (v : Place ℂ F) :
    Tendsto (placeFamily N v) (𝓝[≠] (0 : ℂ)) (𝓝[≠] v) := by
  have hc := placeFamily_continuousAt_zero N v
  rw [ContinuousAt, (place_spec N v).2.1] at hc
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (hc.mono_left nhdsWithin_le_nhds)
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N v) :=
    nhdsWithin_le_nhds (ball_mem_nhds _ (place_spec N v).1)
  filter_upwards [hb, self_mem_nhdsWithin] with z hz hn
  intro he
  apply hn
  exact placeFamily_injOn N v hz (mem_ball_self (place_spec N v).1)
    (he.trans (place_spec N v).2.1.symm)

theorem one_form_law_punctured (Q : Place ℂ F) (θ : Ω[F⁄ℂ]) :
    ∀ᶠ y in 𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) Q Q),
      readDifferential N Q θ y =
        readDifferential N ((extChartAt 𝓘(ℂ, ℂ) Q).symm y) θ
          (extChartAt 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) Q).symm y)
            ((extChartAt 𝓘(ℂ, ℂ) Q).symm y)) *
          deriv (extChartAt 𝓘(ℂ, ℂ) ((extChartAt 𝓘(ℂ, ℂ) Q).symm y) ∘
            (extChartAt 𝓘(ℂ, ℂ) Q).symm) y := by
  rw [extPlaceChart_self]
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N Q) :=
    nhdsWithin_le_nhds (ball_mem_nhds _ (place_spec N Q).1)
  filter_upwards [hb, (placeFamily_tendsto_punctured N Q).eventually
    (eventually_differentialCoeff_mem_punctured N Q θ)] with y hy hyr
  rw [extPlaceChart_symm_apply, extPlaceChart_self]
  exact one_form_law_at N Q θ hy hyr

end
end Dubon2026.SourceFunctionField.OriginalChart
