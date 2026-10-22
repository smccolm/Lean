import Dubon2026.SourceOriginalCuspChartParameters
import Dubon2026.SourceOriginalFiniteChartParameters
import Dubon2026.SourceOriginalCuspCount

/-! DUB-17/18 -> original torsion cardinality -> complex curve charts.
Every original complex place has an injective uniformizer parameter with
literal residue evaluation, exact normalized orders and regular-function
analyticity throughout its disk. Finite places use the existing modular
charts. The proved exhaustive original cusp family supplies every pole.
No place classification or local analytic parameter is an input.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem original_place_chart_parameter (N : ℕ) [NeZero N]
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ (ρ : ℝ) (γ : ℂ → Place ℂ (modularFunctionFieldOver N ℂ)),
      0 < ρ ∧ γ 0 = v ∧ Set.InjOn γ (Metric.ball 0 ρ) ∧
      (∀ z ∈ Metric.ball 0 ρ, originalPlaceEval N ℂ (γ z) v.uniformizer = z) ∧
      ∀ z ∈ Metric.ball 0 ρ, ∀ f : modularFunctionFieldOver N ℂ, f ≠ 0 →
        MeromorphicAt (fun t => originalPlaceEval N ℂ (γ t) f) z ∧
        meromorphicOrderAt (fun t => originalPlaceEval N ℂ (γ t) f) z = (γ z).ord f ∧
        (f ∈ (γ z).toValuationSubring → AnalyticAt ℂ (fun t => originalPlaceEval N ℂ (γ t) f) z) := by
  classical
  by_cases hv : jOver N ℂ ∈ v.toValuationSubring
  · exact original_finite_place_chart_parameter N v hv
  have hvpole : v.ord (jOver N ℂ) < 0 := lt_of_not_ge
    (fun h => hv (v.mem_of_ord_nonneg h))
  have hfin : {w : Place ℂ (modularFunctionFieldOver N ℂ) | w.ord (jOver N ℂ) < 0}.Finite :=
    (finite_original_divisor_support N ℂ (jOver N ℂ)).subset fun _ hw => ne_of_lt hw
  haveI : NeZero (N : ℂ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ N
  have hu := hz.isUnit (NeZero.ne N)
  have hζ : IsPrimitiveRoot (hu.unit : ℂ) N := by rw [hu.unit_spec]; exact hz
  have hvS : v ∈ hfin.toFinset := hfin.mem_toFinset.mpr hvpole
  rw [original_cusp_family_exhaustive N ℂ hu.unit hζ hfin.toFinset (fun _ => hfin.mem_toFinset)] at hvS
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hvS
  exact original_cusp_place_chart_parameter N hu.unit hζ s

end
end Dubon2026.SourceFunctionField
