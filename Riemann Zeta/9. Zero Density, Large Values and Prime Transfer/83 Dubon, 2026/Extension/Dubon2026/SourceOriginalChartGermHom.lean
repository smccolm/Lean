import Dubon2026.SourceOriginalChartDifferentials
import Mathlib.Order.Filter.Germ.Basic

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> compatibility
of actual differential readings. Literal chart evaluation of the original
function field is a ring homomorphism on punctured germs. Native local
meromorphic analyticity gives regularity away from the center; actual
residue homomorphisms then prove addition and multiplication. This avoids
a separate global finite-pole-set/topological argument for these germs.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem chartRead_algebraMap (v : Place ℂ (modularFunctionFieldOver N ℂ)) (c : ℂ) :
    chartRead N v (algebraMap ℂ (modularFunctionFieldOver N ℂ) c) = fun _ => c := by
  funext z
  exact originalPlaceEval_algebraMap N ℂ (placeFamily N v z) c

theorem chartRead_zero (v : Place ℂ (modularFunctionFieldOver N ℂ)) : chartRead N v 0 = 0 := by
  simpa only [map_zero] using chartRead_algebraMap N v 0

theorem chartRead_one (v : Place ℂ (modularFunctionFieldOver N ℂ)) : chartRead N v 1 = 1 := by
  simpa only [map_one] using chartRead_algebraMap N v 1

theorem meromorphicAt_chartRead (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) :
    MeromorphicAt (chartRead N v f) z := by
  by_cases hf : f = 0
  · rw [hf, chartRead_zero]
    exact MeromorphicAt.const 0 z
  exact ((place_spec N v).2.2.1 z hz f hf).1

theorem eventually_chartRead_regular (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), f ∈ (placeFamily N v z).toValuationSubring := by
  by_cases hf : f = 0
  · subst f
    exact Eventually.of_forall fun z => zero_mem _
  have ha := (meromorphicAt_chartRead N v f (mem_ball_self (place_spec N v).1)).eventually_analyticAt
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N v) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 (place_spec N v).1)
  filter_upwards [ha, hb] with z hz hzb
  have ho := hz.meromorphicOrderAt_nonneg
  change 0 ≤ meromorphicOrderAt (fun u => originalPlaceEval N ℂ (placeFamily N v u) f) z at ho
  rw [((place_spec N v).2.2.1 z hzb f hf).2.1] at ho
  exact (placeFamily N v z).mem_of_ord_nonneg (by exact_mod_cast ho)

theorem chartRead_add (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f g : modularFunctionFieldOver N ℂ) :
    chartRead N v (f + g) =ᶠ[𝓝[≠] (0 : ℂ)] chartRead N v f + chartRead N v g := by
  filter_upwards [eventually_chartRead_regular N v f, eventually_chartRead_regular N v g] with z hf hg
  change originalPlaceEval N ℂ (placeFamily N v z) (f + g) =
    originalPlaceEval N ℂ (placeFamily N v z) f + originalPlaceEval N ℂ (placeFamily N v z) g
  rw [originalPlaceEval_of_mem N ℂ _ (add_mem hf hg),
    originalPlaceEval_of_mem N ℂ _ hf, originalPlaceEval_of_mem N ℂ _ hg]
  exact (originalPlaceRegularEval N ℂ (placeFamily N v z)).map_add ⟨f, hf⟩ ⟨g, hg⟩

theorem chartRead_mul (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f g : modularFunctionFieldOver N ℂ) :
    chartRead N v (f * g) =ᶠ[𝓝[≠] (0 : ℂ)] chartRead N v f * chartRead N v g := by
  filter_upwards [eventually_chartRead_regular N v f, eventually_chartRead_regular N v g] with z hf hg
  change originalPlaceEval N ℂ (placeFamily N v z) (f * g) =
    originalPlaceEval N ℂ (placeFamily N v z) f * originalPlaceEval N ℂ (placeFamily N v z) g
  rw [originalPlaceEval_of_mem N ℂ _ (mul_mem hf hg),
    originalPlaceEval_of_mem N ℂ _ hf, originalPlaceEval_of_mem N ℂ _ hg]
  exact (originalPlaceRegularEval N ℂ (placeFamily N v z)).map_mul ⟨f, hf⟩ ⟨g, hg⟩

/-- The actual original function field evaluated in a punctured uniformizer germ. -/
def chartReadHom (v : Place ℂ (modularFunctionFieldOver N ℂ)) :
    modularFunctionFieldOver N ℂ →+* Germ (𝓝[≠] (0 : ℂ)) ℂ where
  toFun f := (chartRead N v f : Germ (𝓝[≠] (0 : ℂ)) ℂ)
  map_one' := by rw [chartRead_one, Germ.coe_one]
  map_zero' := by rw [chartRead_zero, Germ.coe_zero]
  map_add' f g := by
    rw [← Germ.coe_add]
    exact Germ.coe_eq.mpr (chartRead_add N v f g)
  map_mul' f g := by
    rw [← Germ.coe_mul]
    exact Germ.coe_eq.mpr (chartRead_mul N v f g)

theorem chartReadHom_apply (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (f : modularFunctionFieldOver N ℂ) :
    chartReadHom N v f = (chartRead N v f : Germ (𝓝[≠] (0 : ℂ)) ℂ) := rfl

end
end Dubon2026.SourceFunctionField.OriginalChart
