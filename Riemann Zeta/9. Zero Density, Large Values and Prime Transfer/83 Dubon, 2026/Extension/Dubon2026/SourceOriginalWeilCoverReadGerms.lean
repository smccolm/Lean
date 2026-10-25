import Dubon2026.SourceOriginalWeilCoverEvaluationContinuity
import Dubon2026.SourceCurveRationalEvaluationLaws

/-! DUB-17/18 -> cover Abel converse -> actual field comparison.
The constructed cover residue readings preserve addition and multiplication
in punctured chart germs. Native meromorphic analyticity supplies regularity
away from the center, where the actual residue homomorphisms apply.
Only the field-reading laws needed for comparison are constructed here.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Metric
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

/-- Genuine residue evaluation along the constructed cover chart family. -/
def chartRead (v : Place ℂ EE) (a : EE) : ℂ → ℂ := fun z =>
  (placeFamily N n r A hr hrA v z).rationalEval
    (originalWeilKummerCover_residue_bijective N ℂ n r _) a

theorem chartRead_algebraMap (v : Place ℂ EE) (c : ℂ) :
    chartRead N n r A hr hrA v (algebraMap ℂ EE c) = fun _ => c := by
  funext z
  exact (placeFamily N n r A hr hrA v z).rationalEval_algebraMap
    (originalWeilKummerCover_residue_bijective N ℂ n r _) c

theorem chartRead_zero (v : Place ℂ EE) : chartRead N n r A hr hrA v 0 = 0 := by
  simpa only [map_zero] using chartRead_algebraMap N n r A hr hrA v 0

theorem chartRead_one (v : Place ℂ EE) : chartRead N n r A hr hrA v 1 = 1 := by
  simpa only [map_one] using chartRead_algebraMap N n r A hr hrA v 1

theorem meromorphicAt_chartRead (v : Place ℂ EE) (a : EE) {z : ℂ}
    (hz : z ∈ ball 0 (placeRadius N n r A hr hrA v)) :
    MeromorphicAt (chartRead N n r A hr hrA v a) z := by
  by_cases ha : a = 0
  · rw [ha, chartRead_zero]
    exact MeromorphicAt.const 0 z
  exact ((place_spec N n r A hr hrA v).2.2.1 z hz a ha).1

theorem eventually_chartRead_regular (v : Place ℂ EE) (a : EE) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), a ∈ (placeFamily N n r A hr hrA v z).toValuationSubring := by
  by_cases ha : a = 0
  · subst a
    exact Eventually.of_forall fun _ => zero_mem _
  have han := (meromorphicAt_chartRead N n r A hr hrA v a
    (mem_ball_self (place_spec N n r A hr hrA v).1)).eventually_analyticAt
  have hb : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ ball 0 (placeRadius N n r A hr hrA v) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 (place_spec N n r A hr hrA v).1)
  filter_upwards [han, hb] with z hz hzb
  have ho := hz.meromorphicOrderAt_nonneg
  change 0 ≤ meromorphicOrderAt (fun u => (placeFamily N n r A hr hrA v u).rationalEval
    (originalWeilKummerCover_residue_bijective N ℂ n r _) a) z at ho
  rw [((place_spec N n r A hr hrA v).2.2.1 z hzb a ha).2.1] at ho
  exact (placeFamily N n r A hr hrA v z).mem_of_ord_nonneg (by exact_mod_cast ho)

theorem chartRead_add (v : Place ℂ EE) (a b : EE) :
    chartRead N n r A hr hrA v (a + b) =ᶠ[𝓝[≠] (0 : ℂ)]
      chartRead N n r A hr hrA v a + chartRead N n r A hr hrA v b := by
  filter_upwards [eventually_chartRead_regular N n r A hr hrA v a,
    eventually_chartRead_regular N n r A hr hrA v b] with z ha hb
  let w := placeFamily N n r A hr hrA v z
  let hw := originalWeilKummerCover_residue_bijective N ℂ n r w
  change w.rationalEval hw (a + b) = w.rationalEval hw a + w.rationalEval hw b
  rw [w.rationalEval_of_mem hw (add_mem ha hb), w.rationalEval_of_mem hw ha,
    w.rationalEval_of_mem hw hb]
  exact (w.rationalRegularEval hw).map_add ⟨a, ha⟩ ⟨b, hb⟩

theorem chartRead_mul (v : Place ℂ EE) (a b : EE) :
    chartRead N n r A hr hrA v (a * b) =ᶠ[𝓝[≠] (0 : ℂ)]
      chartRead N n r A hr hrA v a * chartRead N n r A hr hrA v b := by
  filter_upwards [eventually_chartRead_regular N n r A hr hrA v a,
    eventually_chartRead_regular N n r A hr hrA v b] with z ha hb
  exact (placeFamily N n r A hr hrA v z).rationalEval_mul_of_mem
    (originalWeilKummerCover_residue_bijective N ℂ n r _) ha hb

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
