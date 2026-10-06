import Dubon2026.SteinhausLogScale
import Dubon2026.SteinhausIndependentLaw

/-! # Lemma 4.1 for arbitrary independent Steinhaus variables

The law of each variable is the actual normalized Haar unit-circle pushforward.
The theorem derives the expected logarithm from independence and that law.
-/

namespace Dubon2026

open MeasureTheory ProbabilityTheory

/-- One logarithmic constant for every admissible sum on every probability space. -/
theorem steinhaus_translated_logarithmic_estimate {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (κ : Type) [Fintype κ] [Nonempty κ]
      (b : κ → ℝ), (∀ i, 0 < b i) → 5 ≤ Fintype.card κ →
      steinhausMaxCoefficient b / steinhausMinCoefficient b ≤ K →
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : κ → Ω → ℂ), (∀ i, Measurable (Z i)) → iIndepFun Z P →
        (∀ i, P.map (Z i) = uniformSteinhausLaw) → ∀ a : ℂ,
      Integrable (fun ω => Real.log ‖a + ∑ i, (b i : ℂ) * Z i ω‖) P ∧
      Real.log (Real.sqrt (∑ i, b i ^ 2)) - C ≤
        ∫ ω, Real.log ‖a + ∑ i, (b i : ℂ) * Z i ω‖ ∂P := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_steinhaus_log hK
  refine ⟨C, hC, ?_⟩
  intro κ _ _ b hb hm hcomp Ω _ P _ Z hZ hind hlaw a
  obtain ⟨hi, he⟩ := hbound κ b hb hm hcomp a
  have hg : Measurable (fun w : ℂ => Real.log ‖a + w‖) := by fun_prop
  have hs : Measurable (fun ω => ∑ i, (b i : ℂ) * Z i ω) := by fun_prop
  have hsum := (continuous_steinhausSum b).measurable
  have hmap := independent_steinhaus_sum_law Z hZ hind hlaw b
  have hiLaw : Integrable (fun w : ℂ => Real.log ‖a + w‖) (steinhausLaw b) :=
    (integrable_map_measure hg.aestronglyMeasurable hsum.aemeasurable).mpr hi
  have hiMap : Integrable (fun w : ℂ => Real.log ‖a + w‖)
      (P.map (fun ω => ∑ i, (b i : ℂ) * Z i ω)) := by
    rw [hmap]
    exact hiLaw
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable hs.aemeasurable).mp hiMap, ?_⟩
  rw [← integral_map hs.aemeasurable hg.aestronglyMeasurable, hmap]
  change Real.log (steinhausScale b) - C ≤
    ∫ w, Real.log ‖a + w‖ ∂(steinhausHaar κ).map (steinhausSum b)
  rw [integral_map hsum.aemeasurable hg.aestronglyMeasurable]
  exact he

end Dubon2026
