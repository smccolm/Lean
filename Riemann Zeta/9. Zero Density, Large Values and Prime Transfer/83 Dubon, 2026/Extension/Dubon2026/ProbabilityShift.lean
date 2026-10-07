import Dubon2026.JessenShift
import Dubon2026.WeakLimit

/-! # Translating the normalized probability limit with the actual coefficient shift -/

namespace Dubon2026

open Filter Set MeasureTheory
open scoped Topology

noncomputable section

theorem jessenProbability_congr {a b : ℕ → ℂ} (hab : a = b) (ha : a 1 = 1) (hb : b 1 = 1) :
    jessenProbability ha = jessenProbability hb := by
  subst b
  rfl

theorem jessenProbability_shiftedCoefficients {a : ℕ → ℂ} {N : ℕ}
    (ha : a 1 = 1) (hN : 1 ≤ N) (hM : 1 < lastIndex a N) (c : ℝ) :
    jessenProbability (a := shiftedCoefficients a c) (by rwa [shiftedCoefficients_one]) N =
      (jessenProbability ha N).map (measurable_id.add_const c).aemeasurable := by
  apply Subtype.ext
  change (jessenProbability _ N : Measure ℝ) =
    Measure.map (fun x : ℝ => x + c) (jessenProbability ha N : Measure ℝ)
  rw [jessenProbability_eq _ hN (by rwa [lastIndex_shiftedCoefficients]),
    jessenProbability_eq ha hN hM, normalizedJessenMeasure_shiftedCoefficients]

theorem shifted_jessen_probability_limit {a : ℕ → ℂ} {α : ℝ} (ha : a 1 = 1)
    (he : ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 1 < lastIndex a N)
    (hw : Tendsto (jessenProbability ha) atTop
      (𝓝 (⟨Measure.dirac α, inferInstance⟩ : ProbabilityMeasure ℝ))) (c : ℝ) :
    Tendsto (jessenProbability (a := shiftedCoefficients a c)
      (by rwa [shiftedCoefficients_one])) atTop
      (𝓝 (⟨Measure.dirac (α + c), inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have hlim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hw
    (continuous_id.add_const c)
  have heq : ProbabilityMeasure.map (⟨Measure.dirac α, inferInstance⟩ : ProbabilityMeasure ℝ)
      (measurable_id.add_const c).aemeasurable =
      (⟨Measure.dirac (α + c), inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply Subtype.ext
    exact Measure.map_dirac α
  rw [heq] at hlim
  apply hlim.congr'
  filter_upwards [he] with N hN
  exact (jessenProbability_shiftedCoefficients ha hN.1 hN.2 c).symm

theorem normalizedJessen_shiftedCoefficients (a : ℕ → ℂ) (c : ℝ) (N : ℕ) (σ : ℝ) :
    normalizedJessen (shiftedCoefficients a c) N σ = normalizedJessen a N (σ - c) := by
  rw [normalizedJessen, normalizedJessen, jessenFunction_shiftedCoefficients]

theorem shifted_normalizedJessen_limit {a : ℕ → ℂ} {α : ℝ}
    (hp : TendstoLocallyUniformly (normalizedJessen a) (fun σ => max (α - σ) 0) atTop)
    (c : ℝ) :
    TendstoLocallyUniformly (normalizedJessen (shiftedCoefficients a c))
      (fun σ => max (α + c - σ) 0) atTop := by
  have hh := hp.comp (g := fun σ : ℝ => σ - c) (continuous_id.sub continuous_const)
  have hf : (fun σ : ℝ => max (α - σ) 0) ∘ (fun σ => σ - c) =
      (fun σ => max (α + c - σ) 0) := by
    funext σ
    dsimp
    congr 1
    ring
  rw [hf] at hh
  convert hh using 1
  funext N σ
  exact normalizedJessen_shiftedCoefficients a c N σ

end

end Dubon2026
