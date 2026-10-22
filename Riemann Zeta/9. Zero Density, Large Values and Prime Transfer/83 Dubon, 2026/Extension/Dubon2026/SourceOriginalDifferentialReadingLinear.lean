import Dubon2026.SourceOriginalLocalAbelJacobi

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> full real
span of actual loop periods. A linear combination of original regular
differentials has the corresponding analytic chart reading. A reading
vanishing near one place forces the actual differential to vanish, by
the existing exact finite order of every nonzero original function.
These are the algebraic inputs to the compact maximum-principle argument;
no independent analytic differential or injectivity premise is supplied.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem original_differentialCoeff_sum_smul {n : ℕ}
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (c : Fin n → ℂ)
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ]) :
    v.differentialCoeff (∑ i, c i • b i) =
      ∑ i, algebraMap ℂ (modularFunctionFieldOver N ℂ) (c i) * v.differentialCoeff (b i) := by
  haveI := original_place_dCoordGenerates N ℂ v
  haveI : Nontrivial Ω[modularFunctionFieldOver N ℂ⁄ℂ] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_original_differentials N ℂ)
  apply v.differentialCoeff_unique
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_smul, v.differentialCoeff_smul_dCoord, IsScalarTower.algebraMap_smul]

theorem originalPlaceEval_sum_mul_of_mem {n : ℕ}
    (w : Place ℂ (modularFunctionFieldOver N ℂ)) (c : Fin n → ℂ)
    (f : Fin n → modularFunctionFieldOver N ℂ) (hf : ∀ i, f i ∈ w.toValuationSubring) :
    originalPlaceEval N ℂ w (∑ i, algebraMap ℂ (modularFunctionFieldOver N ℂ) (c i) * f i) =
      ∑ i, c i * originalPlaceEval N ℂ w (f i) := by
  let h : Fin n → w.toValuationSubring := fun i =>
    algebraMap ℂ w.toValuationSubring (c i) * ⟨f i, hf i⟩
  have he : ((∑ i, h i : w.toValuationSubring) : modularFunctionFieldOver N ℂ) =
      ∑ i, algebraMap ℂ (modularFunctionFieldOver N ℂ) (c i) * f i := by
    simp [h, w.coe_algebraMap]
  rw [← he, originalPlaceEval_of_mem N ℂ w (SetLike.coe_mem (∑ i, h i))]
  change originalPlaceRegularEval N ℂ w (∑ i, h i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [h]
  rw [map_mul, originalPlaceRegularEval_algebraMap,
    originalPlaceEval_of_mem N ℂ w (hf i)]

theorem readDifferential_sum_smul {n : ℕ}
    (v : Place ℂ (modularFunctionFieldOver N ℂ)) (c : Fin n → ℂ)
    (b : Fin n → Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hb : ∀ i, b i ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {z : ℂ} (hz : z ∈ ball 0 (placeRadius N v)) :
    readDifferential N v (∑ i, c i • b i) z = ∑ i, c i * readDifferential N v (b i) z := by
  simp only [readDifferential_eq_coefficient N v _ hz, chartRead,
    original_differentialCoeff_sum_smul]
  exact originalPlaceEval_sum_mul_of_mem N (placeFamily N v z) c
    (fun i => v.differentialCoeff (b i)) (fun i => chart_differentialCoeff_regular N v (b i) (hb i) hz)

theorem eq_zero_of_readDifferential_eventually_eq_zero
    (v : Place ℂ (modularFunctionFieldOver N ℂ))
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ∀ᶠ z in 𝓝 (0 : ℂ), readDifferential N v ω z = 0) : ω = 0 := by
  haveI := original_place_dCoordGenerates N ℂ v
  suffices hc : v.differentialCoeff ω = 0 by
    rw [← v.differentialCoeff_smul_dCoord ω, hc, zero_smul]
  by_contra hc
  have he : ∀ᶠ z in 𝓝 (0 : ℂ), chartRead N v (v.differentialCoeff ω) z = 0 := by
    filter_upwards [hω, ball_mem_nhds (0 : ℂ) (place_spec N v).1] with z hz hzb
    rwa [readDifferential_eq_coefficient N v ω hzb] at hz
  have htop : meromorphicOrderAt (chartRead N v (v.differentialCoeff ω)) 0 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr (he.filter_mono nhdsWithin_le_nhds)
  have ho := meromorphicOrderAt_place_reading N v hc
  change meromorphicOrderAt (chartRead N v (v.differentialCoeff ω)) 0 = _ at ho
  rw [htop] at ho
  exact WithTop.top_ne_coe ho

end
end Dubon2026.SourceFunctionField.OriginalChart
