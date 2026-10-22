import Dubon2026.SourceOriginalPathIntegralLinearCombination
import Dubon2026.SourceOriginalRegularPathPrimitives

/-! DUB-17/18 -> original Abel-Jacobi -> all-simple-pole loop generation.
The existing linear path-integral law assumes global regularity. Here only
regularity on the traversed path is needed: the existing chart-order theorem
propagates coefficient membership locally, and the original evaluation and
coefficient linearity proofs supply finite sums. This discharges the basis
extension needed for differentials with poles outside the path.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem readDifferential_sum_smul_of_coeff_mem {n : ℕ} (v : Place ℂ F)
    (c : Fin n → ℂ) (b : Fin n → Ω[F⁄ℂ])
    (hb : ∀ i, v.differentialCoeff (b i) ∈ v.toValuationSubring) :
    readDifferential N v (∑ i, c i • b i) =ᶠ[𝓝 (0 : ℂ)]
      fun z => ∑ i, c i * readDifferential N v (b i) z := by
  have hm : ∀ i, ∀ᶠ z in 𝓝 (0 : ℂ),
      v.differentialCoeff (b i) ∈ (placeFamily N v z).toValuationSubring := by
    intro i
    apply (place_spec N v).2.2.1.eventually_mem (ball_mem_nhds 0 (place_spec N v).1)
    rw [(place_spec N v).2.1]
    exact hb i
  filter_upwards [Filter.eventually_all.mpr hm, ball_mem_nhds (0 : ℂ) (place_spec N v).1]
    with z hz hzb
  simp only [readDifferential_eq_coefficient N v _ hzb, chartRead,
    original_differentialCoeff_sum_smul]
  exact originalPlaceEval_sum_mul_of_mem N (placeFamily N v z) c
    (fun i => v.differentialCoeff (b i)) hz

theorem isPrimitiveAlong_sum_smul_of_coeff_mem {n : ℕ} (c : Fin n → ℂ)
    (b : Fin n → Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q)
    (hb : ∀ i t, (γ t).differentialCoeff (b i) ∈ (γ t).toValuationSubring)
    (g : Fin n → unitInterval → ℂ) (hg : ∀ i, IsPrimitiveAlong N (b i) γ (g i)) :
    IsPrimitiveAlong N (∑ i, c i • b i) γ (fun t => ∑ i, c i * g i t) := by
  intro t₀
  choose Φ hΦ hgf using fun i => hg i t₀
  refine ⟨fun z => ∑ i, c i * Φ i z, ?_, ?_⟩
  · have hd : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i,
        HasDerivAt (Φ i) (readDifferential N (γ t₀) (b i) z) z := by
      simpa only [placeChart_self] using Filter.eventually_all.mpr hΦ
    rw [placeChart_self]
    filter_upwards [hd, readDifferential_sum_smul_of_coeff_mem N (γ t₀) c b
      (fun i => hb i t₀)] with z hz he
    rw [he]
    exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hz i).const_mul (c i)
  · filter_upwards [Filter.eventually_all.mpr hgf] with t ht
    simp only [ht]

theorem pathIntegral_sum_smul_of_coeff_mem {n : ℕ} (c : Fin n → ℂ)
    (b : Fin n → Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q)
    (hb : ∀ i t, (γ t).differentialCoeff (b i) ∈ (γ t).toValuationSubring) :
    pathIntegral N (∑ i, c i • b i) γ = ∑ i, c i * pathIntegral N (b i) γ := by
  choose g hg using fun i => exists_isPrimitiveAlong_of_coeff_mem N (b i) γ (hb i)
  rw [pathIntegral_eq_of_isPrimitiveAlong N
    (isPrimitiveAlong_sum_smul_of_coeff_mem N c b γ hb g hg)]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pathIntegral_eq_of_isPrimitiveAlong N (hg i)]
  ring

end
end Dubon2026.SourceFunctionField.OriginalChart
