import Dubon2026.SourceOriginalWeilCoverPathIntegralLinearCombination
import Dubon2026.SourceOriginalWeilCoverRegularPathPrimitives

/-! DUB-17/18 -> cover Abel converse -> common coefficients for all simple-pole
differentials. Adapt the existing finite-sum law assuming regularity only on
the traversed path, using the proved actual cover evaluation identities. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand baseDivisor hRadicand hOrders)

theorem readDifferential_sum_smul_of_coeff_mem {kDim : ℕ} (v : Place ℂ EE)
    (c : Fin kDim → ℂ) (b : Fin kDim → Ω[EE⁄ℂ])
    (hb : ∀ i, v.differentialCoeff (b i) ∈ v.toValuationSubring) :
    readDifferential N n radicand baseDivisor hRadicand hOrders v (∑ i, c i • b i) =ᶠ[𝓝 (0 : ℂ)]
      fun z => ∑ i, c i * readDifferential N n radicand baseDivisor hRadicand hOrders v (b i) z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have hm : ∀ i, ∀ᶠ z in 𝓝 (0 : ℂ),
      v.differentialCoeff (b i) ∈ (placeFamily N n radicand baseDivisor hRadicand hOrders v z).toValuationSubring := by
    intro i
    apply (place_spec N n radicand baseDivisor hRadicand hOrders v).2.2.1.eventually_mem (ball_mem_nhds 0 (place_spec N n radicand baseDivisor hRadicand hOrders v).1)
    rw [(place_spec N n radicand baseDivisor hRadicand hOrders v).2.1]
    exact hb i
  filter_upwards [Filter.eventually_all.mpr hm, ball_mem_nhds (0 : ℂ) (place_spec N n radicand baseDivisor hRadicand hOrders v).1]
    with z hz hzb
  simp only [readDifferential_eq_coefficient N n radicand baseDivisor hRadicand hOrders v _ hzb, chartRead,
    cover_differentialCoeff_sum_smul]
  exact cover_eval_sum_mul_of_mem N n radicand (placeFamily N n radicand baseDivisor hRadicand hOrders v z) c
    (fun i => v.differentialCoeff (b i)) hz

theorem isPrimitiveAlong_sum_smul_of_coeff_mem {kDim : ℕ} (c : Fin kDim → ℂ)
    (b : Fin kDim → Ω[EE⁄ℂ]) {P Q : Place ℂ EE} (γ : CoverPath P Q)
    (hb : ∀ i t, (γ t).differentialCoeff (b i) ∈ (γ t).toValuationSubring)
    (g : Fin kDim → unitInterval → ℂ) (hg : ∀ i, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (b i) γ (g i)) :
    IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (∑ i, c i • b i) γ (fun t => ∑ i, c i * g i t) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro t₀
  choose Φ hΦ hgf using fun i => hg i t₀
  refine ⟨fun z => ∑ i, c i * Φ i z, ?_, ?_⟩
  · have hd : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i,
        HasDerivAt (Φ i) (readDifferential N n radicand baseDivisor hRadicand hOrders (γ t₀) (b i) z) z := by
      simpa only [placeChart_self] using Filter.eventually_all.mpr hΦ
    rw [placeChart_self]
    filter_upwards [hd, readDifferential_sum_smul_of_coeff_mem N n radicand baseDivisor hRadicand hOrders (γ t₀) c b
      (fun i => hb i t₀)] with z hz he
    rw [he]
    exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hz i).const_mul (c i)
  · filter_upwards [Filter.eventually_all.mpr hgf] with t ht
    simp only [ht]

theorem pathIntegral_sum_smul_of_coeff_mem {kDim : ℕ} (c : Fin kDim → ℂ)
    (b : Fin kDim → Ω[EE⁄ℂ]) {P Q : Place ℂ EE} (γ : CoverPath P Q)
    (hb : ∀ i t, (γ t).differentialCoeff (b i) ∈ (γ t).toValuationSubring) :
    pathIntegral N n radicand baseDivisor hRadicand hOrders (∑ i, c i • b i) γ = ∑ i, c i * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i) γ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  choose g hg using fun i => exists_isPrimitiveAlong_of_coeff_mem N n radicand baseDivisor hRadicand hOrders (b i) γ (hb i)
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders
    (isPrimitiveAlong_sum_smul_of_coeff_mem N n radicand baseDivisor hRadicand hOrders c b γ hb g hg)]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (hg i)]
  ring

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
