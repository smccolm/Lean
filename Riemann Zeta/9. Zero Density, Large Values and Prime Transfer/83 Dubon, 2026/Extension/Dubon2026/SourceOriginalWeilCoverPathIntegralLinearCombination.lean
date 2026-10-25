import Dubon2026.SourceOriginalWeilCoverDifferentialReadingLinear
import Dubon2026.SourceOriginalWeilCoverPathIntegral

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> raw reciprocity period correction. Reuse the native actual Abel potential and compact maximum-principle argument; only the exact linear and integer-coordinate consumers required for correction are retained. -/
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

theorem isPrimitiveAlong_sum_smul {kDim : ℕ} (c : Fin kDim → ℂ)
    (b : Fin kDim → Ω[EE⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ EE)
    {P Q : Place ℂ EE} (γ : CoverPath P Q) (g : Fin kDim → unitInterval → ℂ)
    (hg : ∀ i, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (b i) γ (g i)) :
    IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (∑ i, c i • b i) γ (fun t => ∑ i, c i * g i t) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro t₀
  choose Φ hΦ hgf using fun i => hg i t₀
  refine ⟨fun z => ∑ i, c i * Φ i z, ?_, ?_⟩
  · have hd : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ i,
        HasDerivAt (Φ i) (readDifferential N n radicand baseDivisor hRadicand hOrders (γ t₀) (b i) z) z := by
      simpa only [placeChart_self] using Filter.eventually_all.mpr hΦ
    rw [placeChart_self]
    filter_upwards [hd, ball_mem_nhds (0 : ℂ) (place_spec N n radicand baseDivisor hRadicand hOrders (γ t₀)).1] with z hz hzb
    rw [readDifferential_sum_smul N n radicand baseDivisor hRadicand hOrders (γ t₀) c b hb hzb]
    exact HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (hz i).const_mul (c i)
  · filter_upwards [Filter.eventually_all.mpr hgf] with t ht
    simp only [ht]

theorem pathIntegral_sum_smul {kDim : ℕ} (c : Fin kDim → ℂ)
    (b : Fin kDim → Ω[EE⁄ℂ]) (hb : ∀ i, b i ∈ regularDifferentials ℂ EE)
    {P Q : Place ℂ EE} (γ : CoverPath P Q) :
    pathIntegral N n radicand baseDivisor hRadicand hOrders (∑ i, c i • b i) γ = ∑ i, c i * pathIntegral N n radicand baseDivisor hRadicand hOrders (b i) γ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  choose g hg using fun i => exists_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (b i) (hb i) γ
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (isPrimitiveAlong_sum_smul N n radicand baseDivisor hRadicand hOrders c b hb γ g hg)]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand baseDivisor hRadicand hOrders (hg i)]
  ring


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
