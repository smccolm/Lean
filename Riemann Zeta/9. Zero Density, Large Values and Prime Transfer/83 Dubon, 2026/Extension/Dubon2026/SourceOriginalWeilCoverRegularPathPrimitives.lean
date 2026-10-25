import Dubon2026.SourceOriginalWeilCoverRegularPathLocalPrimitives
import Dubon2026.SourceOriginalWeilCoverPathIntegral
import Dubon2026.SourceOriginalWeilCoverDifferentialResidues

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period exponential and principality. Adapt the native original-curve deduction to the literal cover, using proved chart, residue and meromorphic comparison inputs. No global regularity or completed Abel converse is assumed. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)

theorem exists_isPrimitiveAlong_of_coeff_mem (ω : Ω[EE⁄ℂ])
    {P Q : Place ℂ (EE)}
    (γ : CoverPath P Q)
    (hω : ∀ t, (γ t).differentialCoeff ω ∈ (γ t).toValuationSubring) :
    ∃ g, IsPrimitiveAlong N n radicand A hRadicand hOrders ω γ g := by
  letI := placeTopology N n radicand A hRadicand hOrders
  let c := γ.extend
  have hc : Continuous c := γ.continuous_extend
  have hωc : ∀ t, (c t).differentialCoeff ω ∈ (c t).toValuationSubring :=
    fun t => hω (projIcc 0 1 zero_le_one t)
  have hct : ∀ t : unitInterval, c t = γ t := γ.extend_extends'
  have hk : ∀ t₀ : ℝ, ContinuousAt (fun t => placeChart N n radicand A hRadicand hOrders (c t₀) (c t)) t₀ := fun t₀ =>
    (continuousAt_placeChart N n radicand A hRadicand hOrders (c t₀) (c t₀) (mem_placeChart_source N n radicand A hRadicand hOrders (c t₀))).comp hc.continuousAt
  obtain ⟨G, hG⟩ := exists_isPrimOn_Icc
    (R := fun t z => readDifferential N n radicand A hRadicand hOrders (c t) ω z)
    (k := fun t₀ t => placeChart N n radicand A hRadicand hOrders (c t₀) (c t)) hk
    (fun s => exists_cover_path_local_primitive_of_coeff_mem N n radicand A hRadicand hOrders ω c hc hωc s)
  refine ⟨fun t => G t, fun t₀ => ?_⟩
  obtain ⟨Φ, hΦ, hGt⟩ := hG t₀ t₀.2
  refine ⟨Φ, ?_, ?_⟩
  · have hΦ' : ∀ᶠ z in 𝓝 (placeChart N n radicand A hRadicand hOrders (c t₀) (c t₀)),
        HasDerivAt Φ (readDifferential N n radicand A hRadicand hOrders (c t₀) ω z) z := hΦ
    rwa [hct t₀] at hΦ'
  · have h2 : ∀ᶠ t in 𝓝[unitInterval] (t₀ : ℝ), G t = Φ (placeChart N n radicand A hRadicand hOrders (c t₀) (c t)) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hGt, self_mem_nhdsWithin] with t ht hts
      exact ht hts
    have h3 := (eventually_nhds_subtype_iff unitInterval t₀
      fun t => G t = Φ (placeChart N n radicand A hRadicand hOrders (c t₀) (c t))).2 h2
    filter_upwards [h3] with t ht
    show G t = Φ (placeChart N n radicand A hRadicand hOrders (γ t₀) (γ t))
    rw [ht, hct t₀, hct t]

theorem exists_isPrimitiveAlong_of_simplePole_residue_zero
    (ω : Ω[EE⁄ℂ])
    (hω : ∀ v : Place ℂ (EE), -1 ≤ v.ordDifferential ω)
    {P Q : Place ℂ (EE)}
    (γ : CoverPath P Q)
    (hres : ∀ t, coverDifferentialResidue N n radicand (γ t) ω = 0) :
    ∃ g, IsPrimitiveAlong N n radicand A hRadicand hOrders ω γ g := by
  letI := placeTopology N n radicand A hRadicand hOrders
  apply exists_isPrimitiveAlong_of_coeff_mem N n radicand A hRadicand hOrders ω γ
  intro t
  apply (γ t).mem_of_ord_nonneg
  change 0 ≤ (γ t).ordDifferential ω
  by_contra hn
  have he : (γ t).ordDifferential ω = -1 := by have h := hω (γ t); omega
  exact coverDifferentialResidue_ne_zero_of_simplePole N n radicand (γ t) ω he (hres t)


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
