import Dubon2026.SourceOriginalRegularPathLocalPrimitives
import Dubon2026.SourceOriginalPathIntegral
import Dubon2026.SourceOriginalDifferentialResidues

/-! DUB-17/18 -> Abel-Jacobi converse -> period correction and meromorphic
exponential. Along a continuous path regularity at each traversed original
place supplies small primitives. Actual coordinate changes transport them
to the charts used by the existing path-integral definition. The primitive
disk is shrunk locally; global regularity is not required or inferred.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N]

theorem exists_isPrimitiveAlong_of_coeff_mem (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)}
    (γ : @Path (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) P Q)
    (hω : ∀ t, (γ t).differentialCoeff ω ∈ (γ t).toValuationSubring) :
    ∃ g, IsPrimitiveAlong N ω γ g := by
  letI := placeTopology N
  let c := γ.extend
  have hc : Continuous c := γ.continuous_extend
  have hωc : ∀ t, (c t).differentialCoeff ω ∈ (c t).toValuationSubring :=
    fun t => hω (projIcc 0 1 zero_le_one t)
  have hct : ∀ t : unitInterval, c t = γ t := γ.extend_extends'
  have hk : ∀ t₀ : ℝ, ContinuousAt (fun t => placeChart N (c t₀) (c t)) t₀ := fun t₀ =>
    (continuousAt_placeChart N (c t₀) (c t₀) (mem_placeChart_source N (c t₀))).comp hc.continuousAt
  obtain ⟨G, hG⟩ := exists_isPrimOn_Icc
    (R := fun t z => readDifferential N (c t) ω z)
    (k := fun t₀ t => placeChart N (c t₀) (c t)) hk
    (fun s => exists_original_path_local_primitive_of_coeff_mem N ω c hc hωc s)
  refine ⟨fun t => G t, fun t₀ => ?_⟩
  obtain ⟨Φ, hΦ, hGt⟩ := hG t₀ t₀.2
  refine ⟨Φ, ?_, ?_⟩
  · have hΦ' : ∀ᶠ z in 𝓝 (placeChart N (c t₀) (c t₀)),
        HasDerivAt Φ (readDifferential N (c t₀) ω z) z := hΦ
    rwa [hct t₀] at hΦ'
  · have h2 : ∀ᶠ t in 𝓝[unitInterval] (t₀ : ℝ), G t = Φ (placeChart N (c t₀) (c t)) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hGt, self_mem_nhdsWithin] with t ht hts
      exact ht hts
    have h3 := (eventually_nhds_subtype_iff unitInterval t₀
      fun t => G t = Φ (placeChart N (c t₀) (c t))).2 h2
    filter_upwards [h3] with t ht
    show G t = Φ (placeChart N (γ t₀) (γ t))
    rw [ht, hct t₀, hct t]

theorem exists_isPrimitiveAlong_of_simplePole_residue_zero
    (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), -1 ≤ v.ordDifferential ω)
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)}
    (γ : @Path (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) P Q)
    (hres : ∀ t, originalDifferentialResidue N (γ t) ω = 0) :
    ∃ g, IsPrimitiveAlong N ω γ g := by
  apply exists_isPrimitiveAlong_of_coeff_mem N ω γ
  intro t
  apply (γ t).mem_of_ord_nonneg
  change 0 ≤ (γ t).ordDifferential ω
  by_contra hn
  have he : (γ t).ordDifferential ω = -1 := by have h := hω (γ t); omega
  exact originalDifferentialResidue_ne_zero_of_simplePole N (γ t) ω he (hres t)

end
end Dubon2026.SourceFunctionField.OriginalChart
