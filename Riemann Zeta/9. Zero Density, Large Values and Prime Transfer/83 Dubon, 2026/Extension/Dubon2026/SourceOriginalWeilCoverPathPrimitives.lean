import Dubon2026.SourceOriginalWeilCoverPathLocalPrimitives
import Mathlib.Topology.Path
import Mathlib.Topology.LocallyConstant.Basic

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel comparison.
Adapt the proved original-curve coordinate and primitive arguments to the
literal Kummer cover, using its constructed charts and finite coordinate.
The primitive gluing argument is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_exists_isPrimitiveAlong_of_mem_regularDifferentials.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set KaehlerDifferential OriginalPrimitiveGlue
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

/-- A local analytic primitive along an actual continuous cover-place path. -/
def IsPrimitiveAlong (ω : Ω[EE⁄ℂ])
    {P Q : Place ℂ (EE)}
    (γ : @Path (Place ℂ (EE)) (placeTopology N n r A hr hrA) P Q)
    (g : unitInterval → ℂ) : Prop :=
  ∀ t₀ : unitInterval, ∃ Φ : ℂ → ℂ,
    (∀ᶠ z in 𝓝 (placeChart N n r A hr hrA (γ t₀) (γ t₀)),
      HasDerivAt Φ (readDifferential N n r A hr hrA (γ t₀) ω z) z) ∧
      ∀ᶠ t in 𝓝 t₀, g t = Φ (placeChart N n r A hr hrA (γ t₀) (γ t))

theorem exists_isPrimitiveAlong (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE))
    {P Q : Place ℂ (EE)}
    (γ : @Path (Place ℂ (EE)) (placeTopology N n r A hr hrA) P Q) :
    ∃ g, IsPrimitiveAlong N n r A hr hrA ω γ g := by
  letI := placeTopology N n r A hr hrA
  let c := γ.extend
  have hc : Continuous c := γ.continuous_extend
  have hct : ∀ t : unitInterval, c t = γ t := γ.extend_extends'
  have hk : ∀ t₀ : ℝ, ContinuousAt (fun t => placeChart N n r A hr hrA (c t₀) (c t)) t₀ := fun t₀ =>
    (continuousAt_placeChart N n r A hr hrA (c t₀) (c t₀) (mem_placeChart_source N n r A hr hrA (c t₀))).comp hc.continuousAt
  obtain ⟨G, hG⟩ := exists_isPrimOn_Icc
    (R := fun t z => readDifferential N n r A hr hrA (c t) ω z)
    (k := fun t₀ t => placeChart N n r A hr hrA (c t₀) (c t)) hk
    (fun s => exists_cover_path_local_primitive N n r A hr hrA ω hω c hc s)
  refine ⟨fun t => G t, fun t₀ => ?_⟩
  obtain ⟨Φ, hΦ, hGt⟩ := hG t₀ t₀.2
  refine ⟨Φ, ?_, ?_⟩
  · have hΦ' : ∀ᶠ z in 𝓝 (placeChart N n r A hr hrA (c t₀) (c t₀)),
        HasDerivAt Φ (readDifferential N n r A hr hrA (c t₀) ω z) z := hΦ
    rwa [hct t₀] at hΦ'
  · have h2 : ∀ᶠ t in 𝓝[unitInterval] (t₀ : ℝ), G t = Φ (placeChart N n r A hr hrA (c t₀) (c t)) := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hGt, self_mem_nhdsWithin] with t ht hts
      exact ht hts
    have h3 := (eventually_nhds_subtype_iff unitInterval t₀
      fun t => G t = Φ (placeChart N n r A hr hrA (c t₀) (c t))).2 h2
    filter_upwards [h3] with t ht
    show G t = Φ (placeChart N n r A hr hrA (γ t₀) (γ t))
    rw [ht, hct t₀, hct t]

theorem IsPrimitiveAlong.sub_eq_initial
    {ω : Ω[EE⁄ℂ]}
    {P Q : Place ℂ (EE)}
    {γ : @Path (Place ℂ (EE)) (placeTopology N n r A hr hrA) P Q}
    {g g' : unitInterval → ℂ}
    (hg : IsPrimitiveAlong N n r A hr hrA ω γ g) (hg' : IsPrimitiveAlong N n r A hr hrA ω γ g') (t : unitInterval) :
    g t - g' t = g 0 - g' 0 := by
  letI := placeTopology N n r A hr hrA
  have hlc : IsLocallyConstant (fun t => g t - g' t) := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun t₀ => ?_
    obtain ⟨Φ, hΦ, hgt⟩ := hg t₀
    obtain ⟨Φ', hΦ', hgt'⟩ := hg' t₀
    have hk : ContinuousAt (fun t : unitInterval => placeChart N n r A hr hrA (γ t₀) (γ t)) t₀ :=
      (continuousAt_placeChart N n r A hr hrA (γ t₀) (γ t₀) (mem_placeChart_source N n r A hr hrA (γ t₀))).comp
        γ.continuous.continuousAt
    have hsub := hk.eventually (eventually_sub_eq_of_hasDerivAt hΦ hΦ')
    filter_upwards [hgt, hgt', hsub] with u hu hu' hus
    show g u - g' u = g t₀ - g' t₀
    rw [hu, hu', hgt.self_of_nhds, hgt'.self_of_nhds]
    exact hus
  exact hlc.apply_eq_of_preconnectedSpace t 0

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
