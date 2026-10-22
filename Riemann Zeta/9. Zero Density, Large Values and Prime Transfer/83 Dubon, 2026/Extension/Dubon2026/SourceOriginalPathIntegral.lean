import Dubon2026.SourceOriginalPathPrimitives

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi -> actual periods.
Define integration by endpoint differences of analytic path primitives.
The preceding existence theorem proves that the primitive branch applies
to every original regular differential, and uniqueness makes its value
independent of the chosen primitive. Normalized primitives realize the
integral and are continuous along the actual path.
The total definition follows Definitions/Def_AlgebraicCurve_ComplexLineIntegral
in anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]

open Classical in
/-- Endpoint difference of an analytic path primitive, when one exists. -/
def pathIntegral (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)}
    (γ : @Path (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) P Q) : ℂ :=
  if h : ∃ g, IsPrimitiveAlong N ω γ g then h.choose 1 - h.choose 0 else 0

theorem pathIntegral_eq_of_isPrimitiveAlong
    {ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ]}
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)}
    {γ : @Path (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N ω γ g) :
    pathIntegral N ω γ = g 1 - g 0 := by
  have hex : ∃ g, IsPrimitiveAlong N ω γ g := ⟨g, hg⟩
  rw [pathIntegral, dif_pos hex]
  have h := hex.choose_spec.sub_eq_initial N hg 1
  linear_combination h

theorem IsPrimitiveAlong.add_const
    {ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ]}
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)}
    {γ : @Path (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N ω γ g) (c : ℂ) :
    IsPrimitiveAlong N ω γ (fun t => g t + c) := by
  intro t₀
  obtain ⟨Φ, hΦ, hG⟩ := hg t₀
  refine ⟨fun z => Φ z + c, hΦ.mono fun z hz => hz.add_const c, ?_⟩
  exact hG.mono fun t ht => congrArg (· + c) ht

theorem IsPrimitiveAlong.continuous
    {ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ]}
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)}
    {γ : @Path (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N ω γ g) : Continuous g := by
  letI := placeTopology N
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨Φ, hΦ, hG⟩ := hg t₀
  have hk := (continuousAt_placeChart N (γ t₀) (γ t₀)
    (mem_placeChart_source N (γ t₀))).comp γ.continuous.continuousAt
  have hcomp : ContinuousAt (fun t : unitInterval => Φ (placeChart N (γ t₀) (γ t))) t₀ :=
    ContinuousAt.comp (f := fun t : unitInterval => placeChart N (γ t₀) (γ t))
      hΦ.self_of_nhds.continuousAt hk
  apply hcomp.congr
  filter_upwards [hG] with t ht
  exact ht.symm

theorem exists_normalized_path_primitive (ω : Ω[modularFunctionFieldOver N ℂ⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (modularFunctionFieldOver N ℂ))
    {P Q : Place ℂ (modularFunctionFieldOver N ℂ)}
    (γ : @Path (Place ℂ (modularFunctionFieldOver N ℂ)) (placeTopology N) P Q) :
    ∃ g : unitInterval → ℂ, IsPrimitiveAlong N ω γ g ∧ Continuous g ∧
      g 0 = 0 ∧ g 1 = pathIntegral N ω γ := by
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong N ω hω γ
  have hn := hg.add_const N (-g 0)
  refine ⟨fun t => g t + -g 0, hn, hn.continuous N, by simp, ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong N hg, sub_eq_add_neg]

end
end Dubon2026.SourceFunctionField.OriginalChart
