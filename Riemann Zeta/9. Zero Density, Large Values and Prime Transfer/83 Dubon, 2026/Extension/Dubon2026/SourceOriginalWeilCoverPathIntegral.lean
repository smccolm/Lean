import Dubon2026.SourceOriginalWeilCoverPathPrimitives

/-! DUB-17/18 -> auxiliary point division -> cover Abel comparison.
The native original-curve path and local Abel arguments are adapted to the
literal Kummer splitting field and its constructed complex manifold.
All path and primitive inputs are proved; Abel inversion and its principal
kernel remain required. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
Def_AlgebraicCurve_ComplexLineIntegral and
S_AlgebraicCurve_exists_ball_abelJacobiVec_sub_sub_mem_pathPeriodLattice.
-/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hr : r ≠ 0)
variable (hrA : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord r = (n : ℤ) * A v)
include A hr hrA

open Classical in
/-- Endpoint difference of an analytic path primitive, when one exists. -/
def pathIntegral (ω : Ω[EE⁄ℂ])
    {P Q : Place ℂ (EE)}
    (γ : @Path (Place ℂ (EE)) (placeTopology N n r A hr hrA) P Q) : ℂ :=
  if h : ∃ g, IsPrimitiveAlong N n r A hr hrA ω γ g then h.choose 1 - h.choose 0 else 0

theorem pathIntegral_eq_of_isPrimitiveAlong
    {ω : Ω[EE⁄ℂ]}
    {P Q : Place ℂ (EE)}
    {γ : @Path (Place ℂ (EE)) (placeTopology N n r A hr hrA) P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N n r A hr hrA ω γ g) :
    pathIntegral N n r A hr hrA ω γ = g 1 - g 0 := by
  have hex : ∃ g, IsPrimitiveAlong N n r A hr hrA ω γ g := ⟨g, hg⟩
  rw [pathIntegral, dif_pos hex]
  have h := hex.choose_spec.sub_eq_initial N n r A hr hrA hg 1
  linear_combination h

theorem IsPrimitiveAlong.add_const
    {ω : Ω[EE⁄ℂ]}
    {P Q : Place ℂ (EE)}
    {γ : @Path (Place ℂ (EE)) (placeTopology N n r A hr hrA) P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N n r A hr hrA ω γ g) (c : ℂ) :
    IsPrimitiveAlong N n r A hr hrA ω γ (fun t => g t + c) := by
  intro t₀
  obtain ⟨Φ, hΦ, hG⟩ := hg t₀
  refine ⟨fun z => Φ z + c, hΦ.mono fun z hz => hz.add_const c, ?_⟩
  exact hG.mono fun t ht => congrArg (· + c) ht

theorem IsPrimitiveAlong.continuous
    {ω : Ω[EE⁄ℂ]}
    {P Q : Place ℂ (EE)}
    {γ : @Path (Place ℂ (EE)) (placeTopology N n r A hr hrA) P Q}
    {g : unitInterval → ℂ} (hg : IsPrimitiveAlong N n r A hr hrA ω γ g) : Continuous g := by
  letI := placeTopology N n r A hr hrA
  apply continuous_iff_continuousAt.mpr
  intro t₀
  obtain ⟨Φ, hΦ, hG⟩ := hg t₀
  have hk := (continuousAt_placeChart N n r A hr hrA (γ t₀) (γ t₀)
    (mem_placeChart_source N n r A hr hrA (γ t₀))).comp γ.continuous.continuousAt
  have hcomp : ContinuousAt (fun t : unitInterval => Φ (placeChart N n r A hr hrA (γ t₀) (γ t))) t₀ :=
    ContinuousAt.comp (f := fun t : unitInterval => placeChart N n r A hr hrA (γ t₀) (γ t))
      hΦ.self_of_nhds.continuousAt hk
  apply hcomp.congr
  filter_upwards [hG] with t ht
  exact ht.symm

theorem exists_normalized_path_primitive (ω : Ω[EE⁄ℂ])
    (hω : ω ∈ regularDifferentials ℂ (EE))
    {P Q : Place ℂ (EE)}
    (γ : @Path (Place ℂ (EE)) (placeTopology N n r A hr hrA) P Q) :
    ∃ g : unitInterval → ℂ, IsPrimitiveAlong N n r A hr hrA ω γ g ∧ Continuous g ∧
      g 0 = 0 ∧ g 1 = pathIntegral N n r A hr hrA ω γ := by
  obtain ⟨g, hg⟩ := exists_isPrimitiveAlong N n r A hr hrA ω hω γ
  have hn := hg.add_const N n r A hr hrA (-g 0)
  refine ⟨fun t => g t + -g 0, hn, hn.continuous N n r A hr hrA, by simp, ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong N n r A hr hrA hg, sub_eq_add_neg]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
