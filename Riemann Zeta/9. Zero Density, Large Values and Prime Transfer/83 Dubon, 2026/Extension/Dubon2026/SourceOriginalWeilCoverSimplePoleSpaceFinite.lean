import Dubon2026.SourceOriginalWeilCoverSimplePoleSpace
import Mathlib.RingTheory.Noetherian.Basic

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse ->
meromorphic loop generation for every permitted simple-pole differential.
Reuse the existing simple-pole subspace and finite residue-kernel argument
with the actual cover linear coefficients, residues and finite regular space.
A finite basis will allow one simultaneous integer loop formula to extend
by linearity to all allowed differentials; generation itself remains open. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)

/-- The existing actual differential residues restricted to the allowed pole set. -/
def coverSimplePoleResidues (S : Finset (Place ℂ EE)) :
    coverSimplePoleSpace N n radicand S →ₗ[ℂ] (S → ℂ) :=
  LinearMap.pi fun v => (coverDifferentialResidue N n radicand v.1).comp (coverSimplePoleSpace N n radicand S).subtype

theorem cover_simple_pole_regular_of_residue_zero (v : Place ℂ EE) (θ : Ω[EE⁄ℂ])
    (hp : -1 ≤ v.ordDifferential θ) (hz : coverDifferentialResidue N n radicand v θ = 0) :
    0 ≤ v.ordDifferential θ := by
  by_contra h
  have he : v.ordDifferential θ = -1 := by omega
  exact coverDifferentialResidue_ne_zero_of_simplePole N n radicand v θ he hz

theorem cover_simple_pole_kernel_regular (S : Finset (Place ℂ EE))
    (θ : coverSimplePoleSpace N n radicand S) (h : coverSimplePoleResidues N n radicand S θ = 0) :
    (θ : Ω[EE⁄ℂ]) ∈ regularDifferentials ℂ EE := by
  apply (mem_cover_regularDifferentials_iff_ord_nonneg N n radicand _).mpr
  intro v
  by_cases hv : v ∈ S
  · exact cover_simple_pole_regular_of_residue_zero N n radicand v θ (θ.2 v).1 (congrFun h ⟨v, hv⟩)
  · exact (θ.2 v).2 hv

theorem finite_cover_simplePoleSpace (S : Finset (Place ℂ EE)) :
    FiniteDimensional ℂ (coverSimplePoleSpace N n radicand S) := by
  letI := finite_cover_regularDifferentials N n radicand
  refine (Module.finite_def.mpr ?_ : Module.Finite ℂ (coverSimplePoleSpace N n radicand S))
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (coverSimplePoleResidues N n radicand S)
    (IsNoetherian.noetherian _) ?_
  rw [top_inf_eq]
  let ι : LinearMap.ker (coverSimplePoleResidues N n radicand S) →ₗ[ℂ] regularDifferentials ℂ EE :=
    LinearMap.codRestrict (regularDifferentials ℂ EE)
      ((coverSimplePoleSpace N n radicand S).subtype.comp (LinearMap.ker (coverSimplePoleResidues N n radicand S)).subtype)
      fun θ => cover_simple_pole_kernel_regular N n radicand S θ.1 (LinearMap.mem_ker.mp θ.2)
  have hι : Function.Injective ι := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  letI : Module.Finite ℂ (LinearMap.ker (coverSimplePoleResidues N n radicand S)) :=
    Module.Finite.of_injective ι hι
  exact Module.Finite.iff_fg.mp inferInstance

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
