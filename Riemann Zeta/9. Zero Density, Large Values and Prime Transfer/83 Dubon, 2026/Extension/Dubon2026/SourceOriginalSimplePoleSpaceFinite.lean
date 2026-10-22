import Dubon2026.SourceOriginalSimplePoleSpace
import Dubon2026.SourceOriginalRegularFinite
import Dubon2026.SourceOriginalRegularOrders
import Mathlib.RingTheory.Noetherian.Basic

/-! DUB-17/18 -> original Abel-Jacobi -> meromorphic loop-period generation.
The existing linear residues map the exact simple-pole space to finitely many
complex coordinates. Its kernel injects into the already finite original
regular differentials. Native finite-module arguments give a finite-dimensional
space, with no new residue-linearity or bounded-divisor hypothesis.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

/-- The existing actual differential residues restricted to the allowed pole set. -/
def originalSimplePoleResidues (S : Finset (Place ℂ F)) :
    originalSimplePoleSpace N S →ₗ[ℂ] (S → ℂ) :=
  LinearMap.pi fun v => (originalDifferentialResidue N v.1).comp (originalSimplePoleSpace N S).subtype

theorem original_simple_pole_regular_of_residue_zero (v : Place ℂ F) (θ : Ω[F⁄ℂ])
    (hp : -1 ≤ v.ordDifferential θ) (hz : originalDifferentialResidue N v θ = 0) :
    0 ≤ v.ordDifferential θ := by
  by_contra h
  have he : v.ordDifferential θ = -1 := by omega
  exact originalDifferentialResidue_ne_zero_of_simplePole N v θ he hz

theorem original_simple_pole_kernel_regular (S : Finset (Place ℂ F))
    (θ : originalSimplePoleSpace N S) (h : originalSimplePoleResidues N S θ = 0) :
    (θ : Ω[F⁄ℂ]) ∈ regularDifferentials ℂ F := by
  apply (mem_original_regularDifferentials_iff_ord_nonneg N ℂ _).mpr
  intro v
  by_cases hv : v ∈ S
  · exact original_simple_pole_regular_of_residue_zero N v θ (θ.2 v).1 (congrFun h ⟨v, hv⟩)
  · exact (θ.2 v).2 hv

theorem finite_original_simplePoleSpace (S : Finset (Place ℂ F)) :
    FiniteDimensional ℂ (originalSimplePoleSpace N S) := by
  letI := finite_original_regularDifferentials N ℂ
  refine (Module.finite_def.mpr ?_ : Module.Finite ℂ (originalSimplePoleSpace N S))
  refine Submodule.fg_of_fg_map_of_fg_inf_ker (originalSimplePoleResidues N S)
    (IsNoetherian.noetherian _) ?_
  rw [top_inf_eq]
  let ι : LinearMap.ker (originalSimplePoleResidues N S) →ₗ[ℂ] regularDifferentials ℂ F :=
    LinearMap.codRestrict (regularDifferentials ℂ F)
      ((originalSimplePoleSpace N S).subtype.comp (LinearMap.ker (originalSimplePoleResidues N S)).subtype)
      fun θ => original_simple_pole_kernel_regular N S θ.1 (LinearMap.mem_ker.mp θ.2)
  have hι : Function.Injective ι := by
    intro a b hab
    have h := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h)
  letI : Module.Finite ℂ (LinearMap.ker (originalSimplePoleResidues N S)) :=
    Module.Finite.of_injective ι hι
  exact Module.Finite.iff_fg.mp inferInstance

end
end Dubon2026.SourceFunctionField
