import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # The actual finite quotient of a continuous representation with discrete coefficients -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type*} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [DiscreteTopology R]

omit [IsTopologicalGroup G] in
/-- The original kernel is open because the original matrix-entry representation is continuous into the actual discrete matrix space. -/
theorem continuousMatrixRepresentation_isOpen_ker (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) : IsOpen (ρ.ker : Set G) := by
  have he : (ρ.ker : Set G) = (fun g => (ρ g).val) ⁻¹' {1} := by
    ext g
    change ρ g = 1 ↔ (ρ g).val = 1
    constructor
    · intro h
      exact congrArg Units.val h
    · intro h
      apply Units.ext
      exact h
  rw [he]
  exact (isOpen_discrete _).preimage
    ((Units.continuous_val (M := Matrix ι ι R)).comp hρ)

/-- The literal original representation kernel as an actual open normal subgroup. -/
def continuousMatrixRepresentationKernel (ρ : G →* GeneralLinearGroup ι R)
    (hρ : Continuous ρ) : OpenNormalSubgroup G where
  toOpenSubgroup := ⟨ρ.ker, continuousMatrixRepresentation_isOpen_ker ρ hρ⟩
  isNormal' := inferInstance

/-- For an original compact group, the quotient by the actual continuous representation kernel is finite. -/
theorem continuousMatrixRepresentation_quotient_finite [CompactSpace G]
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) : Finite (G ⧸ ρ.ker) :=
  Subgroup.quotient_finite_of_isOpen ρ.ker (continuousMatrixRepresentation_isOpen_ker ρ hρ)

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [DiscreteTopology R] in
/-- The original representation factors exactly through its actual kernel quotient. -/
theorem continuousMatrixRepresentation_factor (ρ : G →* GeneralLinearGroup ι R) :
    (QuotientGroup.kerLift ρ).comp (QuotientGroup.mk' ρ.ker) = ρ := by
  apply MonoidHom.ext
  intro g
  exact QuotientGroup.kerLift_mk ρ g

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [DiscreteTopology R] in
/-- The original representation of the actual kernel quotient is faithful. -/
theorem continuousMatrixRepresentation_quotient_injective (ρ : G →* GeneralLinearGroup ι R) :
    Function.Injective (QuotientGroup.kerLift ρ) := QuotientGroup.kerLift_injective ρ

end
end Dubon2026
