import Dubon2026.MatrixRepresentationStrictConjugacy
import Mathlib.Algebra.Group.End
import Mathlib.Topology.Algebra.Group.Matrix

/-! # Actual conjugation of whole original continuous matrix representations -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι A : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing A]

/-- Conjugate the whole original representation by the actual invertible change of basis. -/
def matrixRepresentationConjugate (ρ : G →* GeneralLinearGroup ι A)
    (U : GeneralLinearGroup ι A) : G →* GeneralLinearGroup ι A :=
  (MulAut.conj U).toMonoidHom.comp ρ

/-- The genuine conjugated representation evaluates by the original matrix conjugation formula. -/
theorem matrixRepresentationConjugate_apply (ρ : G →* GeneralLinearGroup ι A)
    (U : GeneralLinearGroup ι A) (x : G) :
    matrixRepresentationConjugate ρ U x = U * ρ x * U⁻¹ := rfl

/-- Actual coefficient reduction commutes with conjugating the entire original representation. -/
theorem matrixRepresentationConjugate_map {B : Type} [CommRing B]
    (f : A →+* B) (ρ : G →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A) :
    (GeneralLinearGroup.map f).comp (matrixRepresentationConjugate ρ U) =
      matrixRepresentationConjugate ((GeneralLinearGroup.map f).comp ρ)
        (GeneralLinearGroup.map f U) := by
  apply MonoidHom.ext
  intro x
  change GeneralLinearGroup.map f (U * ρ x * U⁻¹) =
    GeneralLinearGroup.map f U * GeneralLinearGroup.map f (ρ x) *
      (GeneralLinearGroup.map f U)⁻¹
  simp only [map_mul, map_inv]

/-- A genuine change of basis reducing to the identity supplies strict conjugacy of the whole original representations. -/
theorem matrixStrictlyConjugate_conjugate {K : Type} [CommRing K]
    (r : A →+* K) (ρ : G →* GeneralLinearGroup ι A) (U : GeneralLinearGroup ι A)
    (hU : GeneralLinearGroup.map r U = 1) :
    MatrixStrictlyConjugate r ρ (matrixRepresentationConjugate ρ U) :=
  ⟨U, hU, fun _ => rfl⟩

/-- Conjugation by an actual fixed original invertible matrix preserves continuity of the whole representation. -/
theorem matrixRepresentationConjugate_continuous [TopologicalSpace G]
    [TopologicalSpace A] [IsTopologicalRing A]
    (ρ : G →* GeneralLinearGroup ι A) (hρ : Continuous ρ) (U : GeneralLinearGroup ι A) :
    Continuous (matrixRepresentationConjugate ρ U) := by
  change Continuous (fun x => U * ρ x * U⁻¹)
  exact (continuous_const.mul hρ).mul continuous_const

end
end Dubon2026
