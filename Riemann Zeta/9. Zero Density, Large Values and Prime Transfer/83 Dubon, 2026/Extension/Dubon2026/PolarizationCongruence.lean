import Dubon2026.PolarizedTwistedDual
import Dubon2026.MatrixRepresentationConjugation

/-! Actual basis change for source polarization matrices. This transports
the CM trace-ring intertwiner back to the universal matrices, where the
proved scalar centralizer establishes symmetry on DUB-17's descent route. -/

namespace Dubon2026
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The actual congruence of polarization matrices under a matrix basis change. -/
def polarizationCongruence (B U : GeneralLinearGroup ι R) : GeneralLinearGroup ι R :=
  U * B * (polarizedContragredient U)⁻¹

/-- The source congruence is the original matrix product U B U-transpose. -/
theorem polarizationCongruence_val (B U : GeneralLinearGroup ι R) :
    (polarizationCongruence B U).val = U.val * B.val * U.val.transpose := rfl

/-- Actual polarization congruence preserves symmetry. -/
theorem polarizationCongruence_symmetric (B U : GeneralLinearGroup ι R)
    (hB : B.val.transpose = B.val) :
    (polarizationCongruence B U).val.transpose = (polarizationCongruence B U).val := by
  rw [polarizationCongruence_val, transpose_mul, transpose_mul, transpose_transpose, hB]
  exact (mul_assoc _ _ _).symm

/-- Reversing the original basis change recovers the same polarization matrix. -/
theorem polarizationCongruence_cancel (B U : GeneralLinearGroup ι R) :
    polarizationCongruence (polarizationCongruence B U) U⁻¹ = B := by
  unfold polarizationCongruence
  rw [map_inv]
  group

/-- Symmetry after an actual invertible congruence implies original symmetry. -/
theorem polarizationCongruence_symmetric_iff (B U : GeneralLinearGroup ι R) :
    (polarizationCongruence B U).val.transpose = (polarizationCongruence B U).val ↔
      B.val.transpose = B.val := by
  constructor
  · intro h
    have he := polarizationCongruence_symmetric (polarizationCongruence B U) U⁻¹ h
    rwa [polarizationCongruence_cancel] at he
  · exact polarizationCongruence_symmetric B U

/-- Twisted duality commutes with an actual whole matrix basis change,
with the inverse-transpose change of basis on the twisted dual. -/
theorem polarizedTwistedDual_conjugate (ρ : G →* GeneralLinearGroup ι R)
    (μ : G →* Rˣ) (U : GeneralLinearGroup ι R) :
    polarizedTwistedDual (matrixRepresentationConjugate ρ U) μ =
      matrixRepresentationConjugate (polarizedTwistedDual ρ μ) (polarizedContragredient U) := by
  apply MonoidHom.ext
  intro g
  simp only [polarizedTwistedDual_apply, matrixRepresentationConjugate_apply, map_mul, map_inv]
  have hc := (polarizedScalar_commute (μ g) (polarizedContragredient U)).eq
  calc
    _ = (GeneralLinearGroup.scalar ι (μ g) * polarizedContragredient U) *
        polarizedContragredient (ρ g) * (polarizedContragredient U)⁻¹ := by simp only [mul_assoc]
    _ = _ := by rw [hc]; simp only [mul_assoc]

/-- Original conjugate duality is carried to the congruent polarization
under the same actual matrix basis change. -/
theorem polarizationCongruence_duality (ρ : G →* GeneralLinearGroup ι R)
    (μ : G →* Rˣ) (c : G →* G) (B U : GeneralLinearGroup ι R)
    (hB : ∀ g, ρ (c g) = B * polarizedTwistedDual ρ μ g * B⁻¹) :
    ∀ g, matrixRepresentationConjugate ρ U (c g) =
      polarizationCongruence B U *
        polarizedTwistedDual (matrixRepresentationConjugate ρ U) μ g *
          (polarizationCongruence B U)⁻¹ := by
  intro g
  rw [polarizedTwistedDual_conjugate]
  simp only [matrixRepresentationConjugate_apply, polarizationCongruence, hB g]
  group

/-- Actual coefficient change carries the entire original conjugate-duality
equation to the mapped matrix, multiplier and polarization. -/
theorem polarization_duality_map {A : Type} [CommRing A]
    (f : R →+* A) (ρ : G →* GeneralLinearGroup ι R) (μ : G →* Rˣ)
    (c : G →* G) (B : GeneralLinearGroup ι R)
    (hB : ∀ g, ρ (c g) = B * polarizedTwistedDual ρ μ g * B⁻¹) :
    ∀ g, ((GeneralLinearGroup.map f).comp ρ) (c g) = GeneralLinearGroup.map f B *
      polarizedTwistedDual ((GeneralLinearGroup.map f).comp ρ)
        ((Units.map f.toMonoidHom).comp μ) g * (GeneralLinearGroup.map f B)⁻¹ := by
  intro g
  have he := congrArg (GeneralLinearGroup.map f) (hB g)
  rw [map_mul, map_mul, map_inv] at he
  have hd := DFunLike.congr_fun (polarizedTwistedDual_map f ρ μ) g
  exact he.trans (congrArg (fun x => GeneralLinearGroup.map f B * x *
    (GeneralLinearGroup.map f B)⁻¹) hd)

end Dubon2026
