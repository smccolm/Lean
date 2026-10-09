import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # The actual group-algebra action of a matrix representation -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R S : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    [CommRing R] [CommRing S]

/-- Extend the original matrix representation by linearity to its genuine group algebra. -/
def groupAlgebraMatrix (ρ : G →* GeneralLinearGroup ι R) :
    MonoidAlgebra R G →ₐ[R] Matrix ι ι R :=
  MonoidAlgebra.lift R (Matrix ι ι R) G ((Units.coeHom _).comp ρ)

/-- A single original group-algebra term acts by its coefficient times its original matrix. -/
theorem groupAlgebraMatrix_single (ρ : G →* GeneralLinearGroup ι R) (g : G) (a : R) :
    groupAlgebraMatrix ρ (MonoidAlgebra.single g a) = a • (ρ g).val :=
  MonoidAlgebra.lift_single _ _ _

/-- Entrywise coefficient change commutes with the original group-algebra matrix action. -/
theorem groupAlgebraMatrix_map (ρ : G →* GeneralLinearGroup ι R)
    (φ : R →+* S) (x : MonoidAlgebra R G) :
    φ.mapMatrix (groupAlgebraMatrix ρ x) =
      groupAlgebraMatrix ((GeneralLinearGroup.map φ).comp ρ)
        (MonoidAlgebra.mapRingHom G φ x) := by
  have he : φ.mapMatrix.comp (groupAlgebraMatrix ρ).toRingHom =
      (groupAlgebraMatrix ((GeneralLinearGroup.map φ).comp ρ)).toRingHom.comp
        (MonoidAlgebra.mapRingHom G φ) := by
    apply MonoidAlgebra.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, MonoidAlgebra.mapRingHom_single, groupAlgebraMatrix_single]
      ext i j
      by_cases h : i = j <;>
        simp [GeneralLinearGroup.map, Matrix.smul_apply, h]
    · intro g
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, MonoidAlgebra.mapRingHom_single, groupAlgebraMatrix_single]
      ext i j
      simp [GeneralLinearGroup.map]
  exact RingHom.congr_fun he x

end
end Dubon2026
