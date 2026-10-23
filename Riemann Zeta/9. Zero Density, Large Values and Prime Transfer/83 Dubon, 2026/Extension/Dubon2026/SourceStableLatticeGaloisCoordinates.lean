import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! DUB-17/18 -> actual residual Galois association -> integral action.
Restrict the given field representation to the constructed stable
lattice using the native subrepresentation, then take its genuine basis
matrices. Group inverses make these matrices invertible over the
integer ring itself. -/
namespace Dubon2026
noncomputable section
open Matrix
variable {S E G : Type*} [CommRing S] [CommRing E] [Algebra S E] [Group G]

/-- The original field action viewed as linear over the coefficient integers. -/
def fieldMatrixIntegralAction (ρ : G →* GeneralLinearGroup (Fin 2) E) :
    G →* Module.End S (Fin 2 → E) where
  toFun g := (Matrix.mulVecLin (ρ g).val).restrictScalars S
  map_one' := by ext x i; simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    change (ρ (g * h)).val *ᵥ x = (ρ g).val *ᵥ ((ρ h).val *ᵥ x)
    rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

/-- The actual Galois action on the invariant integral lattice. -/
def stableLatticeGaloisRep (ρ : G →* GeneralLinearGroup (Fin 2) E)
    (L : Submodule S (Fin 2 → E)) (hL : ∀ g x, x ∈ L → (ρ g).val *ᵥ x ∈ L) :
    G →* Module.End S L :=
  Representation.subrepresentation (fieldMatrixIntegralAction (S := S) ρ) L hL

theorem stableLatticeGaloisRep_coe (ρ : G →* GeneralLinearGroup (Fin 2) E)
    (L : Submodule S (Fin 2 → E)) (hL : ∀ g x, x ∈ L → (ρ g).val *ᵥ x ∈ L)
    (g : G) (x : L) :
    (stableLatticeGaloisRep ρ L hL g x : Fin 2 → E) = (ρ g).val *ᵥ (x : Fin 2 → E) := rfl

/-- Integral invertible matrices in an actual basis of the stable rank-two lattice. -/
def stableLatticeGeneralLinearRep (ρ : G →* GeneralLinearGroup (Fin 2) E)
    (L : Submodule S (Fin 2 → E)) (hL : ∀ g x, x ∈ L → (ρ g).val *ᵥ x ∈ L)
    (b : Module.Basis (Fin 2) S L) : G →* GeneralLinearGroup (Fin 2) S :=
  (((LinearMap.toMatrixAlgEquiv b).toRingHom.toMonoidHom).comp
    (stableLatticeGaloisRep ρ L hL)).toHomUnits

theorem stableLatticeGeneralLinearRep_entry (ρ : G →* GeneralLinearGroup (Fin 2) E)
    (L : Submodule S (Fin 2 → E)) (hL : ∀ g x, x ∈ L → (ρ g).val *ᵥ x ∈ L)
    (b : Module.Basis (Fin 2) S L) (g : G) (i j : Fin 2) :
    (stableLatticeGeneralLinearRep ρ L hL b g).val i j =
      b.repr (stableLatticeGaloisRep ρ L hL g (b j)) i := by
  exact LinearMap.toMatrix_apply b b (stableLatticeGaloisRep ρ L hL g) i j

theorem stableLatticeGeneralLinearRep_action (ρ : G →* GeneralLinearGroup (Fin 2) E)
    (L : Submodule S (Fin 2 → E)) (hL : ∀ g x, x ∈ L → (ρ g).val *ᵥ x ∈ L)
    (b : Module.Basis (Fin 2) S L) (g : G) (x : L) :
    (stableLatticeGeneralLinearRep ρ L hL b g).val *ᵥ b.repr x =
      b.repr (stableLatticeGaloisRep ρ L hL g x) :=
  LinearMap.toMatrix_mulVec_repr b b (stableLatticeGaloisRep ρ L hL g) x

end
end Dubon2026
