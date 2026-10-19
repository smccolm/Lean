import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! Scalar group-algebra parameters from the actual auxiliary inertia
characters. The product group records the labelled diagonal characters;
the determinant relation can subsequently be imposed on this same group.
This map is required for the unramified augmentation comparison in the
arithmetic patching route to Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section

variable {D ι A : Type*} [Group D] [Fintype ι] [CommRing A]

/-- The coordinate characters give one scalar character on the genuine
product of the fixed inertia quotient, with its original labels. -/
def auxiliaryProductCharacter (κ : D →* (ι → A)ˣ) : (ι → D) →* Aˣ where
  toFun d := ∏ i, Units.map (Pi.evalRingHom (fun _ : ι => A) i).toMonoidHom (κ (d i))
  map_one' := by simp
  map_mul' d e := by simp [Finset.prod_mul_distrib]

/-- A single coordinate recovers exactly its original labelled character. -/
theorem auxiliaryProductCharacter_single [DecidableEq ι] (κ : D →* (ι → A)ˣ) (i : ι) (d : D) :
    auxiliaryProductCharacter κ (Pi.mulSingle i d) =
      Units.map (Pi.evalRingHom (fun _ : ι => A) i).toMonoidHom (κ d) := by
  classical
  change (∏ j, Units.map (Pi.evalRingHom (fun _ : ι => A) j).toMonoidHom
    (κ ((Pi.mulSingle i d : ι → D) j))) = _
  simpa only [Pi.mulSingle_eq_same] using
    (Finset.prod_eq_single i
      (f := fun j => Units.map (Pi.evalRingHom (fun _ : ι => A) j).toMonoidHom
        (κ ((Pi.mulSingle i d : ι → D) j)))
      (fun j _ hji => by simp [Pi.mulSingle_eq_of_ne hji]) (by simp))

variable (O : Type*) [CommRing O] [Algebra O A]

/-- The actual labelled scalar characters define the coefficient
group-algebra map used for auxiliary deformation parameters. -/
def auxiliaryCharacterGroupAlgebra (κ : D →* (ι → A)ˣ) :
    MonoidAlgebra O (ι → D) →ₐ[O] A :=
  MonoidAlgebra.lift O A (ι → D) ((Units.coeHom A).comp (auxiliaryProductCharacter κ))

/-- The basis element for one coordinate is its literal scalar inertia value. -/
theorem auxiliaryCharacterGroupAlgebra_of_single [DecidableEq ι]
    (κ : D →* (ι → A)ˣ) (i : ι) (d : D) :
    auxiliaryCharacterGroupAlgebra O κ (MonoidAlgebra.of O (ι → D) (Pi.mulSingle i d)) =
      (κ d).val i := by
  rw [auxiliaryCharacterGroupAlgebra, MonoidAlgebra.lift_of, MonoidHom.comp_apply,
    auxiliaryProductCharacter_single]
  rfl

/-- The scalar character value of an arbitrary product coordinate. -/
theorem auxiliaryCharacterGroupAlgebra_of (κ : D →* (ι → A)ˣ) (d : ι → D) :
    auxiliaryCharacterGroupAlgebra O κ (MonoidAlgebra.of O (ι → D) d) =
      ∏ i, (κ (d i)).val i := by
  rw [auxiliaryCharacterGroupAlgebra, MonoidAlgebra.lift_of, MonoidHom.comp_apply]
  simp [auxiliaryProductCharacter]

/-- The literal group-algebra augmentation sends every group basis element to one. -/
def coefficientGroupAlgebraAugmentation (E : Type*) [Monoid E] : MonoidAlgebra O E →ₐ[O] O :=
  MonoidAlgebra.lift O O E 1

/-- Evaluation of the actual augmentation on a group basis element. -/
theorem coefficientGroupAlgebraAugmentation_of {E : Type*} [Monoid E] (d : E) :
    coefficientGroupAlgebraAugmentation O E (MonoidAlgebra.of O E d) = 1 :=
  MonoidAlgebra.lift_of _ d

end
end Dubon2026
