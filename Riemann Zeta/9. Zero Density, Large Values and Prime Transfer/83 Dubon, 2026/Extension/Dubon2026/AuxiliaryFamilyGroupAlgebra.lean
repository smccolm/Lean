import Dubon2026.AuxiliaryCharacterGroupAlgebra

/-! One scalar parameter map for the actual finite auxiliary family.
The local quotient groups may differ from prime to prime. This assembles
their existing character maps into the single group algebra required by
the arithmetic patching input for Dubon Theorem 2.6. -/

namespace Dubon2026
noncomputable section

variable {S ι A : Type*} [Fintype S] [Fintype ι] [CommRing A]
  {D : S → Type*} [∀ s, Group (D s)]

/-- Multiply the actual local scalar parameter characters across the
same finite auxiliary set. -/
def auxiliaryFamilyCharacter (κ : ∀ s, D s →* (ι → A)ˣ) : (∀ s, ι → D s) →* Aˣ where
  toFun d := ∏ s, auxiliaryProductCharacter (κ s) (d s)
  map_one' := by simp
  map_mul' d e := by simp [Finset.prod_mul_distrib]

/-- A single auxiliary component retains its original local scalar map. -/
theorem auxiliaryFamilyCharacter_single [DecidableEq S]
    (κ : ∀ s, D s →* (ι → A)ˣ) (s : S) (d : ι → D s) :
    auxiliaryFamilyCharacter κ (Pi.mulSingle s d) = auxiliaryProductCharacter (κ s) d := by
  classical
  change (∏ t, auxiliaryProductCharacter (κ t) ((Pi.mulSingle s d : ∀ t, ι → D t) t)) = _
  simpa only [Pi.mulSingle_eq_same] using
    (Finset.prod_eq_single s
      (f := fun t => auxiliaryProductCharacter (κ t) ((Pi.mulSingle s d : ∀ t, ι → D t) t))
      (fun t _ hts => by simp [Pi.mulSingle_eq_of_ne hts]) (by simp))

variable (O : Type*) [CommRing O] [Algebra O A]

/-- The actual finite family supplies one coefficient group-algebra map. -/
def auxiliaryFamilyGroupAlgebra (κ : ∀ s, D s →* (ι → A)ˣ) :
    MonoidAlgebra O (∀ s, ι → D s) →ₐ[O] A :=
  MonoidAlgebra.lift O A (∀ s, ι → D s) ((Units.coeHom A).comp (auxiliaryFamilyCharacter κ))

/-- The group basis element supported in one prime and one character
coordinate maps to precisely that original inertia scalar. -/
theorem auxiliaryFamilyGroupAlgebra_of_single [DecidableEq S] [DecidableEq ι]
    (κ : ∀ s, D s →* (ι → A)ˣ) (s : S) (i : ι) (d : D s) :
    auxiliaryFamilyGroupAlgebra O κ
      (MonoidAlgebra.of O (∀ s, ι → D s) (Pi.mulSingle s (Pi.mulSingle i d))) =
        (κ s d).val i := by
  rw [auxiliaryFamilyGroupAlgebra, MonoidAlgebra.lift_of, MonoidHom.comp_apply,
    auxiliaryFamilyCharacter_single, auxiliaryProductCharacter_single]
  rfl

/-- The literal arbitrary group-basis value is the product of all
original labelled local inertia scalars. -/
theorem auxiliaryFamilyGroupAlgebra_of
    (κ : ∀ s, D s →* (ι → A)ˣ) (d : ∀ s, ι → D s) :
    auxiliaryFamilyGroupAlgebra O κ (MonoidAlgebra.of O (∀ s, ι → D s) d) =
      ∏ s, ∏ i, (κ s (d s i)).val i := by
  rw [auxiliaryFamilyGroupAlgebra, MonoidAlgebra.lift_of, MonoidHom.comp_apply]
  simp [auxiliaryFamilyCharacter, auxiliaryProductCharacter]

end
end Dubon2026
