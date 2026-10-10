import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Actual local coefficient fiber products and their compatible units -/

namespace Dubon2026
noncomputable section

variable {A B C : Type*} [Ring A] [Ring B] [Ring C]

/-- The genuine ring of pairs of original coefficients with equal images in the original common coefficient ring. -/
abbrev CoefficientFiberProduct (f : A →+* C) (g : B →+* C) :=
  RingHom.eqLocus (f.comp (RingHom.fst A B)) (g.comp (RingHom.snd A B))

/-- First actual projection of the original coefficient fiber product. -/
def coefficientFiberProductFst (f : A →+* C) (g : B →+* C) :
    CoefficientFiberProduct f g →+* A :=
  (RingHom.fst A B).comp (CoefficientFiberProduct f g).subtype

/-- Second actual projection of the original coefficient fiber product. -/
def coefficientFiberProductSnd (f : A →+* C) (g : B →+* C) :
    CoefficientFiberProduct f g →+* B :=
  (RingHom.snd A B).comp (CoefficientFiberProduct f g).subtype

/-- Compatible original coefficient units give a genuine unit of the actual fiber-product ring, with componentwise inverse. -/
def coefficientFiberProductUnit (f : A →+* C) (g : B →+* C)
    (a : Aˣ) (b : Bˣ) (h : Units.map f.toMonoidHom a = Units.map g.toMonoidHom b) :
    (CoefficientFiberProduct f g)ˣ where
  val := ⟨(a.val, b.val), congrArg Units.val h⟩
  inv := ⟨((a⁻¹).val, (b⁻¹).val), by
    have hi : Units.map f.toMonoidHom a⁻¹ = Units.map g.toMonoidHom b⁻¹ := by
      simpa only [map_inv] using congrArg Inv.inv h
    exact congrArg Units.val hi⟩
  val_inv := by
    apply Subtype.ext
    exact Prod.ext a.val_inv b.val_inv
  inv_val := by
    apply Subtype.ext
    exact Prod.ext a.inv_val b.inv_val

/-- The genuine compatible coefficient unit retains both actual original unit projections. -/
theorem coefficientFiberProductUnit_projections (f : A →+* C) (g : B →+* C)
    (a : Aˣ) (b : Bˣ) (h : Units.map f.toMonoidHom a = Units.map g.toMonoidHom b) :
    Units.map (coefficientFiberProductFst f g).toMonoidHom (coefficientFiberProductUnit f g a b h) = a ∧
      Units.map (coefficientFiberProductSnd f g).toMonoidHom (coefficientFiberProductUnit f g a b h) = b := by
  constructor <;> apply Units.ext <;> rfl

/-- Surjectivity of the second actual coefficient map makes the first actual fiber-product projection surjective. -/
theorem coefficientFiberProductFst_surjective (f : A →+* C) (g : B →+* C)
    (hg : Function.Surjective g) : Function.Surjective (coefficientFiberProductFst f g) := by
  intro a
  obtain ⟨b, hb⟩ := hg (f a)
  exact ⟨⟨(a, b), hb.symm⟩, rfl⟩

end

noncomputable section
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- The first actual fiber-product projection reflects units whenever the second original coefficient homomorphism does. -/
theorem coefficientFiberProductFst_isLocalHom (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    IsLocalHom (coefficientFiberProductFst f g) := by
  constructor
  intro x hx
  have hb : IsUnit x.val.2 := by
    apply isUnit_of_map_unit g
    have h : f x.val.1 = g x.val.2 := x.property
    rw [← h]
    exact f.isUnit_map hx
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hb
  have hab : Units.map f.toMonoidHom a = Units.map g.toMonoidHom b := by
    apply Units.ext
    change f (a : A) = g (b : B)
    rw [ha, hb]
    exact x.property
  refine ⟨coefficientFiberProductUnit f g a b hab, ?_⟩
  apply Subtype.ext
  exact Prod.ext ha hb

/-- The original coefficient fiber product is a genuine local ring when its first coefficient ring is local and its second coefficient map reflects units. -/
theorem coefficientFiberProduct_isLocalRing [IsLocalRing A]
    (f : A →+* C) (g : B →+* C) [IsLocalHom g] :
    IsLocalRing (CoefficientFiberProduct f g) := by
  letI := coefficientFiberProductFst_isLocalHom f g
  exact (coefficientFiberProductFst f g).domain_isLocalRing


end
end Dubon2026
