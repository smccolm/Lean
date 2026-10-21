import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> parabolic Hecke realization -> period surjectivity ->
matching cusp-form lower dimension bound -> regular differential realization.
This selects the original Laurent-series modular function field and its
literal j series. The analytic modularity and finite extension are assembled in
SourceOriginalDifferentialInjectivity. Regularity, geometric genus and
cusp-form realization remain separate proof obligations.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_LaurentCoeff.lean, coefficient map and base change.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open HahnSeries IntermediateField

section CoeffMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Apply the original coefficient ring homomorphism to each Laurent coefficient. -/
def coeffMap (f : R →+* S) : LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_zero' := by
    ext k
    simp
  map_one' := by
    ext k
    simp [HahnSeries.coeff_one, apply_ite f]
  map_add' x y := by
    ext k
    simp
  map_mul' x y := by
    have h := HahnSeries.map_mul (f := (f : R →ₙ+* S)) (x := x) (y := y)
    have hx : ∀ z : LaurentSeries R, z.map (f : R →ₙ+* S) = z.map f := fun z =>
      HahnSeries.ext rfl
    rwa [hx, hx, hx] at h

@[simp]
theorem coeffMap_coeff (f : R →+* S) (x : LaurentSeries R) (k : ℤ) :
    (coeffMap f x).coeff k = f (x.coeff k) :=
  rfl

@[simp]
theorem coeffMap_single (f : R →+* S) (k : ℤ) (r : R) :
    coeffMap f (HahnSeries.single k r) = HahnSeries.single k (f r) := by
  ext m
  rcases eq_or_ne m k with rfl | hm
  · simp [HahnSeries.coeff_single_same]
  · simp [HahnSeries.coeff_single_of_ne hm]

theorem coeffMap_coeffMap (g : S →+* T) (f : R →+* S) (x : LaurentSeries R) :
    coeffMap g (coeffMap f x) = coeffMap (g.comp f) x := by
  ext k
  simp

@[simp]
theorem coeffMap_id (x : LaurentSeries R) : coeffMap (RingHom.id R) x = x := by
  ext k
  simp

theorem coeffMap_congr {f g : R →+* S} (h : f = g) (x : LaurentSeries R) :
    coeffMap f x = coeffMap g x := by
  subst h; rfl

end CoeffMap

section BaseChange
variable (L : Type*) [Field L] [Algebra ℚ L]

/-- The rational coefficient embedding into the specified scalar field. -/
def coeffEmb : LaurentSeries ℚ →+* LaurentSeries L :=
  coeffMap (algebraMap ℚ L)

@[simp] theorem coeffEmb_coeff (x : LaurentSeries ℚ) (k : ℤ) :
    (coeffEmb L x).coeff k = algebraMap ℚ L (x.coeff k) := rfl

variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
/-- The scalar-field adjoin of the actual embedded original function field. -/
def laurentBaseChange : IntermediateField L (LaurentSeries L) :=
  IntermediateField.adjoin L (⇑(coeffEmb L) '' (F₀ : Set (LaurentSeries ℚ)))

variable {F₀} in

theorem coeffEmb_mem_laurentBaseChange {x : LaurentSeries ℚ} (hx : x ∈ F₀) :
    coeffEmb L x ∈ laurentBaseChange L F₀ :=
  IntermediateField.subset_adjoin L _ ⟨x, hx, rfl⟩

end BaseChange

end
end Dubon2026.SourceFunctionField
