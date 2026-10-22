import Dubon2026.SourceOriginalConstantFieldPlaces

/-! DUB-17/18 -> original Tate module -> Qbar torsion comparison -> divisor
conorm. The constructed unique place extension is injective and preserves
orders. Original functions have order zero at every complex place outside
this image, by normalizing any nontrivial restricted valuation. These exact
facts ensure a finite pushed-forward divisor is the actual principal divisor.
Adapted from S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_pic0_complex,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, place-map section.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower originalFieldScalarTower

/-- The unique original complex place above the specified arithmetic place. -/
def liftPlace (v : Place Qbar FQ) : Place ℂ FC := (exists_original_extended_place N v).choose

theorem liftPlace_comap (v : Place Qbar FQ) :
    (liftPlace N v).toValuationSubring.comap (fieldMap N) = v.toValuationSubring :=
  (exists_original_extended_place N v).choose_spec.1

theorem mem_liftPlace_iff (v : Place Qbar FQ) (f : FQ) :
    fieldMap N f ∈ (liftPlace N v).toValuationSubring ↔ f ∈ v.toValuationSubring := by
  rw [← liftPlace_comap N v]
  exact Iff.rfl

theorem ord_liftPlace (v : Place Qbar FQ) (f : FQ) :
    (liftPlace N v).ord (fieldMap N f) = v.ord f :=
  (exists_original_extended_place N v).choose_spec.2.1 f

theorem liftPlace_unique {v : Place Qbar FQ} {Q' : Place ℂ FC}
    (h : Q'.toValuationSubring.comap (fieldMap N) = v.toValuationSubring) : Q' = liftPlace N v :=
  (exists_original_extended_place N v).choose_spec.2.2 Q' h

theorem liftPlace_injective : Function.Injective (liftPlace N) := fun v w h =>
  Place.ext (by rw [← liftPlace_comap N v, ← liftPlace_comap N w, h])

theorem exists_eq_liftPlace {w' : Place ℂ FC}
    (hwx : ∃ y : FQ, fieldMap N y ∉ w'.toValuationSubring) : ∃ v, w' = liftPlace N v := by
  letI := finiteDimensional_original N Qbar
  have hV : w'.toValuationSubring.comap (fieldMap N) ≠ ⊤ := by
    intro h
    obtain ⟨y, hy⟩ := hwx
    exact hy (show y ∈ w'.toValuationSubring.comap (fieldMap N) from
      h ▸ ValuationSubring.mem_top y)
  obtain ⟨v, hv⟩ := ConstantField.exists_place_of_finite_coordinate
    (jOver N Qbar) (transcendental_jOver N Qbar) (w'.toValuationSubring.comap (fieldMap N))
    (fun a => by
      change fieldMap N (algebraMap Qbar FQ a) ∈ w'.toValuationSubring
      rw [fieldMap_constants]
      exact w'.algebraMap_mem' _) hV
  exact ⟨v, liftPlace_unique N hv.symm⟩

theorem ord_phi_of_forall_ne {w' : Place ℂ FC} (hoff : ∀ v, w' ≠ liftPlace N v)
    (f : FQ) : w'.ord (fieldMap N f) = 0 := by
  have hall : ∀ y : FQ, fieldMap N y ∈ w'.toValuationSubring := by
    by_contra h
    push Not at h
    obtain ⟨v, hv⟩ := exists_eq_liftPlace N h
    exact hoff v hv
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  exact ConstantField.ord_eq_zero_of_mem_of_inv_mem w' (hall f) (by rw [← map_inv₀]; exact hall f⁻¹)

theorem forall_ne_liftPlace_of_comap_ne {w' : Place ℂ FC}
    (h : ∀ v : Place Qbar FQ,
      w'.toValuationSubring.comap (algebraMap FQ FC) ≠ v.toValuationSubring) :
    ∀ v, w' ≠ liftPlace N v := fun v hv =>
  h v (by rw [hv]; exact liftPlace_comap N v)

theorem forall_comap_ne_of_ne_liftPlace {w' : Place ℂ FC}
    (h : ∀ v, w' ≠ liftPlace N v) (v : Place Qbar FQ) :
    w'.toValuationSubring.comap (algebraMap FQ FC) ≠ v.toValuationSubring := fun hv =>
  h v (liftPlace_unique N hv)


end
end Dubon2026.SourceFunctionField.OriginalConstantField
