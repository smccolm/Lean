import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.Separable

/-! DUB-17/18 -> original Frobenius/inertia -> residue curve differentials ->
separability of the literal j coordinate. These Frobenius and degree facts
are the inputs to the no-pth-root criterion, used only for that coordinate.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_isCurveOver_modularFunctionFieldFullC.lean,
W5EC2.Criterion. No source resource-limit or linter overrides are imported. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial IntermediateField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem frobenius_image_range_algebraMap
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p] :
    (frobenius L p) '' Set.range (algebraMap K L) = Set.range (algebraMap K L) := by
  ext u
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a ^ p, by rw [map_pow, frobenius_def]⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, rfl⟩ := surjective_frobenius K p a
    exact ⟨algebraMap K L b, ⟨b, rfl⟩, by rw [frobenius_def, frobenius_def, map_pow]⟩

theorem map_frobenius_adjoin_toSubfield
    (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [PerfectRing K p] (S : Set L) :
    (adjoin K S).toSubfield.map (frobenius L p) =
      (adjoin K ((frobenius L p) '' S)).toSubfield := by
  rw [adjoin_toSubfield, adjoin_toSubfield, RingHom.map_field_closure, Set.image_union,
    frobenius_image_range_algebraMap]

theorem map_frobenius_adjoin_toSubfield_le
    (p : ℕ) [Fact p.Prime] [CharP L p] (S : Set L) :
    (adjoin K S).toSubfield.map (frobenius L p) ≤
      (adjoin K ((frobenius L p) '' S)).toSubfield := by
  rw [adjoin_toSubfield, RingHom.map_field_closure, Subfield.closure_le, Set.image_union]
  rintro u (⟨_, ⟨a, rfl⟩, rfl⟩ | hu)
  · exact pow_mem ((adjoin K _).algebraMap_mem a) p
  · exact IntermediateField.subset_adjoin K _ hu

theorem relfinrank_adjoin_simple (F : IntermediateField K L) {a : L}
    (ha : IsIntegral F a) :
    IntermediateField.relfinrank F (restrictScalars K F⟮a⟯) = (minpoly F a).natDegree := by
  have hle : F ≤ restrictScalars K F⟮a⟯ := fun u hu => (algebraMap F F⟮a⟯ ⟨u, hu⟩).2
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  have hext : extendScalars hle = F⟮a⟯ :=
    IntermediateField.restrictScalars_injective K (extendScalars_restrictScalars hle)
  rw [hext, IntermediateField.adjoin.finrank ha]

theorem le_restrictScalars_adjoin (F : IntermediateField K L) (S : Set L) :
    F ≤ restrictScalars K (adjoin F S) := fun u hu => (algebraMap F (adjoin F S) ⟨u, hu⟩).2

end
end Dubon2026.SourceCurve
