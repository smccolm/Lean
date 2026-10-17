import Dubon2026.OriginalInertiaFixedField
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-! # Containing actual inertia makes the fixed-field prime unramified

The fixed-field Galois equivalence preserves the literal inertia action.
When the fixing subgroup contains inertia, the upper ramification index
is unchanged; the existing tower formula makes the lower index one.
This turns the norm-map inertia containment into actual ramification
control in DUB-17's prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : HeightOneSpectrum (𝓞 L)) (S : Subgroup Gal(L/K))
  (hS : w.asIdeal.inertia Gal(L/K) ≤ S)

/-- If the fixing subgroup contains the original inertia, then the
fixed-field extension has exactly the same inertia elements. -/
def originalFixedFieldInertiaEquiv :
    (w.asIdeal.inertia Gal(L/K)) ≃
      w.asIdeal.inertia Gal(L/IntermediateField.fixedField S) := by
  let e := IntermediateField.subgroupEquivAlgEquiv S
  exact {
    toFun := fun σ => ⟨e ⟨σ.val, hS σ.property⟩, fun a => σ.property a⟩
    invFun := fun τ => ⟨(e.symm τ.val).val, fun a => by
      change (e (e.symm τ.val)) • a - a ∈ w.asIdeal
      rw [e.apply_symm_apply]
      exact τ.property a⟩
    left_inv := fun σ => by
      apply Subtype.ext
      exact congrArg (fun s : S => s.val) (e.symm_apply_apply ⟨σ.val, hS σ.property⟩)
    right_inv := fun τ => Subtype.ext (e.apply_symm_apply τ.val) }

include hS in
/-- A normal fixed-field prime below a prime whose inertia lies in the
fixing subgroup has actual ramification index one. -/
theorem originalFixedField_ramification_one_of_inertia_le [S.Normal]
    (v : HeightOneSpectrum (𝓞 K))
    (q : HeightOneSpectrum (𝓞 (IntermediateField.fixedField S)))
    [w.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver q.asIdeal]
    [q.asIdeal.LiesOver v.asIdeal] :
    v.asIdeal.ramificationIdx q.asIdeal = 1 := by
  letI : IsGalois K (IntermediateField.fixedField S) := IsGalois.of_fixedField_normal_subgroup S
  have he : v.asIdeal.ramificationIdx w.asIdeal = q.asIdeal.ramificationIdx w.asIdeal := by
    rw [← numberField_card_inertia_eq_ramificationIdx v w,
      ← numberField_card_inertia_eq_ramificationIdx q w]
    exact Nat.card_congr (originalFixedFieldInertiaEquiv w S hS)
  have hn : q.asIdeal.ramificationIdx w.asIdeal ≠ 0 := by
    rw [← numberField_card_inertia_eq_ramificationIdx q w]
    exact Nat.card_pos.ne'
  have ht := Ideal.ramificationIdx_algebra_tower' v.asIdeal q.asIdeal w.asIdeal
  rw [he] at ht
  exact (Nat.mul_right_cancel (Nat.pos_of_ne_zero hn) (show v.asIdeal.ramificationIdx q.asIdeal *
    q.asIdeal.ramificationIdx w.asIdeal = 1 * q.asIdeal.ramificationIdx w.asIdeal by
      simpa only [one_mul] using ht.symm))

end
end Dubon2026
