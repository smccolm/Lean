import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Group.Units.Hom

/-! # The actual integral-unit realization of an original field-unit subgroup -/

namespace Dubon2026
noncomputable section

variable {L : Type*} [Field L] (B : Subring L) (U : Subgroup Lˣ)
  (hU : ∀ u ∈ U, (u : L) ∈ B)

/-- An original field-unit subgroup whose values lie in the actual subring
is equivalent to its literal preimage in the subring units. Its original
inverse also lies in the subgroup, so the inverse in the subring is constructed. -/
def subringUnitSubgroupEquiv :
    U.comap (Units.map B.subtype.toMonoidHom) ≃* U := by
  let j := Units.map B.subtype.toMonoidHom
  let V := U.comap j
  let f : V →* U :=
    { toFun v := ⟨j v, v.property⟩
      map_one' := Subtype.ext (map_one j)
      map_mul' v w := Subtype.ext (map_mul j (v : Bˣ) (w : Bˣ)) }
  apply MulEquiv.ofBijective f
  constructor
  · intro v w h
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    exact congrArg (fun z : U => ((z : Lˣ) : L)) h
  · intro u
    let v : Bˣ :=
      { val := ⟨((u : Lˣ) : L), hU u u.property⟩
        inv := ⟨(((u : Lˣ)⁻¹ : Lˣ) : L), hU _ (U.inv_mem u.property)⟩
        val_inv := Subtype.ext (Units.mul_inv (u : Lˣ))
        inv_val := Subtype.ext (Units.inv_mul (u : Lˣ)) }
    have hv : j v = (u : Lˣ) := Units.ext rfl
    refine ⟨⟨v, ?_⟩, ?_⟩
    · change j v ∈ U
      rw [hv]
      exact u.property
    · exact Subtype.ext hv

/-- The constructed unit equivalence preserves the literal original field
coefficient under the original subring inclusion. -/
theorem subringUnitSubgroupEquiv_coefficient
    (v : U.comap (Units.map B.subtype.toMonoidHom)) :
    (((subringUnitSubgroupEquiv B U hU v : U) : Lˣ) : L) =
      (((v : Bˣ) : B) : L) := by
  rfl

end
end Dubon2026
