import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic.Group

/-! # Smallness from finite arithmetic stabilizers and one torsion-free local image

This is the precise group-theoretic implication used in the source's
unitary small-level argument for DUB-17. Only the restriction of the
local projection to the original arithmetic group must be injective.
-/

namespace Dubon2026

noncomputable section

variable {A G L : Type*} [Group A] [Group G] [Group L]

/-- Finite arithmetic stabilizers and a faithful torsion-free local level imply actual smallness. -/
theorem smallLevel_of_finite_stabilizers_local_torsionFree
    (f : A →* G) (U : Subgroup G) (π : G →* L)
    (hfaithful : Function.Injective (π.comp f))
    (hfinite : ∀ g : G, Finite (U.comap ((MulAut.conj g⁻¹).toMonoidHom.comp f)))
    [IsMulTorsionFree (U.map π)] :
    ∀ (g : G) (u : U), g * u.val * g⁻¹ ∈ f.range → u = 1 := by
  intro g u hu
  obtain ⟨a, ha⟩ := hu
  let H := U.comap ((MulAut.conj g⁻¹).toMonoidHom.comp f)
  have hconj : g⁻¹ * f a * g = u.val := by rw [ha]; group
  have haH : a ∈ H := by
    change g⁻¹ * f a * (g⁻¹)⁻¹ ∈ U
    simpa only [inv_inv, hconj] using u.property
  letI : Finite H := hfinite g
  have haorder : IsOfFinOrder a :=
    H.subtype.isOfFinOrder (isOfFinOrder_of_finite (⟨a, haH⟩ : H))
  have huorder : IsOfFinOrder u.val := by
    rw [← hconj]
    simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv] using
      (MulAut.conj g⁻¹).toMonoidHom.isOfFinOrder (f.isOfFinOrder haorder)
  let z : U.map π := ⟨π u.val, ⟨u.val, u.property, rfl⟩⟩
  have hzorder : IsOfFinOrder z :=
    (U.map π).subtype_injective.isOfFinOrder_iff.mp (π.isOfFinOrder huorder)
  have hz : π u.val = 1 := congrArg Subtype.val hzorder.eq_one'
  have haf : (π.comp f) a = (π.comp f) 1 := by
    change π (f a) = π (f 1)
    rw [ha, map_mul, map_mul, map_inv, hz, mul_one, mul_inv_cancel, map_one, map_one]
  have haone := hfaithful haf
  apply Subtype.ext
  change u.val = 1
  rw [← hconj, haone, map_one]
  group

end
end Dubon2026
