import Dubon2026.SourceGammaOneDiamondFieldRatios
import Dubon2026.SourceGammaOneFieldCuspGerm

/-! DUB-17/18 -> original all-weight association -> arithmetic Gamma1
diamond/Picard comparison -> original complex field diamond.
The native cusp germ is injective because the source is the actual field.
The proved translated-ratio existence supplies a map whose field laws
follow from that injectivity and the already proved germ algebra.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open CongruenceSubgroup UpperHalfPlane Filter
open scoped MatrixGroups Topology
variable (M : ℕ) [NeZero M]

/-- The element of the original field realized by the literal diamond translate. -/
def diamondFieldValue (g : Gamma0 M) (x : functionFieldOver (Gamma1 M) ℂ) :
    functionFieldOver (Gamma1 M) ℂ :=
  (exists_diamond_field_cusp_realization M g x).choose

theorem diamondFieldValue_cuspGerm (g : Gamma0 M)
    (x : functionFieldOver (Gamma1 M) ℂ) (δ : SL(2, ℤ)) :
    fieldCuspGerm M δ (diamondFieldValue M g x) = fieldCuspGerm M (g.val * δ) x :=
  Germ.coe_eq.mpr ((exists_diamond_field_cusp_realization M g x).choose_spec δ)

/-- The actual complex function-field diamond, obtained from modular translation. -/
def diamondFieldHom (g : Gamma0 M) :
    functionFieldOver (Gamma1 M) ℂ →+* functionFieldOver (Gamma1 M) ℂ where
  toFun := diamondFieldValue M g
  map_zero' := by
    apply (fieldCuspGerm M 1).injective
    rw [diamondFieldValue_cuspGerm, map_zero, map_zero]
  map_one' := by
    apply (fieldCuspGerm M 1).injective
    rw [diamondFieldValue_cuspGerm, map_one, map_one]
  map_add' x y := by
    apply (fieldCuspGerm M 1).injective
    rw [diamondFieldValue_cuspGerm, map_add, map_add,
      diamondFieldValue_cuspGerm, diamondFieldValue_cuspGerm]
  map_mul' x y := by
    apply (fieldCuspGerm M 1).injective
    rw [diamondFieldValue_cuspGerm, map_mul, map_mul,
      diamondFieldValue_cuspGerm, diamondFieldValue_cuspGerm]

theorem diamondFieldHom_cuspGerm (g : Gamma0 M)
    (x : functionFieldOver (Gamma1 M) ℂ) (δ : SL(2, ℤ)) :
    fieldCuspGerm M δ (diamondFieldHom M g x) = fieldCuspGerm M (g.val * δ) x :=
  diamondFieldValue_cuspGerm M g x δ

theorem diamondFieldHom_constants (g : Gamma0 M) (c : ℂ) :
    diamondFieldHom M g (algebraMap ℂ (functionFieldOver (Gamma1 M) ℂ) c) =
      algebraMap ℂ (functionFieldOver (Gamma1 M) ℂ) c := by
  apply (fieldCuspGerm M 1).injective
  rw [diamondFieldHom_cuspGerm, fieldCuspGerm_algebraMap, fieldCuspGerm_algebraMap]

theorem diamondFieldHom_one (x : functionFieldOver (Gamma1 M) ℂ) :
    diamondFieldHom M 1 x = x := by
  apply (fieldCuspGerm M 1).injective
  rw [diamondFieldHom_cuspGerm]
  rfl

theorem diamondFieldHom_mul (g h : Gamma0 M) (x : functionFieldOver (Gamma1 M) ℂ) :
    diamondFieldHom M g (diamondFieldHom M h x) = diamondFieldHom M (h * g) x := by
  apply (fieldCuspGerm M 1).injective
  rw [diamondFieldHom_cuspGerm, diamondFieldHom_cuspGerm, diamondFieldHom_cuspGerm]
  change fieldCuspGerm M (h.val * (g.val * 1)) x =
    fieldCuspGerm M (h.val * g.val * 1) x
  rw [mul_assoc]

/-- The original complex field automorphism induced by a Gamma0 diamond lift. -/
def diamondFieldAut (g : Gamma0 M) :
    functionFieldOver (Gamma1 M) ℂ ≃ₐ[ℂ] functionFieldOver (Gamma1 M) ℂ where
  __ := diamondFieldHom M g
  invFun := diamondFieldHom M g⁻¹
  left_inv x := by
    change diamondFieldHom M g⁻¹ (diamondFieldHom M g x) = x
    rw [diamondFieldHom_mul, mul_inv_cancel, diamondFieldHom_one]
  right_inv x := by
    change diamondFieldHom M g (diamondFieldHom M g⁻¹ x) = x
    rw [diamondFieldHom_mul, inv_mul_cancel, diamondFieldHom_one]
  commutes' := diamondFieldHom_constants M g

end
end Dubon2026.SourceFunctionField.GammaOne
