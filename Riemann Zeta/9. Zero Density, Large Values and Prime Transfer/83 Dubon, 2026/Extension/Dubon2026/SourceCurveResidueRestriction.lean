import Dubon2026.SourceCurvePlaceRestriction

/-! DUB-17/18 -> regular differential dimension/local regularity -> finite
residue fields. These are the actual residue fields and maps of restricted
valuation rings. No finiteness or principal-divisor property is assumed here.
Adapted from Def_AlgebraicCurve_DivisorPushPull in
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable {F' : Type*} [Field F'] [Algebra K F'] [Algebra F F']
  [IsScalarTower K F F'] [Algebra.IsIntegral F F'] (w : Place K F')

variable (F) in
/-- The actual inclusion of a restricted valuation ring into the original one. -/
def restrictInclusion : (w.restrict F).toValuationSubring →+* w.toValuationSubring where
  toFun a := ⟨algebraMap F F' (a : F), ValuationSubring.mem_comap.mp a.2⟩
  map_one' := Subtype.ext (map_one (algebraMap F F'))
  map_mul' a b := Subtype.ext (map_mul (algebraMap F F') (a : F) (b : F))
  map_zero' := Subtype.ext (map_zero (algebraMap F F'))
  map_add' a b := Subtype.ext (map_add (algebraMap F F') (a : F) (b : F))

theorem coe_restrictInclusion (a : (w.restrict F).toValuationSubring) :
    ((restrictInclusion F w a : w.toValuationSubring) : F') = algebraMap F F' (a : F) := rfl

instance instIsLocalHomRestrictInclusion : IsLocalHom (restrictInclusion F w) where
  map_nonunit a ha := by
    have ha0 : (a : F) ≠ 0 := by
      rintro h0
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
      have hb' : algebraMap F F' (a : F) * (b : F') = 1 := congrArg Subtype.val hb
      rw [h0, map_zero, zero_mul] at hb'
      exact zero_ne_one hb'
    have hinv : (algebraMap F F' (a : F))⁻¹ ∈ w.toValuationSubring := by
      have hord := w.ord_coe_unit ha.unit
      rw [IsUnit.unit_spec, coe_restrictInclusion] at hord
      apply w.mem_of_ord_nonneg
      rw [w.ord_inv, hord, neg_zero]
    have hmem : (a : F)⁻¹ ∈ (w.restrict F).toValuationSubring := by
      rw [mem_restrict_iff, map_inv₀]
      exact hinv
    exact isUnit_iff_exists_inv.mpr ⟨⟨(a : F)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

variable (F) in
/-- The induced map on actual residue fields. -/
def restrictResidueMap : (w.restrict F).ResidueField →+* w.ResidueField :=
  IsLocalRing.ResidueField.map (restrictInclusion F w)

theorem restrictResidueMap_residue (a : (w.restrict F).toValuationSubring) :
    restrictResidueMap F w (IsLocalRing.residue _ a) =
      IsLocalRing.residue _ (restrictInclusion F w a) :=
  IsLocalRing.ResidueField.map_residue _ _

instance instAlgebraResidueFieldRestrict : Algebra (w.restrict F).ResidueField w.ResidueField :=
  (restrictResidueMap F w).toAlgebra

theorem algebraMap_residueField_eq :
    algebraMap (w.restrict F).ResidueField w.ResidueField = restrictResidueMap F w := rfl

instance instIsScalarTowerResidueFieldRestrict :
    IsScalarTower K (w.restrict F).ResidueField w.ResidueField := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show IsLocalRing.residue _ (algebraMap K w.toValuationSubring a) =
    restrictResidueMap F w (IsLocalRing.residue _ (algebraMap K (w.restrict F).toValuationSubring a))
  rw [restrictResidueMap_residue]
  refine congrArg _ (Subtype.ext ?_)
  show algebraMap K F' a = algebraMap F F' (algebraMap K F a)
  rw [← IsScalarTower.algebraMap_apply]

end
end Dubon2026.SourceCurve.Place
