import Dubon2026.SourceGammaOneHeckeFieldInclusion
import Dubon2026.SourceGammaOneCurveFinite

/-! DUB-17/18 -> original all-weight adic association -> arithmetic Gamma1
realization -> actual geometric Hecke correspondence. These are the two
literal scalar-extended field maps. The second map is proved to preserve
the field; it has no conditional fallback or unproved preservation input. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open IntermediateField

variable (L : Type*) [Field L] [Algebra ℚ L]

theorem gamma1_over_degeneracy_map_le (M d : ℕ) [NeZero d] :
    (laurentBaseChange L (x1FunctionField M)).map (qExpandAlgHom L d) ≤
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (d * M)) := by
  rw [laurentBaseChange, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
  change qExpand L d (coeffMap (algebraMap ℚ L) z) ∈ _
  rw [← coeffMap_qExpand]
  exact coeffEmb_mem_laurentBaseChange L (gamma1_degeneracy_map_le ℚ M d ⟨z, hz, rfl⟩)

/-- The first actual Gamma1 Hecke field map is the inclusion. -/
def heckeAlpha (M d : ℕ) :
    laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (d * M)) :=
  IntermediateField.inclusion (gamma1_hecke_baseChange_le M (d * M) L)

@[simp] theorem heckeAlpha_coe (M d : ℕ)
    (x : laurentBaseChange L (x1FunctionField M)) :
    (heckeAlpha L M d x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

/-- The second actual Gamma1 Hecke field map is the literal substitution q to q^d. -/
def heckeBeta (M d : ℕ) [NeZero d] :
    laurentBaseChange L (x1FunctionField M) →ₐ[L]
      laurentBaseChange L (x1x0FunctionFieldC ℚ M (d * M)) where
  toFun x := ⟨qExpand L d x, gamma1_over_degeneracy_map_le L M d ⟨x, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one (qExpand L d))
  map_mul' x y := Subtype.ext (map_mul (qExpand L d) (x : LaurentSeries L) (y : LaurentSeries L))
  map_zero' := Subtype.ext (map_zero (qExpand L d))
  map_add' x y := Subtype.ext (map_add (qExpand L d) (x : LaurentSeries L) (y : LaurentSeries L))
  commutes' c := Subtype.ext ((qExpandAlgHom L d).commutes c)

@[simp] theorem heckeBeta_coe (M d : ℕ) [NeZero d]
    (x : laurentBaseChange L (x1FunctionField M)) :
    (heckeBeta L M d x : LaurentSeries L) = qExpand L d x := rfl

end
end Dubon2026.SourceFunctionField.GammaOne
