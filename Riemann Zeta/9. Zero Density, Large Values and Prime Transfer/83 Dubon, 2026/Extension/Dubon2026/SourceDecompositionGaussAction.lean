import Dubon2026.SourceOriginalInertiaGaussAction
import Dubon2026.SourceResidueCoefficientAutomorphism

/-! DUB-17/18 -> original arithmetic Frobenius comparison -> actual
Gauss reduction with its residue coefficient action. The native decomposition
group preserves integral fractions and its induced residue automorphism
preserves nonzero denominators. Existing fraction witnesses and their
choice-independence theorem derive equivariance of the actual residue map. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
local notation "kk" => IsLocalRing.ResidueField A

theorem coeffMap_residue_decomposition (d : A.decompositionSubgroup ℚ)
    (y : LaurentSeries A) :
    coeffMap (IsLocalRing.residue A)
        (coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d) y) =
      coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d)
        (coeffMap (IsLocalRing.residue A) y) := by
  ext n
  exact IsLocalRing.ResidueField.residue_smul (A.decompositionSubgroup ℚ) d (y.coeff n)

theorem isInt_coeffMap_decomposition (d : A.decompositionSubgroup ℚ)
    {f : LaurentSeries Qbar} (hf : IsInt A f) :
    IsInt A (coeffMap (d.val : Qbar →+* Qbar) f) := by
  obtain ⟨x, y, hy, h⟩ := hf
  let σA := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d
  refine ⟨coeffMap σA x, coeffMap σA y, ?_, ?_⟩
  · rw [coeffMap_residue_decomposition]
    exact (map_ne_zero _).mpr hy
  · change coeffMap (d.val : Qbar →+* Qbar) f * coeffMap A.subtype (coeffMap σA y) =
      coeffMap A.subtype (coeffMap σA x)
    rw [coeffMap_subtype_decomposition, coeffMap_subtype_decomposition, ← map_mul]
    exact congrArg (coeffMap (d.val : Qbar →+* Qbar)) h

/-- The actual original decomposition-group action restricted to the Gauss ring. -/
def decompositionGaussHom (N : ℕ) (d : A.decompositionSubgroup ℚ) :
    gaussRing A N →+* gaussRing A N where
  toFun f := ⟨coefficientArithmeticRingAut N d.val f.val, by
    rw [mem_gaussRing_iff, coefficientArithmeticRingAut_coe]
    exact isInt_coeffMap_decomposition A d f.property⟩
  map_one' := Subtype.ext (map_one (coefficientArithmeticRingAut N d.val))
  map_mul' f g := Subtype.ext (map_mul (coefficientArithmeticRingAut N d.val) f.val g.val)
  map_zero' := Subtype.ext (map_zero (coefficientArithmeticRingAut N d.val))
  map_add' f g := Subtype.ext (map_add (coefficientArithmeticRingAut N d.val) f.val g.val)

theorem decompositionGaussHom_resHom (N : ℕ) (d : A.decompositionSubgroup ℚ)
    (f : gaussRing A N) :
    resHom A N (decompositionGaussHom A N d f) =
      coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d) (resHom A N f) := by
  obtain ⟨hy, h⟩ := wit_spec A N f
  let σA := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d
  have hy' : ϖ A (coeffMap σA (wit A N f).2) ≠ 0 := by
    rw [coeffMap_residue_decomposition]
    exact (map_ne_zero _).mpr hy
  have h' : ((decompositionGaussHom A N d f : modularFunctionFieldCoeff N Qbar) : LaurentSeries Qbar) *
      ι A (coeffMap σA (wit A N f).2) = ι A (coeffMap σA (wit A N f).1) := by
    change coeffMap (d.val : Qbar →+* Qbar) (f.val : LaurentSeries Qbar) *
      coeffMap A.subtype (coeffMap σA (wit A N f).2) = coeffMap A.subtype (coeffMap σA (wit A N f).1)
    rw [coeffMap_subtype_decomposition, coeffMap_subtype_decomposition, ← map_mul]
    exact congrArg (coeffMap (d.val : Qbar →+* Qbar)) h
  rw [resHom_eq A N hy' h', resHom_eq A N hy h, map_div₀,
    coeffMap_residue_decomposition, coeffMap_residue_decomposition]

theorem decompositionGaussHom_modularResidue (N : ℕ) [NeZero N]
    (hNk : (N : kk) ≠ 0) (d : A.decompositionSubgroup ℚ) (f : gaussRing A N) :
    modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk (decompositionGaussHom A N d f) =
      residueCoefficientRingAut N kk (MulSemiringAction.toRingAut (A.decompositionSubgroup ℚ) kk d)
        (modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f) :=
  Subtype.ext (decompositionGaussHom_resHom A N d f)

end
end Dubon2026.SourceFunctionField.GaussReduction
