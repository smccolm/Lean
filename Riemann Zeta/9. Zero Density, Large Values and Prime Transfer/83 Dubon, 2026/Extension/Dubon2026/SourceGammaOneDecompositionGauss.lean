import Dubon2026.SourceGammaOneRegularProlongation
import Dubon2026.SourceDecompositionGaussAction
import Dubon2026.SourceGammaOneArithmeticField

/-! DUB-17/18 -> original Gamma1 Tate inertia/Frobenius -> equivariant
good reduction. Reuse the proved decomposition action on integral Laurent
fractions and restrict the original Gamma1 arithmetic automorphism to its
actual coefficient valuation. Literal reduction commutes with this action.
Place specialization and injectivity on Picard torsion remain separate.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open GaussReduction
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar)
  (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Γ Qbar
local notation "R" => coefficientGaussRing Γ A

/-- The original arithmetic decomposition action on the original integral functions. -/
def decompositionGaussHom (d : A.decompositionSubgroup ℚ) : R →+* R where
  toFun f := ⟨arithmeticRingAut Γ d.val f.val, by
    change IsInt A (coeffMap (d.val : Qbar →+* Qbar) (f.val : LaurentSeries Qbar))
    exact isInt_coeffMap_decomposition A d f.property⟩
  map_one' := Subtype.ext (map_one (arithmeticRingAut Γ d.val))
  map_mul' f g := Subtype.ext (map_mul (arithmeticRingAut Γ d.val) f.val g.val)
  map_zero' := Subtype.ext (map_zero (arithmeticRingAut Γ d.val))
  map_add' f g := Subtype.ext (map_add (arithmeticRingAut Γ d.val) f.val g.val)

theorem decompositionGaussHom_coe (d : A.decompositionSubgroup ℚ) (f : R) :
    (decompositionGaussHom A Γ d f : FF) = arithmeticRingAut Γ d.val f.val := rfl

theorem decompositionGaussHom_resHom (d : A.decompositionSubgroup ℚ) (f : R) :
    resHom A Γ (decompositionGaussHom A Γ d f) =
      coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d)
        (resHom A Γ f) := by
  obtain ⟨hy, h⟩ := wit_spec A Γ f
  let σA := MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) A d
  have hy' : ϖ A (coeffMap σA (wit A Γ f).2) ≠ 0 := by
    rw [coeffMap_residue_decomposition]
    exact (map_ne_zero _).mpr hy
  have h' : ((decompositionGaussHom A Γ d f : FF) : LaurentSeries Qbar) *
      ι A (coeffMap σA (wit A Γ f).2) = ι A (coeffMap σA (wit A Γ f).1) := by
    change coeffMap (d.val : Qbar →+* Qbar) (f.val : LaurentSeries Qbar) *
      coeffMap A.subtype (coeffMap σA (wit A Γ f).2) =
        coeffMap A.subtype (coeffMap σA (wit A Γ f).1)
    rw [coeffMap_subtype_decomposition, coeffMap_subtype_decomposition, ← map_mul]
    exact congrArg (coeffMap (d.val : Qbar →+* Qbar)) h
  rw [resHom_eq A Γ hy' h', resHom_eq A Γ hy h, map_div₀,
    coeffMap_residue_decomposition, coeffMap_residue_decomposition]

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
