import Dubon2026.SourceOriginalDecompositionDivisorReduction
import Dubon2026.SourceResidueCoefficientPicard
import Dubon2026.SourceOriginalCoefficientPicard
import Dubon2026.SourceModularDecompositionPlaceReduction

/-! DUB-17/18 -> original Frobenius quadratic relation -> arithmetic
Frobenius on the original Picard classes after reduction. The exact original
and residue actions commute on finite divisors, hence on their actual
degree-zero principal-divisor quotients. The same constructed reduction
retains genus equality and injectivity on every invertible torsion group.
The exact source arithmetic Frobenius condition is the only local action
input; no place, divisor or Picard compatibility certificate remains. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem reduction_originalArithmeticPicard_equivariant
    (R : ConstantReduction A FF Fb) (τ : Qbar ≃ₐ[ℚ] Qbar) (e : kk ≃+* kk)
    (hplace : ∀ P : Place Qbar Fo,
      R.placeMap (originalCoefficientPlaceEquiv N (originalArithmeticPlace N τ P)) =
        residueCoefficientPlace N kk e (R.placeMap (originalCoefficientPlaceEquiv N P)))
    (x : Pic0 Qbar Fo) :
    R.pic0Map (originalCoefficientPicardEquiv N (originalArithmeticPicard N τ x)) =
      residueCoefficientPicard N kk e (R.pic0Map (originalCoefficientPicardEquiv N x)) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  change Pic0.mk (R.degZeroMap (originalCoefficientDegZeroEquiv N
    (originalArithmeticDegZero N τ D))) =
      Pic0.mk (residueCoefficientDegZero N kk e
        (R.degZeroMap (originalCoefficientDegZeroEquiv N D)))
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact reduction_originalArithmeticDivisor_equivariant A N R τ e hplace D.val

theorem exists_modular_reduction_arithmeticFrobenius_picard
    (p : ℕ) [Fact p.Prime] [CharP kk p] (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      (∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m))) ∧
      ∀ τ : Qbar ≃ₐ[ℚ] Qbar,
        (∃ hτ : τ ∈ A.decompositionSubgroup ℚ,
          ∀ a : kk, (⟨τ, hτ⟩ : A.decompositionSubgroup ℚ) • a = a ^ p) →
        ∀ x : Pic0 Qbar Fo,
          R.pic0Map (originalCoefficientPicardEquiv N (originalArithmeticPicard N τ x)) =
            residueCoefficientPicard N kk (frobeniusEquiv kk p)
              (R.pic0Map (originalCoefficientPicardEquiv N x)) := by
  obtain ⟨R, hR, hgen, hinj, hplace⟩ :=
    exists_modular_reduction_arithmeticFrobenius_equivariant A N p hNk
  refine ⟨R, hR, hgen, hinj, ?_⟩
  intro τ hτ x
  exact reduction_originalArithmeticPicard_equivariant A N R τ (frobeniusEquiv kk p)
    (hplace τ hτ) x

end
end Dubon2026.SourceFunctionField.GaussReduction
