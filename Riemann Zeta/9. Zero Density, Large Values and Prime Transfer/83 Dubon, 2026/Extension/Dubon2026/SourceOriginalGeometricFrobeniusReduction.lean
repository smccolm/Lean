import Dubon2026.SourceOriginalFrobeniusPicardReduction
import Dubon2026.SourceResidueGeometricFrobeniusPicard

/-! DUB-17/18 -> original Tate Frobenius quadratic relation -> reduction
of original arithmetic Frobenius to geometric Frobenius on actual Picard
classes. The exact coefficient/geometric divisor comparison supplies the
remaining identification in the same constructed modular reduction.
Genus equality and invertible-torsion injectivity remain available on it. -/
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

theorem exists_modular_reduction_geometricFrobenius_picard
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
            residueGeometricFrobeniusPicard N kk p
              (R.pic0Map (originalCoefficientPicardEquiv N x)) := by
  obtain ⟨R, hR, hgen, hinj, hF⟩ :=
    exists_modular_reduction_arithmeticFrobenius_picard A N p hNk
  refine ⟨R, hR, hgen, hinj, ?_⟩
  intro τ hτ x
  exact (hF τ hτ x).trans
    (residueGeometricFrobeniusPicard_eq_coefficient N kk p
      (R.pic0Map (originalCoefficientPicardEquiv N x))).symm

end
end Dubon2026.SourceFunctionField.GaussReduction
