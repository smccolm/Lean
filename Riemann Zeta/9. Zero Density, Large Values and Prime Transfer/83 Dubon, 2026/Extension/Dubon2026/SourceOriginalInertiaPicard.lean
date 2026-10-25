import Dubon2026.SourceOriginalCoefficientPicard
import Dubon2026.SourceOriginalInertiaDivisorReduction
import Dubon2026.SourceOriginalInertiaPlaceReduction

/-! DUB-17/18 -> original Tate inertia -> original Picard torsion.
Descend the actual original-place invariance through literal divisors and
the original Picard quotient. The same constructed modular reduction is
injective on invertible torsion, so native arithmetic inertia acts trivially
on the original Picard torsion. No arithmetic equivariance, genus or
Picard-injectivity certificate remains an assumption of the final theorem. -/
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

theorem reduction_originalArithmeticPicard
    (R : ConstantReduction A FF Fb) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hplace : ∀ P : Place Qbar Fo,
      R.placeMap (originalCoefficientPlaceEquiv N (originalArithmeticPlace N τ P)) =
        R.placeMap (originalCoefficientPlaceEquiv N P)) (x : Pic0 Qbar Fo) :
    R.pic0Map (originalCoefficientPicardEquiv N (originalArithmeticPicard N τ x)) =
      R.pic0Map (originalCoefficientPicardEquiv N x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [originalArithmeticPicard_mk, originalCoefficientPicardEquiv_mk,
    originalCoefficientPicardEquiv_mk, ConstantReduction.pic0Map_mk, ConstantReduction.pic0Map_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact reduction_originalArithmeticDivisor A N R τ hplace D.val

theorem originalArithmeticPicard_eq_self_of_inertia_of_torsion
    (p : ℕ) [CharP kk p] (hp : p.Prime) (hNk : (N : kk) ≠ 0)
    (m : ℕ) (hm : (m : kk) ≠ 0) (τ : Qbar ≃ₐ[ℚ] Qbar)
    (hτ : τ ∈ (A.inertiaSubgroup ℚ).map (A.decompositionSubgroup ℚ).subtype)
    (x : Pic0 Qbar Fo) (hx : x ∈ Pic0.torsion m) :
    originalArithmeticPicard N τ x = x := by
  obtain ⟨R, _, _, hinj, hplace⟩ :=
    exists_modular_reduction_invariant_on_original_places A N p hp hNk
  apply (originalCoefficientPicardEquiv N).injective
  apply hinj m hm
      (originalCoefficientPicardEquiv_torsion N m _ (originalArithmeticPicard_torsion N τ m x hx))
      (originalCoefficientPicardEquiv_torsion N m x hx)
  exact reduction_originalArithmeticPicard A N R τ (hplace τ hτ) x

end
end Dubon2026.SourceFunctionField.GaussReduction
