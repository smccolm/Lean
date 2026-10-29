import Dubon2026.SourceGammaOnePicardTorsion
import Dubon2026.SourceGammaOnePrincipalDivisorIdentities

/-! DUB-17/18 -> original Gamma1 Frobenius/Hecke compatibility -> orders
of actual specialized principal divisors. Transport a Gauss integer to the
same constructed constant reduction and apply its proved principal-divisor
identity. This uses integral fractions directly; no coefficientwise integral
Laurent representative is required. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve
attribute [local instance] specializationResidueAlgebra
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M : ℕ)
local notation "Γ" => CongruenceSubgroup.Gamma1 M
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => functionFieldOver Γ Qbar
local notation "Fb" => residueImage A Γ

theorem gammaOne_reduction_integral_divisor_order
    (R : ConstantReduction A FF Fb) (hR : R.toRegularProlongation = regularProlongation A Γ)
    (f : coefficientGaussRing Γ A) (hf : residueToImage A Γ f ≠ 0)
    (D : Divisor Qbar FF) (hD : ∀ P, D P = P.ord f.val) (Q : Place kk Fb) :
    R.divMap D Q = Q.ord (residueToImage A Γ f) := by
  obtain ⟨f', hf', hres⟩ : ∃ f' : R.toRegularProlongation.integers,
      (f' : FF) = f.val ∧ R.toRegularProlongation.residue f' = residueToImage A Γ f := by
    rw [hR]
    exact ⟨f, rfl, rfl⟩
  have hf0 : R.residue f' ≠ 0 := by rw [hres]; exact hf
  have horders : ∀ P, D P = P.ord (f' : FF) := by rw [hf']; exact hD
  have h := R.mapDomain_placeMap f' hf0 D horders Q
  rw [hres] at h
  exact h

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
