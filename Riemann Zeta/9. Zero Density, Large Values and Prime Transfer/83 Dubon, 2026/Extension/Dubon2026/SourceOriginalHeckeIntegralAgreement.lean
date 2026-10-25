import Dubon2026.SourceOriginalIntegralDivisorReduction
import Dubon2026.SourceOriginalHeckePrincipalNorm
import Dubon2026.SourceOriginalHeckeNormReduction
import Dubon2026.SourceResidueFrobeniusDivisorOperator

/-! DUB-17/18 -> original Tate quadratic relation -> Hecke reduction on
finite torsion. The actual original Hecke norm formula and the exact residue
Frobenius divisor formula discharge agreement on integral principal divisors.
The reduction is the same modular constant reduction used for torsion
injectivity; no Hecke compatibility certificate is supplied. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N p : ℕ) [NeZero N] [Fact p.Prime]
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "F" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
variable [CharP (IsLocalRing.ResidueField A) p]
attribute [local instance] residueModularAlgebra residueConstantsClosed HeckeNorm.alphaAlgebra

theorem original_hecke_reduction_integral_principal
    (hpN : ¬ p ∣ N) (hNk : (N : kk) ≠ 0) (R : ConstantReduction A F Fb)
    (hR : R.toRegularProlongation =
      modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
    (y : LaurentSeries A) (hy : ι A y ∈ Fo) (hry : ϖ A y ≠ 0) :
    R.divMap (originalCoefficientDivisorEquiv N
      (originalHeckeDivisor Qbar N p (originalPrincipalDivisor N Qbar ⟨ι A y, hy⟩))) =
    residueFrobeniusDivisorOperator N kk p
      (R.divMap (originalCoefficientDivisorEquiv N
        (originalPrincipalDivisor N Qbar ⟨ι A y, hy⟩))) := by
  let f : Fo := ⟨ι A y, hy⟩
  have hf : f ≠ 0 := fun h => (ϖ_ne_zero_ne_zero hry)
    ((ι_eq_zero_iff A y).mp (congrArg Subtype.val h))
  let fb : Fb := ⟨ϖ A y, original_integral_laurent_specializes N A hNk y hy⟩
  have hfb : fb ≠ 0 := fun h => hry (congrArg Subtype.val h)
  obtain ⟨y', hy', hres⟩ := original_hecke_norm_integral_reduction N p A hpN y hy
  have hyF' : ι A y' ∈ Fo := by
    rw [hy']
    exact (Algebra.norm Fo (originalHeckeBeta Qbar N p f)).property
  let fb' : Fb := ⟨ϖ A y', original_integral_laurent_specializes N A hNk y' hyF'⟩
  have hbar : fb' = residueCoefficientRingAut N kk (frobeniusEquiv kk p) fb *
      residueGeometricFrobenius N kk p fb := by
    apply Subtype.ext
    change ϖ A y' = coeffMap (frobenius kk p) (ϖ A y) *
      (residueGeometricFrobenius N kk p fb : LaurentSeries kk)
    rw [residueGeometricFrobenius_coe]
    exact hres
  have hry' : ϖ A y' ≠ 0 := by
    intro h
    have hz : fb' = 0 := Subtype.ext h
    rw [hbar] at hz
    exact mul_ne_zero ((map_ne_zero _).mpr hfb) ((map_ne_zero _).mpr hfb) hz
  have hnorm : Algebra.norm Fo (originalHeckeBeta Qbar N p f) = ⟨ι A y', hyF'⟩ :=
    Subtype.ext hy'.symm
  rw [originalHeckeDivisor_principal_norm Qbar N p _ hf, hnorm]
  ext Q
  rw [original_reduction_integral_divisor_order A N hNk R hR y' hyF' hry'
    _ (fun _ => rfl) Q]
  change Q.ord fb' = _
  rw [hbar]
  exact (residueFrobeniusDivisorOperator_order N kk p _ fb hfb
    (original_reduction_integral_divisor_order A N hNk R hR y hy hry _ (fun _ => rfl)) Q).symm

end
end Dubon2026.SourceFunctionField.GaussReduction
