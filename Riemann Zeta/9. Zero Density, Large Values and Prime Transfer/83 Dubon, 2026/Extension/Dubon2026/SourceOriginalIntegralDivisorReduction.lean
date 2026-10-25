import Dubon2026.SourceOriginalInertiaDivisorReduction
import Dubon2026.SourceResidueOriginalSpecialization

/-! DUB-17/18 -> Hecke reduction on finite torsion -> integral principal
agreement. Identify the exact residue of an integral Laurent function in
the same modular constant reduction. Its defining principal-divisor formula,
transported through the proved original/coefficient equivalence, then gives
the orders of the reduced original divisor. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fo" => modularFunctionFieldOver N Qbar
local notation "F" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra

theorem modular_prolongation_integral_laurent
    (hNk : (N : kk) ≠ 0) (S : RegularProlongation A F Fb)
    (hS : S = modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
    (y : LaurentSeries A) (hy : ι A y ∈ F) :
    ∃ f : S.integers, (f : F) = ⟨ι A y, hy⟩ ∧
      (S.residue f : LaurentSeries kk) = ϖ A y := by
  subst S
  exact ⟨⟨⟨ι A y, hy⟩, ι_mem_gaussRing A N hy⟩, rfl, resHom_ι A N hy⟩

theorem original_reduction_integral_divisor_order
    (hNk : (N : kk) ≠ 0) (R : ConstantReduction A F Fb)
    (hR : R.toRegularProlongation =
      modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
    (y : LaurentSeries A) (hy : ι A y ∈ Fo) (hry : ϖ A y ≠ 0)
    (D : Divisor Qbar Fo) (hD : ∀ P, D P = P.ord ⟨ι A y, hy⟩) (Q : Place kk Fb) :
    R.divMap (originalCoefficientDivisorEquiv N D) Q =
      Q.ord ⟨ϖ A y, original_integral_laurent_specializes N A hNk y hy⟩ := by
  let fc := originalCoefficientEquiv N ⟨ι A y, hy⟩
  obtain ⟨f, hf, hres⟩ := modular_prolongation_integral_laurent A N hNk
    R.toRegularProlongation hR y fc.property
  have hr0 : R.residue f ≠ 0 := fun h => hry (hres.symm.trans (congrArg Subtype.val h))
  have hr : R.residue f =
      ⟨ϖ A y, original_integral_laurent_specializes N A hNk y hy⟩ := Subtype.ext hres
  have horders (P : Place Qbar F) :
      originalCoefficientDivisorEquiv N D P = P.ord (f : F) := by
    rw [hf]
    exact divisorTransform_orders (originalCoefficientEquiv N) hD P
  have h := R.mapDomain_placeMap f hr0 (originalCoefficientDivisorEquiv N D) horders Q
  rw [hr] at h
  exact h

end
end Dubon2026.SourceFunctionField.GaussReduction
