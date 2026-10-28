import Dubon2026.SourceGammaOneArithmeticPeriodInclusion
import Dubon2026.SourceGammaOneFiniteParabolicH1

/-! DUB17/18 -> original all-weight arithmetic realization -> finite
Gamma1 H1/Tate comparison. Restriction along the actual arithmetic
period inclusion is bijective by the proved base-change universal
property. Compose this dual comparison with the actual native H1
comparison. Coefficients use the canonical p-adic reduction map.
No basis, lifting, dual comparison or realization premise is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup groupCohomology
variable (M p : ℕ) [NeZero M] [Fact p.Prime] (n : ℕ)

private local instance : Algebra ℤ_[p] (ZMod (p ^ n)) :=
  (PadicInt.toZModPow n).toAlgebra

/-- Restrict a finite arithmetic Tate character to the original integral periods. -/
def arithmeticTateCharacterRestriction :
    (TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] ZMod (p ^ n)) →ₗ[ZMod (p ^ n)]
      (sourceWeightTwoIntegralLattice (Gamma1 M) →+ ZMod (p ^ n)) where
  toFun φ := φ.toAddMonoidHom.comp (arithmeticPeriodInclusion M p).toAddMonoidHom
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem arithmeticTateCharacterRestriction_injective :
    Function.Injective (arithmeticTateCharacterRestriction M p n) := by
  intro φ ψ h
  apply (arithmeticPeriodInclusion_isBaseChange M p).algHom_ext
  intro l
  exact congrArg (fun χ => χ l) h

theorem arithmeticTateCharacterRestriction_surjective :
    Function.Surjective (arithmeticTateCharacterRestriction M p n) := by
  intro ψ
  refine ⟨(arithmeticPeriodInclusion_isBaseChange M p).lift ψ.toIntLinearMap, ?_⟩
  apply AddMonoidHom.ext
  intro l
  exact (arithmeticPeriodInclusion_isBaseChange M p).lift_eq ψ.toIntLinearMap l

/-- The actual finite Tate characters as characters of the original period lattice. -/
def arithmeticTateCharacterEquiv :
    (TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)]
      (sourceWeightTwoIntegralLattice (Gamma1 M) →+ ZMod (p ^ n)) :=
  LinearEquiv.ofBijective (arithmeticTateCharacterRestriction M p n)
    ⟨arithmeticTateCharacterRestriction_injective M p n,
      arithmeticTateCharacterRestriction_surjective M p n⟩

/-- Actual finite arithmetic Tate duality with native parabolic, elliptic-trivial Gamma1 H1. -/
def arithmeticTateFiniteH1Equiv :
    (TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] ZMod (p ^ n)) ≃ₗ[ZMod (p ^ n)]
      finiteParabolicH1 M (p ^ n) :=
  (arithmeticTateCharacterEquiv M p n).trans (finiteLatticeH1Equiv M (p ^ n))

theorem arithmeticTateFiniteH1Equiv_hom_apply
    (φ : TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] ZMod (p ^ n))
    (γ : Gamma1 M) :
    (H1IsoOfIsTrivial (Rep.trivial (ZMod (p ^ n)) (Gamma1 M) (ZMod (p ^ n)))).hom
      (arithmeticTateFiniteH1Equiv M p n φ).val (Additive.ofMul γ) =
        φ (arithmeticPeriodInclusion M p (latticePeriodHom M (Additive.ofMul γ))) :=
  finiteLatticeH1Equiv_hom_apply M (p ^ n) (arithmeticTateCharacterEquiv M p n φ) γ

end
end Dubon2026.SourceFunctionField.GammaOne
