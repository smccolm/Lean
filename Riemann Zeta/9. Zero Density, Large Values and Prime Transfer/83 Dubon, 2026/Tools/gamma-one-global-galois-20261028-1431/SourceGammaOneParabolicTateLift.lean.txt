import Dubon2026.SourceGammaOneParabolicRestriction
import Dubon2026.SourceGammaOneDiamondRestriction
import Dubon2026.SourceGammaOneBinaryDiamondTateH1
import Dubon2026.SourceGammaOneArithmeticTateOperators

/-! DUB-17/18 -> original all-weight arithmetic association -> actual
source parabolic cohomology in the homogeneous-valued Tate dual. Restrict
the original class and apply the proved Tate/H1 equivalence. Native
normalizer invariance then derives combined-diamond fixedness. No
nonvanishing, surjectivity of restriction, or Hecke-character descent is
inferred; the existing comparison requires coefficient prime greater than 3. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup groupCohomology
variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Qbar" => AlgebraicClosure ℚ
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar))

private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V

theorem exists_binaryTate_restriction_diamond_fixed (hlarge : 3 < p)
    (x : sourceParabolicH1 (Gamma0 Q) V) :
    ∃ φ : T →ₗ[ℤ_[p]] V,
      (binaryTateH1Equiv Q p n w hlarge φ).val = sourceGammaOneBinaryRestrictionH1 Q N w x.val ∧
      ∀ g : Gamma0 M,
        ((sourceGammaOneBinaryDiamondCoefficient Q N w g).restrictScalars ℤ_[p]).comp
          (φ.comp (arithmeticDiamondTate M p g)) = φ := by
  let E := binaryTateH1Equiv Q p n w hlarge
  let y : binaryParabolicH1 Q N w :=
    ⟨sourceGammaOneBinaryRestrictionH1 Q N w x.val,
      sourceGammaOneBinaryRestrictionH1_parabolic Q N w x.property⟩
  let φ := E.symm y
  have hφ : (E φ).val = sourceGammaOneBinaryRestrictionH1 Q N w x.val :=
    congrArg Subtype.val (E.apply_symm_apply y)
  refine ⟨φ, hφ, fun g => ?_⟩
  apply E.injective
  apply Subtype.ext
  have hd := binaryTateH1Equiv_diamond Q p n w hlarge g
    (sourceGammaOneBinaryDiamondCoefficient Q N w g) φ
  exact hd.trans ((congrArg
    (sourceGammaOneDiamondH1 (ZMod N) V M g (sourceGammaOneBinaryDiamondCoefficient Q N w g)) hφ).trans
      ((sourceGammaOneBinaryRestrictionH1_diamond Q N w g x.val).trans hφ.symm))

end
end Dubon2026.SourceFunctionField.GammaOne
