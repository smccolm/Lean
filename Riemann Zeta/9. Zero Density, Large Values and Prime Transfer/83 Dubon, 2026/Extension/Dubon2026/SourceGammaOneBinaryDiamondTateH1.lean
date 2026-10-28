import Dubon2026.SourceGammaOneDiamondPeriodInclusion
import Dubon2026.SourceGammaOneDiamondFiniteH1
import Dubon2026.SourceGammaOneBinaryTateH1

/-! DUB-17/18 -> original all-weight association -> finite Gamma1
homogeneous-coefficient arithmetic realization -> diamond transpose.
Compose the proved arithmetic period inclusion and native lattice/H1
diamond identity. The coefficient endomorphism is retained explicitly;
identifying it with the original normalizer coefficient convention is
still a separate obligation. No compatibility is assumed here.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w

private local instance : Algebra ℤ_[p] (ZMod N) :=
  (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V :=
  Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V

theorem binaryTateCharacterEquiv_diamond (g : Gamma0 M) (b : Module.End (ZMod N) V)
    (φ : TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] V) :
    binaryTateCharacterEquiv Q p n w
        ((b.restrictScalars ℤ_[p]).comp
          (φ.comp (TateModule.tateMap p (arithmeticDiamondPicard M g).toAddMonoidHom))) =
      (b.toAddMonoidHom.comp (binaryTateCharacterEquiv Q p n w φ)).comp
        (periodLatticeDiamond M g).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro l
  exact congrArg b (congrArg φ (arithmeticPeriodInclusion_diamond M p g l))

theorem binaryTateH1Equiv_diamond (hlarge : 3 < p) (g : Gamma0 M)
    (b : Module.End (ZMod N) V)
    (φ : TateModule p (Pic0 (AlgebraicClosure ℚ)
      (functionFieldOver (Gamma1 M) (AlgebraicClosure ℚ))) →ₗ[ℤ_[p]] V) :
    (binaryTateH1Equiv Q p n w hlarge
        ((b.restrictScalars ℤ_[p]).comp
          (φ.comp (TateModule.tateMap p (arithmeticDiamondPicard M g).toAddMonoidHom)))).val =
      sourceGammaOneDiamondH1 (ZMod N) V M g b
        (binaryTateH1Equiv Q p n w hlarge φ).val := by
  change (binaryLatticeH1Equiv Q N w (originalGammaOne_level_ge_four Q p n hlarge)
    (binaryTateCharacterEquiv Q p n w
      ((b.restrictScalars ℤ_[p]).comp
        (φ.comp (TateModule.tateMap p (arithmeticDiamondPicard M g).toAddMonoidHom))))).val = _
  rw [binaryTateCharacterEquiv_diamond]
  exact binaryLatticeH1Equiv_diamond Q N w (originalGammaOne_level_ge_four Q p n hlarge)
    g b (binaryTateCharacterEquiv Q p n w φ)

end
end Dubon2026.SourceFunctionField.GammaOne
