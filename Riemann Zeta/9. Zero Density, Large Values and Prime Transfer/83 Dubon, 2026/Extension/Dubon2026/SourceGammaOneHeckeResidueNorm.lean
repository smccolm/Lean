import Dubon2026.SourceGammaOneHeckeGaussNorm
import Dubon2026.SourceGammaOneResidueFrobenius

/-! DUB-17/18 -> original Gamma1 Tate Frobenius -> the exact norm in the
actual residue field. Consume the proved Gauss norm formula with the original
arithmetic Frobenius element. Units remain units under the genuine diamond,
so a nonzero residue yields a nonzero norm residue. The field diamond label
is p*d=1; its orientation is retained without a Picard convention change. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve IntermediateField CongruenceSubgroup
attribute [local instance] specializationResidueAlgebra HeckeNorm.alphaAlgebra HeckeNorm.alphaModule
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (M p : ℕ) [NeZero M] [Fact p.Prime]
  [CharP (IsLocalRing.ResidueField A) p]
local notation "Γ" => Gamma1 M
local notation "FF" => laurentBaseChange Qbar (x1FunctionField M)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ

theorem arithmeticDiamondGauss_residue_ne_zero
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ (functionFieldOver Γ Qbar) =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ Fb)
    (g : Gamma0 M) (f : coefficientGaussRing Γ A) (hf : residueToImage A Γ f ≠ 0) :
    residueToImage A Γ (arithmeticDiamondGauss A M hdeg g f) ≠ 0 := by
  have hu : IsUnit f := (regularProlongation A Γ).isUnit_of_residue_ne_zero hf
  exact ((hu.map (arithmeticDiamondGauss A M hdeg g)).map (residueToImage A Γ)).ne_zero

theorem exists_gammaOne_hecke_residue_norm_of_degree_eq
    (hcop : Nat.Coprime M p)
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ (functionFieldOver Γ Qbar) =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ Fb)
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ p) :
    ∃ g : Gamma0 M, (p : ZMod M) * (g.val 1 1 : ZMod M) = 1 ∧
      ∀ f : coefficientGaussRing Γ A,
        ∃ hn : Algebra.norm FF (heckeBeta Qbar M p f.val) ∈ coefficientGaussRing Γ A,
          residueToImage A Γ ⟨Algebra.norm FF (heckeBeta Qbar M p f.val), hn⟩ =
            decompositionResidueAut A Γ d (residueToImage A Γ (arithmeticDiamondGauss A M hdeg g f)) *
              geometricFrobenius A Γ p d hd (residueToImage A Γ f) ∧
          (residueToImage A Γ f ≠ 0 →
            residueToImage A Γ ⟨Algebra.norm FF (heckeBeta Qbar M p f.val), hn⟩ ≠ 0) := by
  obtain ⟨g, hlabel, hnorm⟩ := exists_gammaOne_hecke_gauss_norm_reduction_of_degree_eq A M p hcop hdeg
  refine ⟨g, hlabel, fun f => ?_⟩
  obtain ⟨hn, hred⟩ := hnorm f
  have he : residueToImage A Γ ⟨Algebra.norm FF (heckeBeta Qbar M p f.val), hn⟩ =
      decompositionResidueAut A Γ d (residueToImage A Γ (arithmeticDiamondGauss A M hdeg g f)) *
        geometricFrobenius A Γ p d hd (residueToImage A Γ f) := by
    apply Subtype.ext
    change resHom A Γ _ =
      coeffMap (MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d)
        (resHom A Γ (arithmeticDiamondGauss A M hdeg g f)) *
          (geometricFrobenius A Γ p d hd (residueToImage A Γ f) : LaurentSeries kk)
    rw [geometricFrobenius_coe]
    have hcoeff : MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) kk d = frobenius kk p := by
      ext a
      exact hd a
    rw [hcoeff]
    exact hred
  refine ⟨hn, he, fun hf => ?_⟩
  rw [he]
  exact mul_ne_zero ((map_ne_zero _).mpr (arithmeticDiamondGauss_residue_ne_zero A M hdeg g f hf))
    ((map_ne_zero _).mpr hf)

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
