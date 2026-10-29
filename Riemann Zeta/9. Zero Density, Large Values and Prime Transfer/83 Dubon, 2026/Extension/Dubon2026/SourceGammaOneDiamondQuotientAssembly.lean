import Dubon2026.SourceGammaOneDiamondQuotientHecke
import Dubon2026.SourceGammaOneDiamondQuotientTransfer

/-! DUB-17/18 -> original all-weight association -> finite original
Hecke-character realization. The actual descended Hecke operator from
the original geometric Frobenius theorem intertwines the original
cohomology transfer. Its operator, quotient polynomial and original
transfer square are derived together from degree/genus preservation;
no Hecke descent or transfer compatibility is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Qbar" => AlgebraicClosure ℚ
local notation "Γ" => Gamma1 M
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver Γ Qbar))
variable (A : ValuationSubring Qbar)
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A Γ
attribute [local instance] specializationResidueAlgebra

private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V

private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance

theorem exists_gammaOne_diamond_quotient_original_transfer_frobenius
    (hlarge : 3 < p)
    (ell : sourceBinaryHeckePrime (Q * N)) [CharP kk ell.val]
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ (functionFieldOver Γ Qbar) =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar (functionFieldOver Γ Qbar))
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ ell.val)
    (hp : (p : kk) ≠ 0) :
    ∃ Hq : Module.End (ZMod N) ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w),
      Hq.comp (binaryTateDiamondRelations Q p n w).mkQ =
        (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell) ∧
      binaryDiamondQuotientGaloisRep Q p n w d.val * Hq =
        binaryDiamondQuotientGaloisRep Q p n w d.val *
          binaryDiamondQuotientGaloisRep Q p n w d.val +
          (ell.val : ZMod N) ^ (w + 1) • 1 ∧
      (binaryDiamondQuotientOriginalTransfer Q p n w hlarge).comp Hq =
        (sourceBinaryH1PrimeOperators (ZMod N) Q w (sourceGammaOneHeckePrimeForget Q N ell)).comp
          (binaryDiamondQuotientOriginalTransfer Q p n w hlarge) := by
  have hs := exists_gammaOne_diamond_quotient_hecke_frobenius_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := h2 d hd hp
  obtain ⟨Hq, hcomp, hpoly⟩ := h3
  refine ⟨Hq, hcomp, hpoly, ?_⟩
  exact binaryDiamondQuotientOriginalTransfer_hecke_of_intertwining Q p n w hlarge ell Hq hcomp

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
