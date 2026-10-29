import Dubon2026.SourceGammaOneParabolicTateLift
import Dubon2026.SourceGammaOneTwistedGaloisFrobenius

/-! DUB-17/18 -> original all-weight arithmetic association -> the
Frobenius polynomial on the actual Tate preimage of an original parabolic
cohomology class. The literal restriction, Tate/H1 equivalence and diamond
invariance supply the input to the genuine Galois polynomial. No diamond
fixedness or Frobenius relation is assumed. Coordinate-degree/genus equality,
the existing comparison range 3<p, and nonvanishing/character transfer remain. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField groupCohomology
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

theorem exists_parabolic_binaryTate_galois_frobenius_of_degree_genus_eq
    (hlarge : 3 < p) (x : sourceParabolicH1 (Gamma0 Q) V)
    (ell : sourceBinaryHeckePrime (Q * N)) [CharP kk ell.val]
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ (functionFieldOver Γ Qbar) =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar (functionFieldOver Γ Qbar))
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ ell.val)
    (hp : (p : kk) ≠ 0) :
    ∃ φ : T →ₗ[ℤ_[p]] V,
      (binaryTateH1Equiv Q p n w hlarge φ).val = sourceGammaOneBinaryRestrictionH1 Q N w x.val ∧
      binaryArithmeticTateGaloisRep Q p n w d.val (binaryTatePrimeOperators Q p n w ell φ) =
        binaryArithmeticTateGaloisRep Q p n w d.val
          (binaryArithmeticTateGaloisRep Q p n w d.val φ) + (ell.val : ZMod N) ^ (w + 1) • φ := by
  have hl := exists_binaryTate_restriction_diamond_fixed Q p n w
  have hl1 := hl hlarge
  have hl2 := hl1 x
  obtain ⟨φ, hφ, hfixed⟩ := hl2
  have hs := exists_gammaOne_galois_frobenius_quadratic_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := h2 d hd hp
  obtain ⟨g, _hg, hq⟩ := h3
  exact ⟨φ, hφ, hq φ (hfixed g)⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
