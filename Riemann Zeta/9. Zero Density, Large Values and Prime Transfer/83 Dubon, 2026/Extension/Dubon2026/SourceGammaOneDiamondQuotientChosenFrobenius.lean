import Dubon2026.SourceGammaOneDiamondQuotientHecke

/-! DUB-17/18 -> original all-weight association -> finite original
Hecke-character realization. The proved projected Frobenius identity and
surjectivity of the actual quotient map give the polynomial for every
original quotient Hecke operator with its exact quotient square. Thus the
family carrying the original adic character retains Frobenius. Degree
and genus preservation remain the explicit geometric inputs. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField

private theorem polynomial_of_projection {R W Z : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
    (q : W →ₗ[R] Z) (hq : Function.Surjective q)
    (F : Module.End R Z) (H : Module.End R W) (Hq : Module.End R Z) (a : R)
    (hH : ∀ x, Hq (q x) = q (H x))
    (hpoly : ∀ x, F (q (H x)) = F (F (q x)) + a • q x) :
    F * Hq = F * F + a • 1 := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := hq z
  change F (Hq (q x)) = F (F (q x)) + a • q x
  exact (congrArg F (hH x)).trans (hpoly x)

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

theorem gammaOne_diamond_quotient_hecke_frobenius_of_intertwining
    (ell : sourceBinaryHeckePrime (Q * N)) [CharP kk ell.val]
    (hdeg : Module.finrank Qbar⟮jCoordinateOver Γ Qbar⟯ (functionFieldOver Γ Qbar) =
      Module.finrank kk⟮residueJCoordinate A Γ⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar (functionFieldOver Γ Qbar))
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ ell.val)
    (hp : (p : kk) ≠ 0)
    (Hq : Module.End (ZMod N) ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w))
    (hH : Hq.comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell)) :
    binaryDiamondQuotientGaloisRep Q p n w d.val * Hq =
      binaryDiamondQuotientGaloisRep Q p n w d.val *
        binaryDiamondQuotientGaloisRep Q p n w d.val +
        (ell.val : ZMod N) ^ (w + 1) • 1 := by
  have hs := gammaOne_diamond_quotient_frobenius_of_degree_genus_eq Q p n w A ell
  have h1 := hs hdeg
  have h2 := h1 hgen
  have h3 := h2 d hd hp
  let q := (binaryTateDiamondRelations Q p n w).mkQ
  let F := binaryDiamondQuotientGaloisRep Q p n w d.val
  let H := binaryTatePrimeOperators Q p n w ell
  have h4 := polynomial_of_projection q (binaryTateDiamondRelations Q p n w).mkQ_surjective
    F H Hq ((ell.val : ZMod N) ^ (w + 1))
  have h5 := h4 (fun x => LinearMap.congr_fun hH x)
  exact h5 h3

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
