import Dubon2026.SourceGammaOnePrimitiveJointGalois
import Dubon2026.SourceGammaOneGeometricHeckeFamily
import Dubon2026.SourceGammaOneDiamondQuotientChosenFrobenius

/-! DUB-17/18 -> original all-weight association -> joint arithmetic
specialization. The primitive boundary quadratic and the existing geometric
quotient polynomial give one Frobenius relation in the same finite operator
ring. Degree and genus are explicit intermediate hypotheses, discharged in
the original local consumer. The diamond is retained explicitly. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup SourceCuspBoundary CoefficientReduction IntermediateField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
private theorem pair_quadratic_of_eq {X Y : Type} [Ring X] [Ring Y]
    (F : X) (G : Y) (H D : X × Y) (Hx Dx : X) (Hy Dy : Y) (a : ℕ)
    (hH : H = (Hx, Hy)) (hD : D = (Dx, Dy))
    (hx : F * Hx = F * F + a • Dx) (hy : G * Hy = G * G + a • Dy) :
    (F, G) * H = (F, G) * (F, G) + a • D := by
  subst H
  subst D
  exact Prod.ext hx hy

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar))
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
local notation "J" => (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w
local notation "S" => sourceBinaryHeckePrime (Q * N) ⊕ Gamma0 M

/-- Each original generator has exactly its geometric/boundary pair
in the literal joint operator image. -/
theorem binaryPrimitiveJointHeckeDiamondWord_ι
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J) (s : S) :
    binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ s) =
      (Sum.elim Hq (fun _ : Gamma0 M => 1) s,
        binaryPrimitiveBoundaryHeckeDiamondOperators Q N w s) := by
  change (FreeAlgebra.lift ℤ (Sum.elim Hq (fun _ : Gamma0 M => 1)) (FreeAlgebra.ι ℤ s),
    FreeAlgebra.lift ℤ (binaryPrimitiveBoundaryHeckeDiamondOperators Q N w) (FreeAlgebra.ι ℤ s)) = _
  exact Prod.ext (FreeAlgebra.lift_ι_apply (Sum.elim Hq (fun _ : Gamma0 M => 1)) s)
    (FreeAlgebra.lift_ι_apply (binaryPrimitiveBoundaryHeckeDiamondOperators Q N w) s)

variable (A : ValuationSubring (AlgebraicClosure ℚ))
local notation "kk" => IsLocalRing.ResidueField A
local notation "Fb" => residueImage A (Gamma1 M)
attribute [local instance] specializationResidueAlgebra

/-- At a valuation satisfying the stated original degree and genus equalities,
the two actual factors give the joint Frobenius polynomial. The original
local consumer proves these narrower geometric hypotheses. -/
theorem binaryPrimitiveJointGaloisRep_frobenius_of_degree_genus_eq
    (ell : sourceBinaryHeckePrime (Q * N)) [CharP kk ell.val]
    (hdeg : Module.finrank Qbar⟮jCoordinateOver (Gamma1 M) Qbar⟯
        (functionFieldOver (Gamma1 M) Qbar) =
      Module.finrank kk⟮residueJCoordinate A (Gamma1 M)⟯ Fb)
    (hgen : genusFF kk Fb = genusFF Qbar (functionFieldOver (Gamma1 M) Qbar))
    (d : A.decompositionSubgroup ℚ) (hd : ∀ a : kk, d • a = a ^ ell.val)
    (hp : (p : kk) ≠ 0)
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    (g : Gamma0 M) (hlabel : (g.val 1 1 : ZMod M) = ell.val) :
    binaryPrimitiveJointGaloisRep Q p n w d.val *
        binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inl ell)) =
      binaryPrimitiveJointGaloisRep Q p n w d.val * binaryPrimitiveJointGaloisRep Q p n w d.val +
        (ell.val ^ (w + 1)) •
          binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inr g)) := by
  have hx := gammaOne_diamond_quotient_hecke_frobenius_of_intertwining Q p n w A ell
    hdeg hgen d hd hp (Hq ell) (hH ell)
  have hy := binaryPrimitiveBoundaryGaloisRep_frobenius Q N w A ell g hlabel d hd
  exact pair_quadratic_of_eq
    (binaryDiamondQuotientGaloisRep Q p n w d.val)
    (binaryPrimitiveBoundaryGaloisRep Q N w d.val)
    (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inl ell)))
    (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inr g)))
    (Hq ell) 1 (binaryPrimitiveColumnHecke Q N w ell) (binaryPrimitiveColumnDiamond Q N w g)
    (ell.val ^ (w + 1))
    (binaryPrimitiveJointHeckeDiamondWord_ι Q p n w Hq (Sum.inl ell))
    (binaryPrimitiveJointHeckeDiamondWord_ι Q p n w Hq (Sum.inr g))
    (by simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hx)
    (by simpa only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] using hy)

end
end Dubon2026.SourceFunctionField.GammaOne
