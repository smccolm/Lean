import Dubon2026.SourceGammaOneDiamondQuotientGalois
import Dubon2026.SourceGammaOneTwistedGaloisHecke
import Dubon2026.SourceIntegralWordAdditiveNaturality

/-! DUB-17/18 -> original all-weight association -> actual finite
Hecke-character realization -> Galois stability of the character part.
The already proved original Galois/Hecke commutation descends through
the actual diamond quotient. Native whole-word transport then gives
commutation with its entire operator algebra. The quotient Hecke square
is explicit and is supplied by the geometric good-prime family theorem. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup

private theorem descend_commute {R W Z : Type*} [CommRing R]
    [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
    (q : W →ₗ[R] Z) (hq : Function.Surjective q)
    (F H : Module.End R W) (Fq Hq : Module.End R Z)
    (hF : ∀ x, Fq (q x) = q (F x)) (hH : ∀ x, Hq (q x) = q (H x))
    (hc : ∀ x, F (H x) = H (F x)) : Commute Fq Hq := by
  change Fq * Hq = Hq * Fq
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := hq z
  change Fq (Hq (q x)) = Hq (Fq (q x))
  rw [hH, hF, hc, ← hH, ← hF]

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
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance

theorem binaryDiamondQuotientGaloisRep_prime_of_intertwining
    (σ : Qbar ≃ₐ[ℚ] Qbar) (ell : sourceBinaryHeckePrime (Q * N))
    (Hq : Module.End (ZMod N) ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w))
    (hH : Hq.comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell)) :
    Commute (binaryDiamondQuotientGaloisRep Q p n w σ) Hq := by
  let q := (binaryTateDiamondRelations Q p n w).mkQ
  let F := binaryArithmeticTateGaloisRep Q p n w σ
  let H := binaryTatePrimeOperators Q p n w ell
  let Fq := binaryDiamondQuotientGaloisRep Q p n w σ
  have hs := descend_commute q (binaryTateDiamondRelations Q p n w).mkQ_surjective F H Fq Hq
  have h1 := hs (binaryDiamondQuotientGaloisRep_mk Q p n w σ)
  have h2 := h1 (fun x => LinearMap.congr_fun hH x)
  exact h2 (binaryArithmeticTateGaloisRep_prime Q p n w σ ell)

theorem binaryDiamondQuotientGaloisRep_word_of_intertwining
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N)
      ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w))
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    (σ : Qbar ≃ₐ[ℚ] Qbar) (a : FreeAlgebra ℤ (sourceBinaryHeckePrime (Q * N)))
    (z : (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w) :
    binaryDiamondQuotientGaloisRep Q p n w σ (FreeAlgebra.lift ℤ Hq a z) =
      FreeAlgebra.lift ℤ Hq a (binaryDiamondQuotientGaloisRep Q p n w σ z) := by
  apply sourceHeckeWord_intertwine_addHom Hq Hq
    (binaryDiamondQuotientGaloisRep Q p n w σ).toAddMonoidHom
  intro ell x
  have hs := binaryDiamondQuotientGaloisRep_prime_of_intertwining Q p n w σ ell
  exact LinearMap.congr_fun (hs (Hq ell) (hH ell)).eq x

end
end Dubon2026.SourceFunctionField.GammaOne
