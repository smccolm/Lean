import Dubon2026.SourceGammaOneLocalGoodReduction
import Dubon2026.SourceGammaOneDiamondQuotientHeckeFamily
/-! DUB-17/18 -> original all-weight association -> finite original
Hecke-character realization. The proved original local degree and genus
preservation discharge both geometric families in the native Frobenius
consumer. All good-prime operators preserve the actual diamond relations,
and their literal quotient operators are constructed. No geometric or
operator-family premise remains; parabolic character transfer is separate. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
noncomputable section
open SourceCurve CongruenceSubgroup IntermediateField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
private theorem good_prime_away_square (Q N : ℕ) (ell : sourceBinaryHeckePrime (Q * N)) :
    ¬ ell.val ∣ Q * N ^ 2 := by
  have hn := ell.property.1.coprime_iff_not_dvd.mp ell.property.2
  intro h
  rcases ell.property.1.dvd_mul.mp h with hQ | hN
  · exact hn (dvd_mul_of_dvd_left hQ N)
  · exact hn (dvd_mul_of_dvd_right (ell.property.1.dvd_of_dvd_pow hN) Q)

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "Γ" => Gamma1 M
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver Γ Qbar))
attribute [local instance] specializationResidueAlgebra
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
theorem gammaOne_diamond_relations_hecke_family :
    ∀ ell : sourceBinaryHeckePrime (Q * N),
      binaryTateDiamondRelations Q p n w ≤
        (binaryTateDiamondRelations Q p n w).comap (binaryTatePrimeOperators Q p n w ell) := by
  apply gammaOne_diamond_relations_hecke_family_of_degree_genus_eq Q p n w
  · intro ell e
    exact (gammaOne_local_degree_and_genus_eq M ell.val ell.property.1
      (good_prime_away_square Q N ell) e).1
  · intro ell e
    exact (gammaOne_local_degree_and_genus_eq M ell.val ell.property.1
      (good_prime_away_square Q N ell) e).2

theorem exists_gammaOne_diamond_quotient_hecke_family :
    ∃ Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N)
        ((T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w),
      ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
        (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell) := by
  have hs := gammaOne_diamond_relations_hecke_family Q p n w
  let K := binaryTateDiamondRelations Q p n w
  exact ⟨fun ell => K.mapQ K (binaryTatePrimeOperators Q p n w ell) (hs ell), fun _ => rfl⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
