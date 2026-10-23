import Dubon2026.SourceIntegralWordAdditiveNaturality
import Dubon2026.SourceAllPrimePeriodPair
import Dubon2026.SourceAllPrimeHeckeCoefficientChange
import Dubon2026.SourceRationalParabolicCharacterSpan
import Dubon2026.SourceOriginalIntegralHecke

/-! DUB-17/18 -> rational rank-two Hecke descent -> rational twins of
every actual integral cusp operator. Genuine prime words intertwine the
original period map, commute with its reflection, and preserve rational
characters. Existing integral prime generation represents every element
of the actual integral Hecke algebra by such a word.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup
variable (N : ℕ) [NeZero N]
local notation "S" => CuspForm (Gamma0 N) 2

/-- Evaluate integral prime words on the actual original cusp space. -/
def sourceWeightTwoCuspHeckeWord : FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] Module.End ℂ S :=
  FreeAlgebra.lift ℤ (fun ell : Nat.Primes => cuspHeckeLinear N 2 ell.val)

/-- Evaluate the same words on genuine characters with the specified coefficient ring. -/
def sourceAllPrimeCharacterHeckeWord (R : Type) [CommRing R] :
    FreeAlgebra ℤ Nat.Primes →ₐ[ℤ] Module.End R (Additive (Gamma0 N) →+ R) :=
  FreeAlgebra.lift ℤ (sourceAllPrimeHeckeHom R N)

theorem sourceAllPrimeCharacterHeckeWord_period (a : FreeAlgebra ℤ Nat.Primes) (f : S) :
    sourceWeightTwoPeriodHom (Gamma0 N) (sourceWeightTwoCuspHeckeWord N a f) =
      sourceAllPrimeCharacterHeckeWord N ℂ a (sourceWeightTwoPeriodHom (Gamma0 N) f) := by
  apply sourceHeckeWord_intertwine_addHom _ _ (sourceWeightTwoPeriodHom (Gamma0 N)).toAddMonoidHom
  intro ell g
  letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
  rw [cuspHeckeLinear_prime N 2 ell.property]
  exact sourceAllPrimePeriodHom_hecke N ell g

theorem sourceAllPrimeCharacterHeckeWord_reflection (a : FreeAlgebra ℤ Nat.Primes)
    (φ : Additive (Gamma0 N) →+ ℂ) :
    sourceWeightTwoPeriodReflection N (sourceAllPrimeCharacterHeckeWord N ℂ a φ) =
      sourceAllPrimeCharacterHeckeWord N ℂ a (sourceWeightTwoPeriodReflection N φ) :=
  sourceHeckeWord_intertwine_addHom _ _ (sourceWeightTwoPeriodReflection N).toAddMonoidHom
    (sourceAllPrimePeriodReflection_hecke N) a φ

omit [NeZero N] in
theorem sourceAllPrimeCharacterHeckeWord_rational (a : FreeAlgebra ℤ Nat.Primes)
    (φ : Additive (Gamma0 N) →+ ℚ) :
    sourceAllPrimeCharacterHeckeWord N ℂ a (sourceRationalCharacterComplex N φ) =
      sourceRationalCharacterComplex N (sourceAllPrimeCharacterHeckeWord N ℚ a φ) := by
  let Φ : (Additive (Gamma0 N) →+ ℚ) →+ (Additive (Gamma0 N) →+ ℂ) := {
    toFun := sourceRationalCharacterComplex N
    map_zero' := AddMonoidHom.ext fun _ => Rat.cast_zero
    map_add' φ ψ := AddMonoidHom.ext fun γ => Rat.cast_add (φ γ) (ψ γ) }
  exact (sourceHeckeWord_intertwine_addHom _ _ Φ
    (fun ell ψ => (sourceAllPrimeHeckeHom_coefficient_change ℚ ℂ N ell
      (Rat.castHom ℂ).toAddMonoidHom ψ).symm) a φ).symm

theorem sourceWeightTwoCuspHeckeWord_exists
    (T : sourceOriginalIntegralHeckeAlgebra N 2) :
    ∃ a : FreeAlgebra ℤ Nat.Primes, sourceWeightTwoCuspHeckeWord N a = T.val := by
  have hle : sourceOriginalIntegralHeckeAlgebra N 2 ≤
      Algebra.adjoin ℤ (Set.range fun ell : Nat.Primes => cuspHeckeLinear N 2 ell.val) := by
    apply Algebra.adjoin_le
    rintro _ ⟨n, rfl⟩
    exact sourceHecke_mem_primeAlgebra N 2 (by norm_num) n n.ne_zero
  have ht := hle T.property
  rw [Algebra.adjoin_range_eq_range_freeAlgebra_lift] at ht
  exact ht

end
end Dubon2026
