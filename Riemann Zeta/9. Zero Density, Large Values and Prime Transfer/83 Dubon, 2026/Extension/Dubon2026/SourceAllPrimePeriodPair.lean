import Dubon2026.SourceAllPrimeHeckeReflection
import Dubon2026.SourceAllPrimeScalarPeriods
import Dubon2026.SourceOriginalPeriodSurjectivity

/-! DUB-17/18 -> rational rank-two Hecke descent -> faithful rational
period realization. Both components of the actual original parabolic
period isomorphism intertwine every prime operator, including U_p.
Reuse its proved surjectivity and the genuine reflection compatibility.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup SourceCuspBoundary

theorem sourceAllPrimePeriodPair_hecke (N : ℕ) [NeZero N]
    (ell : Nat.Primes) (f g : CuspForm (Gamma0 N) 2) :
    sourceWeightTwoPeriodPair N (cuspHeckeLinear N 2 ell.val f, cuspHeckeLinear N 2 ell.val g) =
      sourceAllPrimeHeckeHom ℂ N ell (sourceWeightTwoPeriodPair N (f, g)) := by
  letI : NeZero ell.val := ⟨ell.property.ne_zero⟩
  rw [cuspHeckeLinear_prime N 2 ell.property]
  change sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property f) +
    sourceWeightTwoPeriodReflection N (sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property f)) +
    sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property g) -
    sourceWeightTwoPeriodReflection N (sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property g)) = _
  simp only [sourceAllPrimePeriodHom_hecke, sourceAllPrimePeriodReflection_hecke]
  rw [← map_add, ← map_add, ← map_sub]
  rfl

theorem sourceAllPrimeHeckeHom_parabolic (N : ℕ) [NeZero N] (ell : Nat.Primes)
    (φ : Additive (Gamma0 N) →+ ℂ) (hφ : φ ∈ parabolicHoms N) :
    sourceAllPrimeHeckeHom ℂ N ell φ ∈ parabolicHoms N := by
  obtain ⟨⟨f, g⟩, hfg⟩ := sourceWeightTwoParabolicPeriodPair_surjective N ⟨φ, hφ⟩
  have he : sourceWeightTwoPeriodPair N (f, g) = φ := congrArg Subtype.val hfg
  rw [← he, ← sourceAllPrimePeriodPair_hecke]
  exact (sourceWeightTwoParabolicPeriodPair N
    (cuspHeckeLinear N 2 ell.val f, cuspHeckeLinear N 2 ell.val g)).property

end
end Dubon2026
