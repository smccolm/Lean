import Dubon2026.ArithmeticOrbitPrimeFibers

/-! # Injective indexing of actual local Mackey orbits by genuine primes

Descend the original induced-prime construction to the exact orbit quotient
used by the continuous Mackey formula. Its fibers have already been proved
to be precisely the actual local Galois orbits. Surjectivity onto all primes
above the original rational prime remains the next DUB-17 obligation.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitFieldRationalAlgebra
  arithmeticOrbitCompletionNumberField

variable (a : 𝓞 ℚ) (p : ℕ) (hp : p.Prime)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- The exact local Mackey orbit has a well-defined genuine original prime over the chosen rational prime. -/
def rationalArithmeticOrbitPrimeIndex :
    cosetOrbitIndex (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
      (rationalArithmeticOrbitFixingSubgroup a F) →
        {w : IsDedekindDomain.HeightOneSpectrum (𝓞 F) // originalIntegerPrimeBelow F w = rationalPrimePlace p hp} := by
  letI := cosetOrbitRestrictedAction (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalArithmeticOrbitFixingSubgroup a F)
  refine Quotient.lift (fun c => ⟨rationalArithmeticOrbitPrime a p hp F c,
    rationalArithmeticOrbitPrime_below a p hp F c⟩) ?_
  intro c c' h
  obtain ⟨d, hd⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  apply Subtype.ext
  exact (rationalArithmeticOrbitPrime_eq_of_smul a p hp F c' c d hd).symm

/-- Passing to the original orbit quotient preserves the literal induced prime of each coset. -/
theorem rationalArithmeticOrbitPrimeIndex_mk
    (c : rationalArithmeticGaloisGroup a ⧸ rationalArithmeticOrbitFixingSubgroup a F) :
    (rationalArithmeticOrbitPrimeIndex a p hp F (Quotient.mk'' c)).val =
      rationalArithmeticOrbitPrime a p hp F c := rfl

/-- Distinct actual local Mackey orbits give distinct genuine original primes. -/
theorem rationalArithmeticOrbitPrimeIndex_injective :
    Function.Injective (rationalArithmeticOrbitPrimeIndex a p hp F) := by
  letI := cosetOrbitRestrictedAction (rationalPrimeArithmeticRestriction a p hp).toMonoidHom
    (rationalArithmeticOrbitFixingSubgroup a F)
  intro u v
  refine Quotient.inductionOn₂ u v ?_
  intro c c' h
  have he : rationalArithmeticOrbitPrime a p hp F c = rationalArithmeticOrbitPrime a p hp F c' :=
    congrArg Subtype.val h
  obtain ⟨d, hd⟩ := (rationalArithmeticOrbitPrime_eq_iff a p hp F c' c).mp he.symm
  exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨d, hd⟩))

end
end Dubon2026
