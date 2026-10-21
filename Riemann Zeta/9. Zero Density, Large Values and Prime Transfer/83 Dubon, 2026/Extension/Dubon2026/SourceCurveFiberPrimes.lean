import Dubon2026.SourceCurveFiberPlaces

/-! DUB-17/18 -> original global residue identity -> normal-closure descent.
Every height-one prime of the actual integral closure lies above the base
place's maximal ideal. The exact fiber correspondence therefore identifies
the place fiber with the pinned finite set of primes used in the degree sum.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsDedekindDomain IsLocalRing
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem fiberPrime_liesOver (v : Place K F)
    (P : HeightOneSpectrum (integralClosureAt E v)) :
    P.asIdeal.LiesOver (maximalIdeal v.toValuationSubring) := by
  have h := fiberCenter_liesOver (restrict_fiberPrimePlace v P)
  rwa [fiberCenter_fiberPrimePlace] at h

variable (E) in
/-- Actual chart primes, identified with the native finite primes-over set. -/
def fiberPrimeFinsetEquiv (v : Place K F) :
    HeightOneSpectrum (integralClosureAt E v) ≃
      {P // P ∈ IsDedekindDomain.primesOverFinset (maximalIdeal v.toValuationSubring)
        (integralClosureAt E v)} where
  toFun P := ⟨P.asIdeal, (IsDedekindDomain.mem_primesOverFinset_iff v.maximalIdeal_ne_bot (integralClosureAt E v)).mpr
    ⟨P.isPrime, fiberPrime_liesOver v P⟩⟩
  invFun P := ⟨P.1,
    ((IsDedekindDomain.mem_primesOverFinset_iff v.maximalIdeal_ne_bot (integralClosureAt E v)).mp P.2).1,
    Ideal.ne_bot_of_mem_primesOver v.maximalIdeal_ne_bot
      ((IsDedekindDomain.mem_primesOverFinset_iff v.maximalIdeal_ne_bot (integralClosureAt E v)).mp P.2)⟩
  left_inv _ := HeightOneSpectrum.ext rfl
  right_inv _ := Subtype.ext rfl

instance finite_placeFiber (v : Place K F) :
    Finite {w : Place K E // w.restrict F = v} :=
  Finite.of_equiv _ ((fiberPrimeEquiv E v).trans (fiberPrimeFinsetEquiv E v)).symm

end
end Dubon2026.SourceCurve.Place
