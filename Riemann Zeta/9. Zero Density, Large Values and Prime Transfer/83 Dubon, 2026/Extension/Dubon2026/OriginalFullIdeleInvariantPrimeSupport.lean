import Dubon2026.OriginalFullIdeleInvariantClosureIndependence
import Dubon2026.OriginalFullDecompositionPrimeUnique

/-! # The original single-prime invariant at any compatible local choice

Full decomposition makes the upper prime unique above its base. Together
with proved closure independence, this identifies the same original class
at every compatible choice over that base. Vanishing at the other upper
primes gives vanishing at every other base prime. These are the two cases
needed for DUB-17's actual arithmetic auxiliary-class invariant sum.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

omit [NumberField K] [NumberField L] in
/-- The original contraction is the specified base prime whenever the actual upper prime lies over it. -/
theorem originalFinitePrimeBelow_eq_of_liesOver
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    originalFinitePrimeBelow K L w = v := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  exact (Ideal.over_def w.asIdeal v.asIdeal).symm

variable [FiniteDimensional K L] [IsGalois K L]

section SameBase
variable (v₀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w₀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  [w₀.asIdeal.LiesOver v₀.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  (Ω Ξ : Type) [Field Ω] [Field Ξ]
  [Algebra (v₀.adicCompletion K) Ω] [Algebra (w₀.adicCompletion L) Ω]
  [Algebra (v.adicCompletion K) Ξ] [Algebra (w.adicCompletion L) Ξ]
  [IsScalarTower (v₀.adicCompletion K) (w₀.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ξ]
  [IsGalois (v₀.adicCompletion K) Ω] [IsSepClosed Ω]
  [IsGalois (v.adicCompletion K) Ξ] [IsSepClosed Ξ]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v₀.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v₀.adicCompletion K) Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]

/-- Equality of the original primes transports the normalized invariant between the separately chosen compatible completion closures. -/
theorem originalFullIdeleCompletionInvariant_eq_of_primes
    (hv : v = v₀) (hw : w = w₀)
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    originalFullIdeleCompletionInvariant K L v w Ξ x =
      originalFullIdeleCompletionInvariant K L v₀ w₀ Ω x := by
  subst v
  subst w
  exact originalFullIdeleCompletionInvariant_closure_independent K L v₀ w₀ Ω Ξ x

/-- At a full-decomposition prime, the actual normalized invariant has the same value for any upper prime and compatible closure over the same base prime. -/
theorem originalFullDecomposition_invariant_same_base
    (hw : OriginalFiniteDecompositionGroup K L w₀ = ⊤) (hv : v = v₀)
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    originalFullIdeleCompletionInvariant K L v w Ξ x =
      originalFullIdeleCompletionInvariant K L v₀ w₀ Ω x := by
  subst v
  have hb : originalFinitePrimeBelow K L w₀ = originalFinitePrimeBelow K L w :=
    (originalFinitePrimeBelow_eq_of_liesOver K L v₀ w₀).trans
      (originalFinitePrimeBelow_eq_of_liesOver K L v₀ w).symm
  have he := originalFullDecomposition_prime_unique K L w₀ w hw hb
  subst w
  exact originalFullIdeleCompletionInvariant_closure_independent K L v₀ w₀ Ω Ξ x
end SameBase

section OtherBase
variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (w₀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
  (Ξ : Type) [Field Ξ]
  [Algebra (v.adicCompletion K) Ξ] [Algebra (w.adicCompletion L) Ξ]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ξ]
  [IsGalois (v.adicCompletion K) Ξ] [IsSepClosed Ξ]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]

/-- The actual normalized invariant of a class supported at one upper prime vanishes at every other base prime. -/
theorem originalFullIdeleInvariant_eq_zero_of_other_base
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (hs : ∀ t : IsDedekindDomain.HeightOneSpectrum (𝓞 L), t ≠ w₀ →
      originalFullIdeleAdicH2 K L t x = 0)
    (hv : v ≠ originalFinitePrimeBelow K L w₀) :
    originalFullIdeleCompletionInvariant K L v w Ξ x = 0 := by
  apply originalFullIdeleCompletionInvariant_eq_zero_of_adic K L v w Ξ x
  apply hs w
  intro h
  exact hv ((originalFinitePrimeBelow_eq_of_liesOver K L v w).symm.trans
    (congrArg (originalFinitePrimeBelow K L) h))
end OtherBase

end
end Dubon2026
