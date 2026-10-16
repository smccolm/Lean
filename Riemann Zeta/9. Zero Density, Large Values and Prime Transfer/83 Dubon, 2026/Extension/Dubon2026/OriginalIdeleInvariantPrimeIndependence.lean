import Dubon2026.OriginalIdelePrimeInvariantTransport
import Dubon2026.OriginalFullIdeleInvariantPrimeSupport

/-! # Original completion invariants at arbitrary primes over the same base

The actual Galois prime action supplies the transport. Inflation composition
and closure independence then compare the normalized values without a
full-decomposition hypothesis. This discharges the prime-choice comparison
needed by DUB-17's local-to-global class normalization.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
  (u w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
  (Ω Ξ : Type) [Field Ω] [Field Ξ]
  [Algebra (v.adicCompletion K) Ω] [Algebra (u.adicCompletion L) Ω]
  [Algebra (v.adicCompletion K) Ξ] [Algebra (w.adicCompletion L) Ξ]
  [IsScalarTower (v.adicCompletion K) (u.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ξ]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [IsGalois (v.adicCompletion K) Ξ] [IsSepClosed Ξ]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ξ)]

/-- Every original upper prime and compatible closure over the same base prime gives the same normalized invariant of the actual global idele class. -/
theorem originalFullIdeleCompletionInvariant_prime_independent
    (x : groupCohomology (originalFullIdeleRep K L) 2) :
    originalFullIdeleCompletionInvariant K L v w Ξ x =
      originalFullIdeleCompletionInvariant K L v u Ω x := by
  have hb : originalFinitePrimeBelow K L u = originalFinitePrimeBelow K L w :=
    (originalFinitePrimeBelow_eq_of_liesOver K L v u).trans
      (originalFinitePrimeBelow_eq_of_liesOver K L v w).symm
  obtain ⟨σ, hσ⟩ := (originalFinitePrimeBelow_eq_iff_orbit K L u w).mp hb
  let e := originalAdicPrimeTransportAlgEquiv K L v u w σ hσ
  let j := (IsScalarTower.toAlgHom (v.adicCompletion K) (w.adicCompletion L) Ξ).comp e.toAlgHom
  letI : Algebra (u.adicCompletion L) Ξ := j.toRingHom.toAlgebra
  letI : IsScalarTower (v.adicCompletion K) (u.adicCompletion L) Ξ := IsScalarTower.of_algHom j
  exact (originalFullIdeleCompletionInvariant_prime_transport K L v u w σ hσ Ξ x).trans
    (originalFullIdeleCompletionInvariant_closure_independent K L v u Ω Ξ x)

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

/-- Equality of the base primes alone suffices for normalized invariant equality at arbitrary original upper primes and compatible closures. -/
theorem originalFullIdeleCompletionInvariant_same_base
    (hv : v = v₀) (x : groupCohomology (originalFullIdeleRep K L) 2) :
    originalFullIdeleCompletionInvariant K L v w Ξ x =
      originalFullIdeleCompletionInvariant K L v₀ w₀ Ω x := by
  subst v
  exact originalFullIdeleCompletionInvariant_prime_independent K L v₀ w₀ w Ω Ξ x

end SameBase

end
end Dubon2026
