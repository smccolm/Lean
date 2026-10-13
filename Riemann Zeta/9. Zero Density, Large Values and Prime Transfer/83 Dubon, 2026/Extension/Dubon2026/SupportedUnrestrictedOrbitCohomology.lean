import Dubon2026.SupportedUnrestrictedUnitTransports
import Dubon2026.TransportedFiniteOrbitCohomology

/-! # Original unrestricted idele cohomology through its actual local stabilizers

The original completion-unit transports instantiate the proved orbit
and Shapiro comparison on the same places as the S-unit formula. The
remaining local computations concern the displayed original stabilizer
modules, not a hypothesized supported-idele Herbrand factor. This is the
unrestricted part of DUB-17's global norm-index dependency.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [IsCyclic Gal(L/K)]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual original completion-unit module at an original unrestricted orbit representative. -/
def supportedUnrestrictedOrbitPointRep :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      Rep ℤ (MulAction.stabilizer Gal(L/K) (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  intro ω
  exact transportedOrbitPointRep ℤ Gal(L/K) (SUnitLogPlace L S) (supportedUnrestrictedUnitModule L S)
    (supportedUnrestrictedUnitTransport K L S hS)
    (supportedUnrestrictedUnitTransport_one K L S hS)
    (supportedUnrestrictedUnitTransport_mul K L S hS) ω
    (permutationOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)

/-- Original unrestricted idele cohomology is the product of its actual original local-stabilizer cohomologies. -/
def supportedUnrestrictedOrbitCohomologyEquiv (n : ℕ) :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    groupCohomology (supportedUnrestrictedUnitRep K L S hS) n ≃
      (∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) n) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  exact (transportedFiniteOrbitCohomologyIso ℤ Gal(L/K) (SUnitLogPlace L S)
    (supportedUnrestrictedUnitModule L S)
    (supportedUnrestrictedUnitTransport K L S hS)
    (supportedUnrestrictedUnitTransport_one K L S hS)
    (supportedUnrestrictedUnitTransport_mul K L S hS) n).toLinearEquiv.toEquiv

/-- The actual unrestricted idele-cohomology order is the product of its actual local-stabilizer orders. -/
theorem supportedUnrestrictedUnit_cohomology_card (n : ℕ) :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    Nat.card (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n) =
      ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
        Nat.card (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) n) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  exact (Nat.card_congr
    (supportedUnrestrictedOrbitCohomologyEquiv K L S hS n)).trans Nat.card_pi

/-- Finite original local-stabilizer cohomologies imply finite actual unrestricted idele cohomology. -/
theorem supportedUnrestrictedUnit_cohomology_finite (n : ℕ) :
    letI := IsCyclic.commGroup (α := Gal(L/K))
    letI := sUnitLogPlaceAction K L S hS
    (∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      Finite (groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) n)) →
    Finite (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n) := by
  letI := IsCyclic.commGroup (α := Gal(L/K))
  letI := sUnitLogPlaceAction K L S hS
  intro hf
  letI := hf
  exact Finite.of_equiv (∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      groupCohomology (supportedUnrestrictedOrbitPointRep K L S hS ω) n)
    (supportedUnrestrictedOrbitCohomologyEquiv K L S hS n).symm

end
end Dubon2026
