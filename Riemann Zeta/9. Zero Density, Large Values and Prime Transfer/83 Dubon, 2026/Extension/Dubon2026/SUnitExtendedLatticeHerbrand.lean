import Dubon2026.SUnitFiniteIndexRepresentation
import Dubon2026.PermutedBasisCohomology

/-! # The original extended S-unit lattice Herbrand formula

The constructed actual finite-index subrepresentation has a basis
permuted by the actual logarithmic-place action. Its original cohomology
is computed by the orbit-stabilizer theorem. The original finite-index
comparison derives ambient H1/H2 finiteness and its exact cardinal ratio.
No lattice cohomology assumption remains. This is the main arithmetic
input to DUB-17's S-unit Herbrand calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original extended S-unit lattice has finite H1/H2 and its Herbrand ratio is exactly the original place-orbit stabilizer product. -/
theorem sUnitExtended_log_lattice_herbrand
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitExtendedLogRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 2) =
        Nat.card (groupCohomology (sUnitExtendedLogRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out) := by
  letI := sUnitLogPlaceAction K L S hS
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : IsCyclic Gal(L/K) := ⟨⟨σ, hgen⟩⟩
  letI := IsCyclic.commGroup (α := Gal(L/K))
  let A := sUnitExtendedLogRep K L S hS
  obtain ⟨W, hW, hfinite, b, hb⟩ := sUnitExtended_exists_permutation_subrepresentation K L S hS
  letI : Finite (A ⧸ W) := hfinite
  have hp := permutedBasis_cohomology_orders Gal(L/K) (SUnitLogPlace L S)
    (A.subrepresentation W hW) b hb
  letI := hp.1
  letI := hp.2.1
  have hc := @finiteIndex_herbrand_comparison Gal(L/K) _ _ A W hW σ hgen hfinite hp.1 hp.2.1
  refine ⟨hc.1, hc.2.1, ?_⟩
  have h := hc.2.2
  rw [hp.2.2.1, mul_one, hp.2.2.2] at h
  exact h

end
end Dubon2026
