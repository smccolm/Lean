import Dubon2026.SUnitExtendedLatticeHerbrand
import Dubon2026.SUnitDiagonalHerbrandFactor
import Dubon2026.SUnitLogarithmicHerbrandComparison

/-! # The original S-unit Herbrand cardinality formula

For the original finite Galois-stable support and actual cyclic Galois
action, H1 and H2 of the original S-units are finite. Their cardinal ratio
is the product of the original place-orbit stabilizer orders divided by
the Galois group order. All lattice and cohomology finiteness inputs are
derived through the actual logarithm, finite torsion kernel, constructed
permutation sublattice and invariant diagonal. This discharges the S-unit
factor in DUB-17's global norm-index route; supported-idele cohomology and
the resulting global norm index remain separate necessary obligations.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual cyclic S-unit cohomology groups are finite and satisfy the exact original orbit-stabilizer Herbrand cardinality formula, without cohomological hypotheses. -/
theorem original_sUnit_herbrand_cardinality
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    letI := sUnitLogPlaceAction K L S hS
    Finite (groupCohomology (sUnitOriginalRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitOriginalRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 2) * Nat.card Gal(L/K) =
        Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 1) *
          ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
            Nat.card (MulAction.stabilizer Gal(L/K) ω.out) := by
  letI := sUnitLogPlaceAction K L S hS
  let U := sUnitOriginalRep K L S hS
  let V := sUnitLogLatticeRep K L S hS
  let E := sUnitExtendedLogRep K L S hS
  let p := ∏ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
    Nat.card (MulAction.stabilizer Gal(L/K) ω.out)
  have he := sUnitExtended_log_lattice_herbrand K L S hS σ hgen
  letI : Finite (groupCohomology E 1) := he.1
  letI : Finite (groupCohomology E 2) := he.2.1
  have hd := sUnit_diagonal_herbrand_factor K L S hS σ hgen
  letI : Finite (groupCohomology V 1) := hd.1
  letI : Finite (groupCohomology V 2) := hd.2.1
  have hu := sUnit_logarithmic_herbrand_comparison K L S hS σ hgen
  have hlog : Nat.card (groupCohomology V 2) * Nat.card Gal(L/K) =
      Nat.card (groupCohomology V 1) * p := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := groupCohomology E 1))
    calc
      Nat.card (groupCohomology E 1) *
          (Nat.card (groupCohomology V 2) * Nat.card Gal(L/K)) =
        Nat.card (groupCohomology E 2) * Nat.card (groupCohomology V 1) := by
          simpa only [mul_assoc] using hd.2.2.symm
      _ = Nat.card (groupCohomology E 1) * (Nat.card (groupCohomology V 1) * p) := by
        have heq : Nat.card (groupCohomology E 2) = Nat.card (groupCohomology E 1) * p := he.2.2
        rw [heq]
        ac_rfl
  refine ⟨hu.1, hu.2.1, ?_⟩
  change Nat.card (groupCohomology U 2) * Nat.card Gal(L/K) =
    Nat.card (groupCohomology U 1) * p
  have heq : Nat.card (groupCohomology U 2) * Nat.card (groupCohomology V 1) =
      Nat.card (groupCohomology U 1) * Nat.card (groupCohomology V 2) := hu.2.2
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := groupCohomology V 1))
  calc
    (Nat.card (groupCohomology U 2) * Nat.card Gal(L/K)) * Nat.card (groupCohomology V 1) =
      (Nat.card (groupCohomology U 2) * Nat.card (groupCohomology V 1)) * Nat.card Gal(L/K) := by ac_rfl
    _ = (Nat.card (groupCohomology U 1) * Nat.card (groupCohomology V 2)) * Nat.card Gal(L/K) := by rw [heq]
    _ = Nat.card (groupCohomology U 1) * (Nat.card (groupCohomology V 2) * Nat.card Gal(L/K)) := by ac_rfl
    _ = Nat.card (groupCohomology U 1) * (Nat.card (groupCohomology V 1) * p) := by rw [hlog]
    _ = (Nat.card (groupCohomology U 1) * p) * Nat.card (groupCohomology V 1) := by ac_rfl

end
end Dubon2026
