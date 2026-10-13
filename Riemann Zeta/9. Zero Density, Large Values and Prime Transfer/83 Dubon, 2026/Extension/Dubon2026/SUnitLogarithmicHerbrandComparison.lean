import Dubon2026.SUnitLogarithmicKernelCardinality
import Dubon2026.CyclicCohomologyHerbrandMultiplicativity

/-! # Original S-unit and logarithmic-lattice Herbrand comparison

Apply the original cohomological multiplicativity theorem to the actual
logarithmic short exact sequence. The actual finite torsion kernel has
equal H1/H2 orders, so its positive order cancels. Finiteness and the
Herbrand cardinality of the original logarithmic lattice remain explicit
upstream inputs; no final S-unit quotient is assumed. This reduces
DUB-17's S-unit calculation to the proved finite-index permutation route.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual S-unit Herbrand cardinal ratio equals its actual logarithmic-lattice ratio; only lattice cohomology finiteness is assumed. -/
theorem sUnit_logarithmic_herbrand_comparison
    (σ : Gal(L/K)) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    [Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1)]
    [Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2)] :
    Finite (groupCohomology (sUnitOriginalRep K L S hS) 1) ∧
      Finite (groupCohomology (sUnitOriginalRep K L S hS) 2) ∧
      Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 2) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 1) =
        Nat.card (groupCohomology (sUnitOriginalRep K L S hS) 1) *
          Nat.card (groupCohomology (sUnitLogLatticeRep K L S hS) 2) := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  letI : IsCyclic Gal(L/K) := ⟨⟨σ, hgen⟩⟩
  letI := IsCyclic.commGroup (α := Gal(L/K))
  let X := sUnitLogarithmicShortComplex K L S hS
  letI : Finite (groupCohomology X.X₁ 1) := sUnitLogarithmicKernel_cohomology_finite K L S hS 1
  letI : Finite (groupCohomology X.X₁ 2) := sUnitLogarithmicKernel_cohomology_finite K L S hS 2
  letI : Finite (groupCohomology X.X₃ 1) :=
    inferInstanceAs (Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 1))
  letI : Finite (groupCohomology X.X₃ 2) :=
    inferInstanceAs (Finite (groupCohomology (sUnitLogLatticeRep K L S hS) 2))
  have h := cyclic_cohomology_herbrand_cardinality X
    (sUnitLogarithmicShortComplex_shortExact K L S hS) σ hgen
  refine ⟨h.1, h.2.1, ?_⟩
  change Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₃ 1) =
    Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₃ 2)
  have heq : Nat.card (groupCohomology X.X₁ 1) = Nat.card (groupCohomology X.X₁ 2) :=
    sUnitLogarithmicKernel_first_second_card_eq K L S hS σ hgen
  have hc := h.2.2
  rw [← heq] at hc
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := groupCohomology X.X₁ 1))
  calc
    Nat.card (groupCohomology X.X₁ 1) *
        (Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₃ 1)) =
      Nat.card (groupCohomology X.X₂ 2) * Nat.card (groupCohomology X.X₁ 1) *
        Nat.card (groupCohomology X.X₃ 1) := by ac_rfl
    _ = Nat.card (groupCohomology X.X₂ 1) * Nat.card (groupCohomology X.X₁ 1) *
        Nat.card (groupCohomology X.X₃ 2) := hc
    _ = _ := by ac_rfl

end
end Dubon2026
