import Dubon2026.TransportedOrbitDecomposition
import Dubon2026.OriginalProductH2Detection

/-! # Original transported H2 detection without a cyclic group hypothesis

The existing orbit decomposition and Shapiro isomorphism already apply
to arbitrary groups. Coordinate H2 detection removes the cyclic product
hypothesis, as required for the outside-support part of DUB-17's actual
global-to-local H2 injection and arithmetic invariant sum-zero.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable (R G ι : Type) [CommRing R] [Group G] [MulAction G ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))

/-- The actual original point in its orbit, for an arbitrary acting group. -/
def originalOrbitPoint (ω : MulAction.orbitRel.Quotient G ι) : ω.orbit :=
  ⟨ω.out, MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' ω)⟩

/-- Vanishing of the actual stabilizer H2 groups kills the original transported-product H2. -/
theorem originalTransported_second_zero_of_stabilizers
    (hz : ∀ ω : MulAction.orbitRel.Quotient G ι,
      Limits.IsZero (groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
        (originalOrbitPoint G ι ω)) 2)) :
    Limits.IsZero (groupCohomology (transportedPiRep R G ι M T T_one T_mul) 2) := by
  let A := transportedOrbitFactorRep R G ι M T T_one T_mul
  have ha (ω : MulAction.orbitRel.Quotient G ι) :
      Limits.IsZero (groupCohomology (A ω) 2) :=
    Limits.IsZero.of_iso (hz ω)
      (transportedOrbitFactorCohomologyIso R G ι M T T_one T_mul ω
        (originalOrbitPoint G ι ω) 2)
  exact Limits.IsZero.of_iso (originalPi_second_cohomology_zero A ha)
    ((groupCohomology.functor R G 2).mapIso
      (transportedOrbitProductIso R G ι M T T_one T_mul))

end
end Dubon2026
