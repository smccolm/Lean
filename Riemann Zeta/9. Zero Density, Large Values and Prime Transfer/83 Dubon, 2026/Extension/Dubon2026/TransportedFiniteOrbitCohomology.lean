import Dubon2026.TransportedOrbitDecomposition
import Dubon2026.PermutationOrbitCohomology

/-! # Cohomology of finite transported products through actual stabilizer factors

The actual orbit decomposition, existing finite-product preservation and
proved transported Shapiro comparison give a single cohomology isomorphism.
This computes DUB-17's unrestricted idele factor from the original local
stabilizer modules without a supplied global cohomological formula.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped Classical
variable (R G ι : Type) [CommRing R] [CommGroup G] [MulAction G ι] [Fintype ι]
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (T : ∀ (g : G) (i j : ι), g • i = j → M i ≃ₗ[R] M j)
  (T_one : ∀ (i : ι) (x : M i), T 1 i i (one_smul G i) x = x)
  (T_mul : ∀ (g h : G) (i j k : ι) (hh : h • i = j) (hg : g • j = k)
    (hgh : (g * h) • i = k) (x : M i),
    T (g * h) i k hgh x = T g j k hg (T h i j hh x))

/-- Original cohomology of the finite transported product is the product of its original stabilizer cohomologies. -/
def transportedFiniteOrbitCohomologyIso (n : ℕ) :
    groupCohomology (transportedPiRep R G ι M T T_one T_mul) n ≅
      ModuleCat.of R (∀ ω : MulAction.orbitRel.Quotient G ι,
        groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
          (permutationOrbitPoint G ι ω)) n) :=
  (groupCohomology.functor R G n).mapIso (transportedOrbitProductIso R G ι M T T_one T_mul) ≪≫
    originalFinitePiCohomologyIso (transportedOrbitFactorRep R G ι M T T_one T_mul) n ≪≫
    (LinearEquiv.piCongrRight (fun ω =>
      (transportedOrbitFactorCohomologyIso R G ι M T T_one T_mul ω
        (permutationOrbitPoint G ι ω) n).toLinearEquiv)).toModuleIso

/-- The original finite transported-product cohomology has the product of the actual stabilizer-cohomology orders. -/
theorem transportedFiniteOrbit_cohomology_card (n : ℕ) :
    Nat.card (groupCohomology (transportedPiRep R G ι M T T_one T_mul) n) =
      ∏ ω : MulAction.orbitRel.Quotient G ι,
        Nat.card (groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
          (permutationOrbitPoint G ι ω)) n) :=
  (Nat.card_congr (transportedFiniteOrbitCohomologyIso R G ι M T T_one T_mul n).toLinearEquiv.toEquiv).trans
    Nat.card_pi

/-- Finite actual stabilizer cohomology gives finite original transported-product cohomology. -/
theorem transportedFiniteOrbit_cohomology_finite (n : ℕ)
    [∀ ω : MulAction.orbitRel.Quotient G ι,
      Finite (groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
        (permutationOrbitPoint G ι ω)) n)] :
    Finite (groupCohomology (transportedPiRep R G ι M T T_one T_mul) n) :=
  Finite.of_equiv (∀ ω : MulAction.orbitRel.Quotient G ι,
      groupCohomology (transportedOrbitPointRep R G ι M T T_one T_mul ω
        (permutationOrbitPoint G ι ω)) n)
    (transportedFiniteOrbitCohomologyIso R G ι M T T_one T_mul n).symm.toLinearEquiv.toEquiv

end
end Dubon2026
