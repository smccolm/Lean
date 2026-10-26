import Dubon2026.SourceCoefficientPermutationCoordinates
import Dubon2026.PermutationOrbitDecomposition
import Dubon2026.TransitivePermutationCoinduction

/-! DUB-17/18 -> original all-weight adic association -> geometric
finite-level realization. Reuse the proved orbit decomposition, finite
product cohomology and native Shapiro comparison on the same original
coefficient vectors. No new coinduction or transfer theory is developed. -/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G : Type} [CommRing R] [Group G]
attribute [local instance] sourceCoefficientVectorAction

/-- The actual chosen vector, considered inside its own coefficient orbit. -/
def sourceCoefficientOrbitPoint (A : Rep R G)
    (ω : MulAction.orbitRel.Quotient G A) : ω.orbit :=
  ⟨ω.out, MulAction.orbitRel.Quotient.mem_orbit.mpr (Quotient.out_eq' ω)⟩

/-- Each actual finite coefficient orbit has a finite-index stabilizer. -/
theorem sourceCoefficientOrbitStabilizer_finiteIndex
    (A : Rep R G) [Finite A] (ω : MulAction.orbitRel.Quotient G A) :
    (MulAction.stabilizer G (sourceCoefficientOrbitPoint A ω)).FiniteIndex := by
  letI := Finite.of_equiv
    (MulAction.orbit G (sourceCoefficientOrbitPoint A ω))
    (MulAction.orbitEquivQuotientStabilizer G (sourceCoefficientOrbitPoint A ω))
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Original finite permutation H1 is the product of trivial-coefficient
H1 groups of the stabilizers of its actual coefficient orbits. -/
def sourceCoefficientStabilizerH1Equiv (A : Rep R G) [Fintype A] :
    groupCohomology.H1 (sourceCoefficientPermutationRep A) ≃ₗ[R]
      (∀ ω : MulAction.orbitRel.Quotient G A,
        groupCohomology.H1 (Rep.trivial R
          (MulAction.stabilizer G (sourceCoefficientOrbitPoint A ω)) R)) := by
  classical
  let e := ((groupCohomology.functor R G 1).mapIso
      (sourceCoefficientPermutationCoordinateIso A) ≪≫
    (groupCohomology.functor R G 1).mapIso (permutationOrbitRepIso R G A) ≪≫
    originalFinitePiCohomologyIso
      (fun ω : MulAction.orbitRel.Quotient G A => permutationCoordinateRep R G ω.orbit) 1)
  exact e.toLinearEquiv.trans (LinearEquiv.piCongrRight (fun ω =>
    (transitivePermutationCohomologyIso R G ω.orbit
      (sourceCoefficientOrbitPoint A ω) 1).toLinearEquiv))

end
end Dubon2026
