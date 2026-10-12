import Dubon2026.GaloisNormalInvariantUnitCoefficients
import Dubon2026.SecondCohomologyNormalSubgroupCardinality

/-! # Original Galois unit H2 cardinality through the genuine fixed-field tower -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (S : Subgroup Gal(L/K)) [S.Normal]

/-- The quotient-invariant cohomology is the cohomology of the actual
fixed-field units over the original base, with their original Galois action. -/
def galoisNormalInvariantUnitCohomologyIso (n : ℕ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) n ≅
      groupCohomology ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants S) n :=
  originalCohomologyReindex _ (IsGalois.normalAutEquivQuotient S) n ≪≫
    (groupCohomology.functor ℤ (Gal(L/K) ⧸ S) n).mapIso
      (galoisNormalInvariantUnitCoefficientIso S)

/-- Actual H2 of extension-field units is finite, and its order divides
the product of the two actual fixed-field tower H2 orders. The hypotheses
assert finiteness only; Hilbert 90 and the original dimension shift supply
the exactness needed for this genuine order divisibility. -/
theorem galoisUnit_second_cohomology_fixedField_card_dvd
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) 2)]
    [Finite (groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) 2)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∣
        Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K (IntermediateField.fixedField S)) 2) *
          Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits (IntermediateField.fixedField S) L) 2) := by
  let eQ := galoisNormalInvariantUnitCohomologyIso S 2
  let eS := galoisSubgroupUnitCohomologyIso S 2
  haveI : Finite (groupCohomology ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants S) 2) :=
    Finite.of_equiv _ eQ.toLinearEquiv.toEquiv
  haveI : Finite (groupCohomology (Rep.res S.subtype (Rep.ofAlgebraAutOnUnits K L)) 2) :=
    Finite.of_equiv _ eS.toLinearEquiv.toEquiv
  obtain ⟨hfinite, hdvd⟩ := secondCohomology_normal_subgroup_card_dvd
    (Rep.ofAlgebraAutOnUnits K L) S (galoisSubgroupUnit_first_cohomology_zero S)
  refine ⟨hfinite, ?_⟩
  have hQ := Nat.card_congr eQ.toLinearEquiv.toEquiv
  have hS := Nat.card_congr eS.toLinearEquiv.toEquiv
  rwa [← hQ, ← hS] at hdvd

end
end Dubon2026
