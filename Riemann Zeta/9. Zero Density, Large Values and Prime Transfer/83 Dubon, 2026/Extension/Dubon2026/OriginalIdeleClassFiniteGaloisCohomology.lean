import Dubon2026.OriginalIdeleClassPGroupCohomology
import Dubon2026.FiniteFirstCohomologySylowDetection
import Dubon2026.SecondCohomologySylowCardinality

/-! # Original idele-class cohomology for every finite Galois extension

Actual Sylow restrictions are the already proved p-group fixed-field
extensions. Existing comparison-trace and primary-component arguments
remove the p-group hypothesis. This supplies arbitrary finite-stage H1
vanishing and H2 size bounds needed for the original global invariant
construction in DUB-17's arithmetic duality dependency chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Original idele-class H1 vanishes for every actual finite Galois number-field extension. -/
theorem originalIdeleClass_finiteGalois_first_zero :
    Limits.IsZero (groupCohomology (originalIdeleClassRep K L) 1) := by
  classical
  apply ModuleCat.isZero_iff_subsingleton.mpr
  suffices hz : ∀ x : groupCohomology (originalIdeleClassRep K L) 1, x = 0 from
    ⟨fun x y => (hz x).trans (hz y).symm⟩
  intro x
  apply finiteFirstCohomology_sylow_zero (originalIdeleClassRep K L) x
  intro p hp _
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p Gal(L/K) := Classical.choice inferInstance
  let S : Subgroup Gal(L/K) := P
  let F := IntermediateField.fixedField S
  have hpG : IsPGroup p Gal(L/F) :=
    P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv S)
  have hz := (originalIdeleClass_pGroup_cohomology p F L hpG).1
  have hz' := hz.of_iso (originalIdeleClassSubgroupCohomologyIso S 1).symm
  haveI := ModuleCat.isZero_iff_subsingleton.mp hz'
  exact ⟨P, Subsingleton.elim _ _⟩

/-- Actual original idele-class H2 is finite and its order divides the original Galois degree. -/
theorem originalIdeleClass_finiteGalois_second_card_dvd :
    Finite (groupCohomology (originalIdeleClassRep K L) 2) ∧
      Nat.card (groupCohomology (originalIdeleClassRep K L) 2) ∣ Module.finrank K L := by
  have h := secondCohomology_card_dvd_of_sylows (originalIdeleClassRep K L) (by
    intro p hp P
    letI : Fact p.Prime := ⟨hp⟩
    let S : Subgroup Gal(L/K) := P
    let F := IntermediateField.fixedField S
    have hpG : IsPGroup p Gal(L/F) :=
      P.isPGroup'.of_equiv (IntermediateField.subgroupEquivAlgEquiv S)
    obtain ⟨_, hf, hd⟩ := originalIdeleClass_pGroup_cohomology p F L hpG
    let e := originalIdeleClassSubgroupCohomologyIso S 2
    haveI := hf
    refine ⟨Finite.of_equiv _ e.toLinearEquiv.toEquiv, ?_⟩
    have hc := Nat.card_congr e.toLinearEquiv.toEquiv
    have hG := Nat.card_congr (IntermediateField.subgroupEquivAlgEquiv S).toEquiv
    rw [← hc]
    exact hd.trans (dvd_of_eq hG.symm))
  rwa [IsGalois.card_aut_eq_finrank K L] at h

end
end Dubon2026
