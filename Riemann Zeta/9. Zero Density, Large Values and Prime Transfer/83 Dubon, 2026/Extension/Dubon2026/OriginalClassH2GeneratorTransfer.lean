import Dubon2026.OriginalH2GeneratorInflationTransfer
import Dubon2026.OriginalIdeleClassFiniteGaloisCohomology

/-! # Original arithmetic class H2 generator transfer

The adapted auxiliary-class argument consumes the genuine idele classes.
Original fixed-field comparisons discharge subgroup H1 vanishing and the
target H2 size bound. Only the auxiliary finite-order class and its actual
vanishing restriction remain to be constructed for DUB-17's normalized
class-formation invariant. No normalized invariant is asserted here.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Actual normal-quotient invariant full-class H2 is finite and bounded by the original quotient order. -/
theorem originalIdeleClass_normalQuotient_second_finite_card_le
    (S : Subgroup Gal(L/K)) [S.Normal] :
    Finite (groupCohomology ((originalIdeleClassRep K L).quotientToInvariants S) 2) ∧
      Nat.card (groupCohomology ((originalIdeleClassRep K L).quotientToInvariants S) 2) ≤
        Nat.card (Gal(L/K) ⧸ S) := by
  let F := IntermediateField.fixedField S
  letI : IsGalois K F := IsGalois.of_fixedField_normal_subgroup S
  let e := (originalIdeleClassNormalInvariantCohomologyIso S 2).toLinearEquiv.toEquiv
  obtain ⟨hf, hd⟩ := originalIdeleClass_finiteGalois_second_card_dvd K F
  haveI := hf
  refine ⟨Finite.of_equiv _ e, ?_⟩
  rw [← Nat.card_congr e]
  have hle := Nat.le_of_dvd (Module.finrank_pos (R := K) (M := F)) hd
  have hc : Nat.card (Gal(L/K) ⧸ S) = Module.finrank K F :=
    (Nat.card_congr (IsGalois.normalAutEquivQuotient S).toEquiv).trans
      (IsGalois.card_aut_eq_finrank K F)
  exact hle.trans_eq hc.symm

/-- An auxiliary genuine class of sufficient order with zero original restriction supplies a generator of the target arithmetic quotient H2. -/
theorem originalIdeleClass_quotientH2_generator_from_auxiliary
    (S T : Subgroup Gal(L/K)) [S.Normal] [T.Normal]
    [Fintype Gal(L/K)] [Fintype (Gal(L/K) ⧸ S)]
    (n' : ℕ) (hn : Fintype.card (Gal(L/K) ⧸ S) ∣ n') (hn'0 : n' ≠ 0)
    (u' : groupCohomology ((originalIdeleClassRep K L).quotientToInvariants T) 2)
    (hu' : addOrderOf u' = n')
    (hres : (map S.subtype (𝟙 (Rep.res S.subtype (originalIdeleClassRep K L))) 2).hom
        ((n' / Fintype.card (Gal(L/K) ⧸ S)) •
          (map (A := (originalIdeleClassRep K L).quotientToInvariants T)
            (B := originalIdeleClassRep K L) (QuotientGroup.mk' T)
            (ofHom ((originalIdeleClassRep K L).ρ.quotientToInvariants_lift T)) 2).hom u') = 0) :
    ∃ y : groupCohomology ((originalIdeleClassRep K L).quotientToInvariants S) 2,
      Nat.card (groupCohomology ((originalIdeleClassRep K L).quotientToInvariants S) 2) =
        Fintype.card (Gal(L/K) ⧸ S) ∧
      Submodule.span ℤ {y} = ⊤ ∧
      (map (A := (originalIdeleClassRep K L).quotientToInvariants S)
        (B := originalIdeleClassRep K L) (QuotientGroup.mk' S)
        (ofHom ((originalIdeleClassRep K L).ρ.quotientToInvariants_lift S)) 2).hom y =
        (n' / Fintype.card (Gal(L/K) ⧸ S)) •
          (map (A := (originalIdeleClassRep K L).quotientToInvariants T)
            (B := originalIdeleClassRep K L) (QuotientGroup.mk' T)
            (ofHom ((originalIdeleClassRep K L).ρ.quotientToInvariants_lift T)) 2).hom u' := by
  have hS1 := (originalIdeleClass_finiteGalois_first_zero (IntermediateField.fixedField S) L).of_iso
    (originalIdeleClassSubgroupCohomologyIso S 1).symm
  have hT1 := (originalIdeleClass_finiteGalois_first_zero (IntermediateField.fixedField T) L).of_iso
    (originalIdeleClassSubgroupCohomologyIso T 1).symm
  obtain ⟨hf, hle⟩ := originalIdeleClass_normalQuotient_second_finite_card_le K L S
  rw [Nat.card_eq_fintype_card (α := Gal(L/K) ⧸ S)] at hle
  exact originalH2_generator_from_inflated_cyclic_class (originalIdeleClassRep K L) S T
    hS1 hT1 n' hn hn'0 u' hu' hres hf hle

end
end Dubon2026
