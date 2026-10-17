import Dubon2026.OriginalAdicSubgroupCohomology
import Dubon2026.OriginalH2GeneratorRestriction
import Dubon2026.OriginalCohomologyRestrictionTrace
import Dubon2026.OriginalFundamentalTwoDegreeVanishing

/-! # Actual local fundamental-coefficient acyclicity

The proved local subgroup bounds and Hilbert 90 discharge the cohomology
inputs. Only full order of the selected local class remains explicit;
the completion normalization supplies it in the local/global consumer.
This serves DUB-17's outside-unit inertia and prescribed-support chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

include v in
/-- A full-order original local H2 class restricts to generators on
every actual decomposition subgroup, without size or trace premises. -/
theorem originalAdicUnit_full_order_restricts_to_generators
    (u : groupCohomology (originalAdicUnitRep K L w) 2)
    (hu : addOrderOf u = Nat.card (OriginalFiniteDecompositionGroup K L w)) :
    (∀ S : Subgroup (OriginalFiniteDecompositionGroup K L w),
      Nat.card (groupCohomology (Rep.res S.subtype (originalAdicUnitRep K L w)) 2) = Nat.card S) ∧
    (∀ S : Subgroup (OriginalFiniteDecompositionGroup K L w), Submodule.span ℤ
      {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (originalAdicUnitRep K L w))) 2).hom u} = ⊤) := by
  classical
  let C := originalAdicUnitRep K L w
  letI (S : Subgroup (OriginalFiniteDecompositionGroup K L w)) :
      Fintype ((OriginalFiniteDecompositionGroup K L w) ⧸ S) := Fintype.ofFinite _
  have hsize : ∀ (S : Subgroup (OriginalFiniteDecompositionGroup K L w)) [Fintype S],
      Finite (groupCohomology (Rep.res S.subtype C) 2) ∧
        Nat.card (groupCohomology (Rep.res S.subtype C) 2) ≤ Fintype.card S := by
    intro S _
    simpa only [Nat.card_eq_fintype_card (α := S)] using
      originalAdicUnit_subgroup_second_finite_card_le K L v w S
  obtain ⟨hc, hg⟩ := originalH2_generator_restricts_to_subgroups C u hu hsize
    (fun S => (subgroupCohomologyTrace C S 2).hom)
    (fun S x => originalCohomology_trace_restriction_apply C S 2 x)
  refine ⟨fun S => ?_, hg⟩
  letI : Fintype S := Fintype.ofFinite S
  exact (hc S).trans Nat.card_eq_fintype_card.symm

include v in
/-- Full order of the actual local class gives the needed fundamental
H1/H2 vanishing on every decomposition subgroup. -/
theorem originalAdicUnit_fundamental_subgroup_first_second_zero
    (φ : groupCohomology.cocycles₂ (originalAdicUnitRep K L w))
    (hφ : addOrderOf (groupCohomology.H2π (originalAdicUnitRep K L w) φ) =
      Nat.card (OriginalFiniteDecompositionGroup K L w)) :
    ∀ S : Subgroup (OriginalFiniteDecompositionGroup K L w),
      Limits.IsZero (groupCohomology (Rep.res S.subtype
        (originalFundamentalSplittingModule (originalAdicUnitRep K L w) φ)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype
        (originalFundamentalSplittingModule (originalAdicUnitRep K L w) φ)) 2) := by
  obtain ⟨hc, hg⟩ := originalAdicUnit_full_order_restricts_to_generators K L v w _ hφ
  intro S
  letI : Fintype S := Fintype.ofFinite S
  exact originalFundamentalSubgroup_first_second_zero (originalAdicUnitRep K L w) φ S
    (originalAdicUnit_subgroup_first_zero K L v w S)
    ((hc S).trans Nat.card_eq_fintype_card) (hg S)

end
end Dubon2026
