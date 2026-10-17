import Dubon2026.FiniteCohomologySylowDetection
import Dubon2026.OriginalFiniteNormHomology
import Dubon2026.OriginalPGroupInternalHomAcyclicity
import Dubon2026.OriginalRegularSubgroupAcyclicity

/-! # The two finite internal-Hom degrees required by actual norm duality

Detect the actual lattice internal Hom on Sylow subgroups, reusing the
proved p-group theorem. Its two subgroup degrees discharge invariant norm
lifting, norm injectivity on coinvariants and first homology vanishing.
These feed DUB-17's original norm-quotient/homology equivalence, without a
new general projectivity proof or a Tate-duality dependency closure.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Fintype G] (M B : Rep.{0} ℤ G)
  [Module.Projective ℤ M]

/-- The original lattice internal Hom has zero H1 and H2 for any finite
group when the target has the two actual subgroup degrees. -/
theorem originalFinite_internalHom_first_second_zero
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    Limits.IsZero (groupCohomology ((Rep.ihom M).obj B) 1) ∧
      Limits.IsZero (groupCohomology ((Rep.ihom M).obj B) 2) := by
  have hpos (n : ℕ) : Limits.IsZero (groupCohomology ((Rep.ihom M).obj B) (n + 1)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply subsingleton_of_forall_eq 0
    intro x
    apply finiteCohomology_sylow_zero ((Rep.ihom M).obj B) (n + 1) x
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    let P : Sylow p G := Classical.choice inferInstance
    let S : Subgroup G := P
    letI : Fintype S := Fintype.ofFinite S
    letI : Module.Projective ℤ (Rep.res S.subtype M) := ‹Module.Projective ℤ M›
    have hS (T : Subgroup S) :
        Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 1) ∧
          Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 2) :=
      ⟨originalNestedSubgroup_zero B S T 1 (h _).1,
        originalNestedSubgroup_zero B S T 2 (h _).2⟩
    have hz : Limits.IsZero
        (groupCohomology (Rep.res S.subtype ((Rep.ihom M).obj B)) (n + 1)) :=
      originalPGroup_internalHom_positive_zero (Rep.res S.subtype M)
        (Rep.res S.subtype B) p P.isPGroup' hS n
    haveI := ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨P, Subsingleton.elim _ _⟩
  exact ⟨hpos 0, hpos 1⟩

/-- The two actual internal-Hom degrees vanish on every original subgroup. -/
theorem originalFinite_internalHom_subgroup_first_second_zero
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) (S : Subgroup G) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype ((Rep.ihom M).obj B)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res S.subtype ((Rep.ihom M).obj B)) 2) := by
  letI : Fintype S := Fintype.ofFinite S
  letI : Module.Projective ℤ (Rep.res S.subtype M) := ‹Module.Projective ℤ M›
  have hS (T : Subgroup S) :
      Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 2) :=
    ⟨originalNestedSubgroup_zero B S T 1 (h _).1,
      originalNestedSubgroup_zero B S T 2 (h _).2⟩
  exact originalFinite_internalHom_first_second_zero
    (Rep.res S.subtype M) (Rep.res S.subtype B) hS

/-- Every invariant in the actual lattice internal Hom is a literal norm. -/
theorem originalFinite_internalHom_norm_preimages
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    OriginalInvariantNormSurjective ((Rep.ihom M).obj B) :=
  originalFinite_norm_preimages_of_subgroup_first_second _
    (originalFinite_internalHom_subgroup_first_second_zero M B h)

/-- The actual internal Hom has injective coinvariant norm and zero
first homology, with both conditions derived from the original target. -/
theorem originalFinite_internalHom_norm_homology
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    OriginalNormCoinvariantInjective ((Rep.ihom M).obj B) ∧
      Limits.IsZero (groupHomology ((Rep.ihom M).obj B) 1) := by
  have hS := originalFinite_internalHom_subgroup_first_second_zero M B h
  exact ⟨originalFinite_normCoinvariantInjective _ hS,
    originalFinite_first_homology_zero _ hS⟩

/-- The same two literal norm/homology conditions hold for the original
regular target, with its subgroup vanishing supplied by existing proofs. -/
theorem originalFinite_regularInternalHom_norm_homology :
    OriginalNormCoinvariantInjective ((Rep.ihom M).obj (Rep.leftRegular ℤ G)) ∧
      Limits.IsZero (groupHomology ((Rep.ihom M).obj (Rep.leftRegular ℤ G)) 1) :=
  originalFinite_internalHom_norm_homology M (Rep.leftRegular ℤ G)
    (fun S => ⟨originalRegularSubgroup_positive_zero (k := ℤ) S 0,
      originalRegularSubgroup_positive_zero (k := ℤ) S 1⟩)

end
end Dubon2026
