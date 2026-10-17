import Dubon2026.OriginalPGroupRelationKernelProjective
import Dubon2026.OriginalProjectiveTargetInternalHom
import Dubon2026.OriginalInternalHomShortExact

/-! # Lattice internal-Hom acyclicity of the original fundamental coefficient

Apply literal internal Hom to the actual short exact projective
presentation. The two projective terms have vanishing positive
cohomology by the explicit coinduced comparison. The genuine long exact
sequence gives the required lattice acyclicity for DUB-17's duality
route. No tensor comparison or negative Tate theory is required here.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- Actual subgroup H1/H2 vanishing of an integral p-group coefficient gives all positive internal-Hom vanishing from any original projective integral source. -/
theorem originalPGroup_internalHom_positive_zero
    {G : Type} [Group G] [Fintype G] (M B : Rep.{0} ℤ G)
    [Module.Projective ℤ M] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) (n : ℕ) :
    Limits.IsZero (groupCohomology ((Rep.ihom M).obj B) (n + 1)) := by
  letI := originalPGroup_relationKernel_projective B p hG h
  have hX := originalInternalHom_shortExact M (originalRelationShortComplex_shortExact B)
  have hmid := originalInternalHomFreeTarget_positive_zero M B n
  have hleft := originalInternalHomProjectiveTarget_positive_zero M
    (originalRelationModule B) (n + 1)
  exact (groupCohomology.mapShortComplex₃_exact hX (i := n + 1) (j := n + 2) rfl).isZero_X₂
    (hmid.eq_of_src _ _) (hleft.eq_of_tgt _ _)

/-- The same original internal Hom has vanishing positive cohomology on every subgroup; nested subgroup conditions are derived from their actual image subgroups. -/
theorem originalPGroup_internalHom_subgroup_positive_zero
    {G : Type} [Group G] [Fintype G] (M B : Rep.{0} ℤ G)
    [Module.Projective ℤ M] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2))
    (S : Subgroup G) (n : ℕ) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype ((Rep.ihom M).obj B)) (n + 1)) := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  letI : Module.Projective ℤ (Rep.res S.subtype M) := ‹Module.Projective ℤ M›
  have hS (T : Subgroup S) :
      Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res T.subtype (Rep.res S.subtype B)) 2) :=
    ⟨originalNestedSubgroup_zero B S T 1 (h _).1,
      originalNestedSubgroup_zero B S T 2 (h _).2⟩
  exact originalPGroup_internalHom_positive_zero (Rep.res S.subtype M)
    (Rep.res S.subtype B) p (hG.to_subgroup S) hS n

/-- The actual lattice internal Hom has literal invariant norm preimages, with all subgroup acyclicity inputs derived. -/
theorem originalPGroup_internalHom_norm_preimages
    {G : Type} [Group G] [Fintype G] (M B : Rep.{0} ℤ G)
    [Module.Projective ℤ M] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (h : ∀ S : Subgroup G,
      Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res S.subtype B) 2)) :
    OriginalInvariantNormSurjective ((Rep.ihom M).obj B) :=
  originalPGroup_norm_preimages_of_subgroup_first_second p hG _ (fun S =>
    ⟨originalPGroup_internalHom_subgroup_positive_zero M B p hG h S 0,
      originalPGroup_internalHom_subgroup_positive_zero M B p hG h S 1⟩)

end
end Dubon2026
