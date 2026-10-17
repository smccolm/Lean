import Dubon2026.OriginalHomologyCoinvariantGroupChange
import Dubon2026.OriginalRepresentationNormTower

/-! # Transport of literal subgroup norm-homology witnesses

The same middle coefficient witnesses the full norm of a relative trace,
and its homology class is the actual subgroup-inclusion image. This is the
finite ground-norm comparison needed to identify fixed-field norm ranges
in DUB-17's prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped BigOperators
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (S : Subgroup G) [S.Normal] [Fintype S] [Fintype (G ⧸ S)]

/-- An actual subgroup norm lift becomes a full-group norm lift of the
literal quotient trace of the invariant coefficient. -/
theorem originalSubgroup_norm_lift_trace {A B : Rep.{0} k G} (ι : A ⟶ B)
    (x : A.quotientToInvariants S) (b : B)
    (hb : (Rep.res S.subtype B).ρ.norm b = ι.hom x.val) :
    B.ρ.norm b = ι.hom (((A.quotientToInvariants S).ρ.norm x).val) := by
  rw [← originalRepresentation_norm_tower B S b]
  have hB : (((B.quotientToInvariants S).ρ.norm
      (originalSubgroupNormToInvariants B S b)).val) =
      ∑ q : G ⧸ S, B.ρ q.out ((Rep.res S.subtype B).ρ.norm b) := by
    simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro q _
    simpa only [originalSubgroupNormToInvariants, LinearMap.codRestrict_apply,
      Representation.norm, LinearMap.sum_apply] using
        originalQuotientInvariant_action_out B S q (originalSubgroupNormToInvariants B S b)
  have hA : (((A.quotientToInvariants S).ρ.norm x).val) =
      ∑ q : G ⧸ S, A.ρ q.out x.val := by
    simp only [Representation.norm, LinearMap.sum_apply, Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro q _
    exact originalQuotientInvariant_action_out A S q x
  rw [hB, hA, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [hb, Rep.hom_comm_apply]

omit [Fintype G] [Fintype S] in
/-- The literal quotient trace of a subgroup-invariant coefficient is
invariant under the full group. -/
theorem originalSubgroup_trace_invariant (A : Rep.{0} k G)
    (x : A.quotientToInvariants S) :
    (((A.quotientToInvariants S).ρ.norm x).val) ∈ A.ρ.invariants := by
  intro g
  exact congrArg Subtype.val
    (Representation.self_norm_apply (A.quotientToInvariants S).ρ
      (QuotientGroup.mk g) x)

/-- A literal subgroup norm-homology witness gives a full-group witness
for the relative trace and the actual homology inclusion image. -/
theorem originalSubgroup_norm_homology_transfer
    {Y : ShortComplex (Rep.{0} k G)}
    {P Z : Rep.{0} k G} (f : Y.X₃ ⟶ P) (g : P ⟶ Z) (hfg : f ≫ g = 0)
    (hX : (ShortComplex.mk f g hfg).ShortExact)
    (hS : ((ShortComplex.mk f g hfg).map (Rep.resFunctor S.subtype)).ShortExact)
    (x : Y.X₁.quotientToInvariants S) (b : Y.X₂)
    (hb : (Rep.res S.subtype Y.X₂).ρ.norm b = Y.f.hom x.val)
    (y : groupHomology (Rep.res S.subtype Z) 1)
    (hy : (groupHomology.H0Iso (Rep.res S.subtype Y.X₃)).hom
      (groupHomology.δ hS 1 0 rfl y) =
      Representation.Coinvariants.mk (Rep.res S.subtype Y.X₃).ρ (Y.g.hom b)) :
    Y.X₂.ρ.norm b = Y.f.hom (((Y.X₁.quotientToInvariants S).ρ.norm x).val) ∧
      (groupHomology.H0Iso Y.X₃).hom
        (groupHomology.δ hX 1 0 rfl (groupHomology.map S.subtype (𝟙 _) 1 y)) =
        Representation.Coinvariants.mk Y.X₃.ρ (Y.g.hom b) := by
  refine ⟨originalSubgroup_norm_lift_trace S Y.f x b hb, ?_⟩
  exact originalHomology_groupChange_boundary_representative S.subtype
    (𝟙 ((ShortComplex.mk f g hfg).map (Rep.resFunctor S.subtype))) hS hX y
    (Y.g.hom b) hy

end
end Dubon2026
