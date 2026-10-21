import Dubon2026.SourceHeckeCohomologyTrace
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! Native H1 restriction followed by the original finite coset trace.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> level raising from Q to Q*p -> injectivity of restriction. The exact
degree-one correction is computed using the original cocycle and cosets,
so the composite is multiplication by the genuine subgroup index.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory

variable {R G : Type} [CommRing R] [Group G] (A : Rep R G) (S : Subgroup G)

/-- Restriction to the actual subgroup on full native H1. -/
def sourceH1SubgroupRestriction :
    groupCohomology.H1 A →ₗ[R] groupCohomology.H1 (restrictedCoefficientRep A S.subtype) :=
  (groupCohomology.map S.subtype (𝟙 _) 1).hom

/-- Actual restriction is represented by the literal restricted native cocycle. -/
theorem sourceH1SubgroupRestriction_cocycle (c : groupCohomology.cocycles₁ A) :
    sourceH1SubgroupRestriction A S (groupCohomology.H1π A c) =
      groupCohomology.H1π _ (groupCohomology.mapCocycles₁ S.subtype (𝟙 _) c) :=
  groupCohomology.H1π_comp_map_apply S.subtype (𝟙 _) c

variable [Fintype (G ⧸ S)]

/-- The full trace of a restricted native cocycle differs from its coset
cardinality multiple by the explicit coboundary of the sum of original
coset values. -/
theorem sourceH1RestrictionTrace_cocycle (c : groupCohomology.cocycles₁ A) :
    cosetTraceOne A S (fun s : S => c s.val) -
        (Fintype.card (G ⧸ S) : R) • (c : G → A) =
      groupCohomology.d₀₁ A (∑ q : G ⧸ S, c q.out) := by
  have hc := (groupCohomology.mem_cocycles₁_iff _).mp c.property
  have hterm (g : G) (q : G ⧸ S) :
      A.ρ (g • q).out (c (cosetTransition S g q)) =
        c g + A.ρ g (c q.out) - c (g • q).out := by
    have h := hc (g • q).out (cosetTransition S g q)
    rw [cosetTransition_factor, hc g q.out] at h
    change A.ρ g (c q.out) + c g =
      A.ρ (g • q).out (c (cosetTransition S g q)) + c (g • q).out at h
    rw [add_comm (A.ρ g (c q.out))] at h
    exact eq_sub_of_add_eq h.symm
  funext g
  change (∑ q : G ⧸ S, A.ρ (g • q).out (c (cosetTransition S g q))) -
    (Fintype.card (G ⧸ S) : R) • c g =
      A.ρ g (∑ q : G ⧸ S, c q.out) - ∑ q : G ⧸ S, c q.out
  simp_rw [hterm]
  have hreindex : (∑ q : G ⧸ S, c (g • q).out) = ∑ q : G ⧸ S, c q.out :=
    Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ S => c q.out)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ← map_sum, hreindex, Nat.cast_smul_eq_nsmul]
  abel

/-- On full native H1, the actual trace after restriction is multiplication
by the number of genuine subgroup cosets. -/
theorem sourceH1RestrictionTrace (x : groupCohomology.H1 A) :
    sourceHeckeH1Trace A S (sourceH1SubgroupRestriction A S x) =
      (Fintype.card (G ⧸ S) : R) • x := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  rw [sourceH1SubgroupRestriction_cocycle, sourceHeckeH1Trace_cocycle, ← map_smul]
  apply (groupCohomology.H1π_eq_iff _ _).mpr
  refine ⟨∑ q : G ⧸ S, c q.out, ?_⟩
  exact (sourceH1RestrictionTrace_cocycle A S c).symm

/-- A subgroup of invertible index has injective restriction on the actual
native H1, with the original finite trace proving the claim. -/
theorem sourceH1SubgroupRestriction_injective
    (hcard : IsUnit (Fintype.card (G ⧸ S) : R)) :
    Function.Injective (sourceH1SubgroupRestriction A S) := by
  intro x y h
  have he := congrArg (sourceHeckeH1Trace A S) h
  rw [sourceH1RestrictionTrace, sourceH1RestrictionTrace] at he
  exact hcard.smul_left_cancel.mp he

end
end Dubon2026
