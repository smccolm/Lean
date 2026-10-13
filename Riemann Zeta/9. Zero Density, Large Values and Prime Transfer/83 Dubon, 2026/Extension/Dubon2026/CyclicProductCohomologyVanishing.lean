import Dubon2026.FiniteProductCohomology
import Dubon2026.CyclicPositiveCohomologyVanishing

/-! # Original cyclic cohomology vanishing for products of local factors

For an arbitrary family, the original finite-group norm is coordinatewise.
The existing periodic cohomology projections and coordinatewise choices
of actual norm or coboundary preimages prove positive-degree vanishing
for the product. No general infinite-product cohomology theory is needed.
This is the exact assembly needed for DUB-17's outside-support local factors.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
variable {R G ι : Type} [CommRing R] [CommGroup G] [Fintype G]
  (A : ι → Rep R G)

/-- The actual finite-group norm of the original product representation is coordinatewise. -/
theorem originalPiRep_norm_apply (x : ∀ i, A i) (i : ι) :
    (originalPiRep A).norm.hom x i = (A i).norm.hom (x i) := by
  let p : originalPiRep A ⟶ A i := Rep.ofHom ⟨LinearMap.proj i, by intro g; rfl⟩
  exact (congrArg (fun f : originalPiRep A ⟶ A i => f.hom x) (Rep.norm_comm p)).symm

/-- Vanishing of the original positive cyclic cohomology of every factor implies vanishing for the actual arbitrary product. -/
theorem cyclic_originalPi_cohomology_zero
    (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (n : ℕ) (hn : 0 < n)
    (hzero : ∀ i, Limits.IsZero (groupCohomology (A i) n)) :
    Limits.IsZero (groupCohomology (originalPiRep A) n) := by
  letI (i : ι) : Subsingleton (groupCohomology (A i) n) :=
    ModuleCat.isZero_iff_subsingleton.mp (hzero i)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply subsingleton_of_forall_eq 0
  intro x
  rcases Nat.even_or_odd n with he | ho
  · letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    let π := Rep.FiniteCyclicGroup.groupCohomologyπEven (originalPiRep A) g hg n he
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance x
    apply (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
      (originalPiRep A) g hg n he y).mpr
    have hy : (originalPiRep A).ρ g y.val - y.val = 0 := y.property
    have hcoords (i : ι) : ∃ z : A i, (A i).norm.hom z = y.val i := by
      let yi : LinearMap.ker (Rep.applyAsHom (A i) g - 𝟙 (A i)).hom.toLinearMap :=
        ⟨y.val i, congrFun hy i⟩
      exact (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
        (A i) g hg n he yi).mp (Subsingleton.elim _ _)
    choose z hz using hcoords
    refine ⟨z, ?_⟩
    funext i
    exact (originalPiRep_norm_apply A z i).trans (hz i)
  · let π := Rep.FiniteCyclicGroup.groupCohomologyπOdd (originalPiRep A) g hg n ho
    obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance x
    apply (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff
      (originalPiRep A) g hg n ho y).mpr
    have hy : (originalPiRep A).norm.hom y.val = 0 := y.property
    have hcoords (i : ι) : ∃ z : A i, (A i).ρ g z - z = y.val i := by
      have hi : (A i).norm.hom (y.val i) = 0 := by
        rw [← originalPiRep_norm_apply]
        exact congrFun hy i
      let yi : LinearMap.ker (A i).norm.hom.toLinearMap := ⟨y.val i, hi⟩
      exact (Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff
        (A i) g hg n ho yi).mp (Subsingleton.elim _ _)
    choose z hz using hcoords
    refine ⟨z, ?_⟩
    funext i
    exact hz i

end
end Dubon2026
