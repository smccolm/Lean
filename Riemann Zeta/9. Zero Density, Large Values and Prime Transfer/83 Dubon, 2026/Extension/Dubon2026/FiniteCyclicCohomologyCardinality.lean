import Dubon2026.FinitePeriodicHomologyCardinality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # Equal first and second cohomology cardinalities for actual finite cyclic modules -/

namespace Dubon2026
noncomputable section

open CategoryTheory

/-- A finite group with an actual finite coefficient module has finite
cohomology, by injecting cocycles into the finite cochain space and taking
the genuine cohomology quotient. -/
theorem finite_groupCohomology_of_finite_coefficients
    {R G : Type} [CommRing R] [Group G] [Finite G]
    (A : Rep R G) [Finite A] (n : ℕ) : Finite (groupCohomology A n) := by
  haveI : Finite ((groupCohomology.inhomogeneousCochains A).X n) := by
    change Finite ((Fin n → G) → A)
    infer_instance
  haveI : Finite (groupCohomology.cocycles A n) :=
    Finite.of_injective (groupCohomology.iCocycles A n)
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Finite.of_surjective (groupCohomology.π A n)
    (fun x => groupCohomology_induction_on x (fun c => ⟨c, rfl⟩))

/-- The two actual positive cohomology groups of a finite cyclic module
have equal cardinality. The proof counts the two homologies of the genuine
norm-minus-generator periodic resolution, without assuming a Herbrand quotient. -/
theorem finite_cyclic_first_second_cohomology_card_eq
    {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
    (A : Rep R G) [Finite A] (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (groupCohomology A 1) = Nat.card (groupCohomology A 2) := by
  let f := (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap
  let z := A.norm.hom.toLinearMap
  have hzf : z.comp f = 0 := by
    ext x
    exact (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCat_zero_apply x
  have hfz : f.comp z = 0 := by
    ext x
    exact (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCat_zero_apply x
  have h1 : Nat.card (groupCohomology A 1) =
      Nat.card (linearPeriodicHomology f z hzf) := by
    exact Nat.card_congr
      ((Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by decide) ≪≫
        (Rep.FiniteCyclicGroup.subCompNormHom A g).moduleCatHomologyIso).toLinearEquiv.toEquiv)
  have h2 : Nat.card (groupCohomology A 2) =
      Nat.card (linearPeriodicHomology z f hfz) := by
    exact Nat.card_congr
      ((Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 (by decide) ≪≫
        (Rep.FiniteCyclicGroup.normHomCompSub A g).moduleCatHomologyIso).toLinearEquiv.toEquiv)
  rw [h1, h2]
  exact finite_periodic_homology_card_eq f z hzf hfz

end
end Dubon2026
