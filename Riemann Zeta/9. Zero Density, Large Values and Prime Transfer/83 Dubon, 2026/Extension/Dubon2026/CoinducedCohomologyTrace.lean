import Dubon2026.CoinducedCosetTrace
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Actual subgroup cohomology comparison and its coset-index trace -/

namespace Dubon2026
noncomputable section

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G)

/-- The original cohomology functor preserves sums because the actual
cochain functor and actual homology maps preserve sums. -/
instance originalCohomologyFunctorAdditive (n : ℕ) :
    (groupCohomology.functor k G n).Additive where
  map_add {X Y} f g := by
    change HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor k G).map (f + g)) n =
      HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor k G).map f) n +
        HomologicalComplex.homologyMap ((groupCohomology.cochainsFunctor k G).map g) n
    rw [Functor.map_add, HomologicalComplex.homologyMap_add]

/-- Map original cohomology along the genuine restriction-coinduction unit,
then apply the pinned Shapiro isomorphism to the original subgroup action. -/
def subgroupCohomologyComparison (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology (Rep.res S.subtype A) n :=
  (groupCohomology.functor k G n).map
      (Rep.resCoindToHom S.subtype A (Rep.res S.subtype A) (𝟙 _)) ≫
    (groupCohomology.coindIso (Rep.res S.subtype A) n).hom

variable [Fintype (G ⧸ S)]

/-- Transport the actual coset trace through the inverse of the same
Shapiro isomorphism. -/
def subgroupCohomologyTrace (n : ℕ) :
    groupCohomology (Rep.res S.subtype A) n ⟶ groupCohomology A n :=
  (groupCohomology.coindIso (Rep.res S.subtype A) n).inv ≫
    (groupCohomology.functor k G n).map (coinducedCosetTrace A S)

/-- The actual comparison followed by trace is precisely multiplication
by the number of original subgroup cosets in every cohomology degree. -/
theorem subgroupCohomologyComparison_trace (n : ℕ) :
    subgroupCohomologyComparison A S n ≫ subgroupCohomologyTrace A S n =
      Fintype.card (G ⧸ S) • 𝟙 (groupCohomology A n) := by
  unfold subgroupCohomologyComparison subgroupCohomologyTrace
  erw [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp,
    coinducedCosetTrace_comp_unit, Functor.map_nsmul,
    (groupCohomology.functor k G n).map_id A]
  rfl

/-- Vanishing under the actual subgroup comparison forces the coset index
to annihilate the original cohomology class. -/
theorem subgroupCohomologyComparison_kernel_annihilated (n : ℕ)
    (x : groupCohomology A n) (hx : subgroupCohomologyComparison A S n x = 0) :
    Fintype.card (G ⧸ S) • x = 0 := by
  have h := congrArg (fun f : groupCohomology A n ⟶ groupCohomology A n => f x)
    (subgroupCohomologyComparison_trace A S n)
  change subgroupCohomologyTrace A S n (subgroupCohomologyComparison A S n x) =
    Fintype.card (G ⧸ S) • x at h
  rw [hx, map_zero] at h
  exact h.symm

end
end Dubon2026
