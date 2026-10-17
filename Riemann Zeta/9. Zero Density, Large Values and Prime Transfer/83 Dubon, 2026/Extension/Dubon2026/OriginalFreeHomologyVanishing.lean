import Dubon2026.OriginalArbitraryFreeCoinduced
import Mathlib.RepresentationTheory.FiniteIndex
import Mathlib.RepresentationTheory.Homological.GroupHomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-! # Homology vanishing of the actual arbitrary free cover

Pinned finite-index induction/coinduction and homological Shapiro give
positive homology vanishing without a new bar contraction. This serves
DUB-17's actual relation presentation and integral projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- The actual coinduced original coefficient has zero positive homology, by pinned Shapiro for the trivial subgroup. -/
theorem originalCoinduced_positive_homology_zero
    {k G : Type} [CommRing k] [Group G] [Fintype G] (A : Rep.{0} k G) (n : ℕ) :
    Limits.IsZero (groupHomology (originalCoinducedFunctionRep A) (n + 1)) := by
  classical
  let B := Rep.res (⊥ : Subgroup G).subtype A
  have hz := isZero_groupHomology_succ_of_subsingleton B n
  have hi := groupHomology.indIso (⊥ : Subgroup G) B (n + 1)
  exact (hz.of_iso hi).of_iso
    ((groupHomology.functor k G (n + 1)).mapIso (Rep.indCoindIso B)).symm

/-- The actual arbitrary-index free cover has zero positive homology. -/
theorem originalArbitraryFree_positive_homology_zero
    {k G : Type} [CommRing k] [Group G] [Fintype G] (α : Type) (n : ℕ) :
    Limits.IsZero (groupHomology (Rep.free k G α) (n + 1)) :=
  (originalCoinduced_positive_homology_zero (Rep.trivial k G (α →₀ k)) n).of_iso
    ((groupHomology.functor k G (n + 1)).mapIso (originalArbitraryFreeCoinducedIso α))

end
end Dubon2026
