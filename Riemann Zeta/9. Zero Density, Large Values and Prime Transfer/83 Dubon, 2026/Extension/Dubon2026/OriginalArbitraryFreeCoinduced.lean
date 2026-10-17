import Dubon2026.OriginalCoinducedSubgroupRetract
import Dubon2026.OriginalRelationModuleSequence

/-! # The actual free cover with an arbitrary coefficient index

The fundamental arithmetic coefficient is infinite. Its literal free
cover therefore cannot use the earlier finite-index relation lemma.
Finite group-coordinate sums identify this actual free representation
with original coinduced functions, without assuming a finite index set.
This is the first required input to its kernel presentation on DUB-17's
lattice/internal-Hom duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G] (α : Type)

/-- Actual free coefficients, even with infinite index, are original coinduced finitely supported coordinates. -/
def originalArbitraryFreeCoinducedIso :
    Rep.free k G α ≅ originalCoinducedFunctionRep (Rep.trivial k G (α →₀ k)) := by
  classical
  exact Rep.mkIso {
    toFun := fun f => originalCoinducedFunction _
      (fun g => Finsupp.mapRange (fun v : G →₀ k => v g⁻¹) rfl f)
    invFun := fun f => ∑ g : G,
      Finsupp.mapRange (Finsupp.single g) (Finsupp.single_zero g) (f.val g⁻¹)
    left_inv f := by
      ext a g
      simp only [originalCoinducedFunction]
      simp
    right_inv f := by
      apply Subtype.ext
      funext g
      ext a
      simp only [originalCoinducedFunction, Finsupp.mapRange_apply]
      simp [Finsupp.single_apply]
    map_add' f h := by
      apply Subtype.ext
      funext g
      ext a
      rfl
    map_smul' r f := by
      apply Subtype.ext
      funext g
      ext a
      rfl
    isIntertwining' h := by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext g
      ext a
      change ((Representation.free k G α h) f) a g⁻¹ = f a (g * h)⁻¹
      simp [Representation.free, Representation.finsupp_apply,
        Representation.leftRegular, Representation.ofMulAction, Finsupp.lsum_apply,
        mul_inv_rev]
      rw [Finsupp.sum_eq_single a]
      · rw [Finsupp.single_eq_same]
        exact Finsupp.mapDomain_equiv_apply (f := Equiv.mulLeft h) (f a) g⁻¹
      · intro b _ hba
        simp [hba]
      · intro _
        simp }

/-- The actual arbitrary-index free cover has vanishing positive cohomology on every original subgroup. -/
theorem originalArbitraryFree_subgroup_positive_zero (S : Subgroup G) (n : ℕ) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.free k G α)) (n + 1)) :=
  (originalCoinducedSubgroup_positive_zero (Rep.trivial k G (α →₀ k)) S n).of_iso
    ((groupCohomology.functor k S (n + 1)).mapIso
      ((Rep.resFunctor S.subtype).mapIso (originalArbitraryFreeCoinducedIso α)))

end
end Dubon2026
