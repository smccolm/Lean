import Dubon2026.OriginalCoinducedSubgroupRetract
import Dubon2026.OriginalAugmentationSequence
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # The actual regular coefficient has no positive subgroup cohomology

The original regular representation is identified with original
coinduced functions by the inverse group coordinate. Existing Shapiro
and subgroup-retraction proofs then supply the two vanishing inputs
needed to calculate the augmentation ideal on DUB-17's duality route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] [Finite G]

/-- The literal regular representation is original coinduction of the trivial coefficient. -/
def originalRegularCoinducedIso :
    Rep.leftRegular k G ≅ originalCoinducedFunctionRep (Rep.trivial k G k) :=
  Rep.mkIso {
    toFun := fun f => originalCoinducedFunction _ (fun g => f g⁻¹)
    invFun := fun f => Finsupp.equivFunOnFinite.symm (fun g => f.val g⁻¹)
    left_inv f := by ext g; simp [originalCoinducedFunction]
    right_inv f := by apply Subtype.ext; funext g; simp [originalCoinducedFunction]
    map_add' f h := by apply Subtype.ext; rfl
    map_smul' r f := by apply Subtype.ext; rfl
    isIntertwining' h := by
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      funext g
      change ((Representation.leftRegular k G h) f) g⁻¹ = f (g * h)⁻¹
      simpa only [Representation.leftRegular, Representation.ofMulAction,
        Finsupp.lmapDomain_apply, mul_inv_rev] using
          Finsupp.mapDomain_equiv_apply (f := Equiv.mulLeft h) f g⁻¹ }

/-- Every original subgroup has vanishing positive cohomology of the actual regular coefficient. -/
theorem originalRegularSubgroup_positive_zero (S : Subgroup G) (n : ℕ) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (Rep.leftRegular k G)) (n + 1)) :=
  (originalCoinducedSubgroup_positive_zero (Rep.trivial k G k) S n).of_iso
    ((groupCohomology.functor k S (n + 1)).mapIso
      ((Rep.resFunctor S.subtype).mapIso originalRegularCoinducedIso))

end
end Dubon2026
