import Dubon2026.SourceCurveDivisorPullback
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! DUB-17/18 -> Weil reciprocity and Hecke adjointness -> evaluation
on pulled-back divisors. Expand the existing ramification-weighted divisor
over its actual disjoint finite fibers. The subsequent original consumer
supplies the proved field-norm evaluation, with no abstract pairing input. -/
namespace Dubon2026.SourceCurve.Divisor
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem finitePullback_prod_zpow (D : Divisor K F) (a : Place K E → K) :
    (finitePullback E D).prod (fun w n => a w ^ n) =
      ∏ v ∈ D.support,
        (∏ᶠ w : {w : Place K E // w.restrict F = v},
          a w.val ^ (w.val.ord (algebraMap F E v.uniformizer)).toNat) ^ D v := by
  classical
  have hs : (finitePullback E D).support ⊆ D.support.biUnion (fun v => v.restrictionFiber E) := by
    intro w hw
    have hd : D (w.restrict F) ≠ 0 := by
      intro hz
      apply Finsupp.mem_support_iff.mp hw
      rw [finitePullback_apply, hz, zero_mul]
    exact Finset.mem_biUnion.mpr ⟨w.restrict F, Finsupp.mem_support_iff.mpr hd,
      Place.mem_restrictionFiber.mpr rfl⟩
  have hdisj : Set.PairwiseDisjoint (D.support : Set (Place K F))
      (fun v => v.restrictionFiber E) := by
    intro v _ u _ hne
    apply Finset.disjoint_left.mpr
    intro w hv hu
    exact hne ((Place.mem_restrictionFiber.mp hv).symm.trans (Place.mem_restrictionFiber.mp hu))
  rw [Finsupp.prod_of_support_subset _ hs _ (fun _ _ => zpow_zero _), Finset.prod_biUnion hdisj]
  apply Finset.prod_congr rfl
  intro v _
  have hfiber : (∏ᶠ w : {w : Place K E // w.restrict F = v},
      a w.val ^ (w.val.ord (algebraMap F E v.uniformizer)).toNat) =
      ∏ w ∈ v.restrictionFiber E, a w ^ (w.ord (algebraMap F E v.uniformizer)).toNat := by
    rw [finprod_subtype_eq_finprod_cond (f := fun w : Place K E =>
      a w ^ (w.ord (algebraMap F E v.uniformizer)).toNat)]
    exact finprod_cond_eq_prod_of_cond_iff _ (fun _ => Place.mem_restrictionFiber.symm)
  rw [hfiber, ← Finset.prod_zpow]
  apply Finset.prod_congr rfl
  intro w hw
  have he := w.ord_restricted_uniformizer_pos (F := F)
  have hr := Place.mem_restrictionFiber.mp hw
  rw [hr] at he
  rw [finitePullback_apply, hr, ← zpow_natCast, Int.toNat_of_nonneg he.le,
    ← zpow_mul, mul_comm]

end
end Dubon2026.SourceCurve.Divisor
