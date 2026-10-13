import Dubon2026.NormedFieldSmallUnitBalls
import Dubon2026.SmallUnitGradedQuotient
import Mathlib.GroupTheory.Index

/-! # Original small-unit indices as additive ball quotient cardinalities

The existing difference-from-one quotient supplies the numerical local power
index needed by DUB-17. The product error bound is proved from the actual
ultrametric balls rather than supplied as a local arithmetic hypothesis.
-/

namespace Dubon2026
noncomputable section
open Metric

variable (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K]

/-- The actual additive closed ball at zero as its canonical integer module. -/
def normedFieldBallModule (s : ℝ) (hs : 0 < s) : Submodule ℤ K :=
  (IsUltrametricDist.closedBall_openAddSubgroup K hs).toAddSubgroup.toIntSubmodule

/-- Membership in the actual ball module is precisely the original norm bound. -/
theorem normedFieldBallModule_mem (s : ℝ) (hs : 0 < s) (x : K) :
    x ∈ normedFieldBallModule K s hs ↔ ‖x‖ ≤ s := by
  change dist x 0 ≤ s ↔ ‖x‖ ≤ s
  rw [dist_zero_right]

variable (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (hs1 : s < 1)
  (hmul : s * s ≤ t)

private theorem ballUnitMembership (u : Kˣ) :
    u ∈ normedFieldSmallUnitSubgroup K s hs.le hs1 ↔
      (u : K) - 1 ∈ normedFieldBallModule K s hs :=
  (normedFieldBallModule_mem K s hs ((u : K) - 1)).symm

private theorem ballProduct (hprod : s * s ≤ t) :
    ∀ x ∈ normedFieldBallModule K s hs, ∀ y ∈ normedFieldBallModule K s hs,
      x * y ∈ normedFieldBallModule K t ht := by
  intro x hx y hy
  apply (normedFieldBallModule_mem K t ht _).mpr
  rw [norm_mul]
  exact (mul_le_mul ((normedFieldBallModule_mem K s hs x).mp hx)
    ((normedFieldBallModule_mem K s hs y).mp hy) (norm_nonneg _) hs.le).trans hprod

/-- The actual original difference-from-one homomorphism to the smaller
additive ball quotient. -/
def normedFieldSmallUnitDifferenceMap :
    normedFieldSmallUnitSubgroup K s hs.le hs1 →*
      Multiplicative (normedFieldBallModule K s hs ⧸
        (normedFieldBallModule K t ht).comap (normedFieldBallModule K s hs).subtype) :=
  (smallUnitGradedMap (normedFieldBallModule K s hs) (normedFieldBallModule K t ht)
    (normedFieldSmallUnitSubgroup K s hs.le hs1) (ballUnitMembership K s hs hs1)
    (ballProduct K s t hs ht hmul)).toMultiplicative

/-- The exact kernel is the original unit difference lying in the smaller
ball, with no condition on an arbitrary replacement representative. -/
theorem normedFieldSmallUnitDifferenceMap_eq_one_iff
    (u : normedFieldSmallUnitSubgroup K s hs.le hs1) :
    normedFieldSmallUnitDifferenceMap K s t hs ht hs1 hmul u = 1 ↔
      ‖((u : Kˣ) : K) - 1‖ ≤ t := by
  change smallUnitGradedMap _ _ _ (ballUnitMembership K s hs hs1)
    (ballProduct K s t hs ht hmul) (Additive.ofMul u) = 0 ↔ _
  rw [smallUnitGradedMap_eq_zero_iff]
  exact normedFieldBallModule_mem K t ht _

/-- Actual one-plus-ball elements prove surjectivity of the original
unit-difference map. -/
theorem normedFieldSmallUnitDifferenceMap_surjective :
    Function.Surjective (normedFieldSmallUnitDifferenceMap K s t hs ht hs1 hmul) := by
  change Function.Surjective (smallUnitGradedMap _ _ _ (ballUnitMembership K s hs hs1)
    (ballProduct K s t hs ht hmul)).toMultiplicative
  apply smallUnitGradedMap_surjective _ _ _ (ballUnitMembership K s hs hs1)
    (ballProduct K s t hs ht hmul)
  intro a ha
  have hna : ‖a‖ < 1 := ((normedFieldBallModule_mem K s hs a).mp ha).trans_lt hs1
  intro hz
  have hae : a = -1 := eq_neg_of_add_eq_zero_right hz
  rw [hae, norm_neg, norm_one] at hna
  exact lt_irrefl _ hna

include hmul in
/-- The original unit-ball relative index is the exact additive ball
quotient cardinality. -/
theorem normedFieldSmallUnit_relativeIndex (ht1 : t < 1) :
    (normedFieldSmallUnitSubgroup K t ht.le ht1).relIndex
      (normedFieldSmallUnitSubgroup K s hs.le hs1) =
      Nat.card (normedFieldBallModule K s hs ⧸
        (normedFieldBallModule K t ht).comap (normedFieldBallModule K s hs).subtype) := by
  let f := normedFieldSmallUnitDifferenceMap K s t hs ht hs1 hmul
  have hk : f.ker = (normedFieldSmallUnitSubgroup K t ht.le ht1).subgroupOf
      (normedFieldSmallUnitSubgroup K s hs.le hs1) := by
    ext u
    exact normedFieldSmallUnitDifferenceMap_eq_one_iff K s t hs ht hs1 hmul u
  change Nat.card (_ ⧸ _) = _
  rw [← hk]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
    (normedFieldSmallUnitDifferenceMap_surjective K s t hs ht hs1 hmul)).toEquiv

end
end Dubon2026
