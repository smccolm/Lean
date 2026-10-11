import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Ring

/-! # The actual difference-from-one map on the original small-unit quotient -/

namespace Dubon2026
noncomputable section

variable {R L : Type} [CommRing R] [Field L] [Algebra R L]
  (A B : Submodule R L) (U : Subgroup Lˣ)
  (hU : ∀ u : Lˣ, u ∈ U ↔ (u : L) - 1 ∈ A)

/-- The original unit minus one, retained as an element of its actual lattice. -/
def smallUnitDifference (u : Additive U) : A :=
  ⟨(((Additive.toMul u : U) : Lˣ) : L) - 1,
    (hU _).mp (Additive.toMul u).property⟩

/-- The original difference-from-one map becomes additive in the actual
lattice quotient because its literal product error belongs to the smaller lattice. -/
def smallUnitGradedMap
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ B) :
    Additive U →+ A ⧸ B.comap A.subtype where
  toFun u := (B.comap A.subtype).mkQ (smallUnitDifference A U hU u)
  map_zero' := by
    have hz : smallUnitDifference A U hU 0 = 0 := by
      apply Subtype.ext
      exact sub_self (1 : L)
    rw [hz, map_zero]
  map_add' u v := by
    let du := smallUnitDifference A U hU u
    let dv := smallUnitDifference A U hU v
    have he : smallUnitDifference A U hU (u + v) - (du + dv) ∈ B.comap A.subtype := by
      change (((((Additive.toMul u : U) : Lˣ) : L) *
          (((Additive.toMul v : U) : Lˣ) : L) - 1) -
        (((((Additive.toMul u : U) : Lˣ) : L) - 1) +
          ((((Additive.toMul v : U) : Lˣ) : L) - 1))) ∈ B
      have h := hmul (du : L) du.property (dv : L) dv.property
      convert h using 1
      dsimp [du, dv, smallUnitDifference]
      ring
    change (B.comap A.subtype).mkQ (smallUnitDifference A U hU (u + v)) =
      (B.comap A.subtype).mkQ du + (B.comap A.subtype).mkQ dv
    rw [← map_add]
    exact (Submodule.Quotient.eq _).mpr he

/-- The kernel is exactly the original units whose literal difference from
one lies in the displayed smaller lattice. -/
theorem smallUnitGradedMap_eq_zero_iff
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ B) (u : Additive U) :
    smallUnitGradedMap A B U hU hmul u = 0 ↔
      (((Additive.toMul u : U) : Lˣ) : L) - 1 ∈ B := by
  change (Submodule.Quotient.mk (smallUnitDifference A U hU u) :
    A ⧸ B.comap A.subtype) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero (B.comap A.subtype)

/-- Every original lattice class has the genuine original unit `1+a` as a
preimage. Nonvanishing is the explicit local small-lattice input. -/
theorem smallUnitGradedMap_surjective
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ B)
    (hunit : ∀ a ∈ A, (1 : L) + a ≠ 0) :
    Function.Surjective (smallUnitGradedMap A B U hU hmul) := by
  intro q
  obtain ⟨a, rfl⟩ := (B.comap A.subtype).mkQ_surjective q
  let v : Lˣ := Units.mk0 (1 + (a : L)) (hunit a a.property)
  have hv : v ∈ U := by
    apply (hU v).mpr
    change (1 + (a : L)) - 1 ∈ A
    simpa only [add_sub_cancel_left] using a.property
  let u : U := ⟨v, hv⟩
  refine ⟨Additive.ofMul u, ?_⟩
  have hd : smallUnitDifference A U hU (Additive.ofMul u) = a := by
    apply Subtype.ext
    change (1 + (a : L)) - 1 = (a : L)
    exact add_sub_cancel_left 1 (a : L)
  change (B.comap A.subtype).mkQ (smallUnitDifference A U hU (Additive.ofMul u)) = _
  rw [hd]

/-- The genuine original small-unit quotient is the actual additive lattice
quotient, via the proved literal difference map and its computed kernel. -/
def smallUnitGradedQuotientEquiv
    (hmul : ∀ x ∈ A, ∀ y ∈ A, x * y ∈ B)
    (hunit : ∀ a ∈ A, (1 : L) + a ≠ 0) :
    Additive U ⧸ (smallUnitGradedMap A B U hU hmul).ker ≃+
      A ⧸ B.comap A.subtype :=
  QuotientAddGroup.quotientKerEquivOfSurjective _
    (smallUnitGradedMap_surjective A B U hU hmul hunit)

end
end Dubon2026
