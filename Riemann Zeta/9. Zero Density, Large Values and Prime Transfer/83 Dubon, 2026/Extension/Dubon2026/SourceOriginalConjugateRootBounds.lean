import Dubon2026.SourceUniqueCommonRootDescent

/-! DUB-17/18 -> numerical modular genus -> all-level generation ->
uniqueness of the common root of the lower minimal polynomial and the
prime relation. The proved lower conjugate product forces the top
Laurent exponent to have trivial phase, and excludes the larger
distinguished branch. These are the two concrete uniqueness conditions
needed for descent of the actual preceding j-substitution.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux
variable {K : Type*} [Field K] [Algebra ℚ K]

theorem original_lower_product_root_shape (M p : ℕ) [NeZero M] [NeZero p]
    (η : Kˣ) (hP : expandedJMinpoly K M M = slotProduct M η)
    (y : LaurentSeries K) (hy : (expandedJMinpoly K (M * p) M).IsRoot y) :
    ∃ s ∈ indices M, y = qExpand K p (slotValue η s.1 s.2) := by
  apply expanded_minpoly_root_shape_of_identity p M η hP y
  simpa only [Nat.mul_comm p M] using hy

theorem original_lower_root_top_twist_eq_one (M p : ℕ) [NeZero M] [NeZero p]
    (η : Kˣ) (hP : expandedJMinpoly K M M = slotProduct M η)
    (y : LaurentSeries K) (hy : (expandedJMinpoly K (M * p) M).IsRoot y)
    (w : Kˣ) (he : y = TS K (M * p * M) w) : w = 1 := by
  obtain ⟨⟨a, b⟩, hs, hshape⟩ := original_lower_product_root_shape M p η hP y hy
  haveI : NeZero a := ⟨index_fst_ne_zero hs⟩
  rw [slotValue_eq, qExpand_TS] at hshape
  obtain ⟨hexp, hunit⟩ := TS_injective (he.symm.trans hshape)
  have hsq : M * M = a * a := Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (NeZero.ne p)) (by calc
      p * (M * M) = M * p * M := by ring
      _ = p * (a * a) := hexp)
  have ha : a = M := (Nat.mul_self_inj.mp hsq).symm
  subst a
  have hb := ((mem_indices M M b).mp hs).2.2.1
  rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne M))] at hb
  have hb0 : b = 0 := by omega
  simpa only [hb0, zero_mul, pow_zero] using hunit

theorem original_lower_root_ne_larger_branch (M p : ℕ) [NeZero M] [hp : Fact p.Prime]
    (η : Kˣ) (hP : expandedJMinpoly K M M = slotProduct M η)
    (y : LaurentSeries K) (hy : (expandedJMinpoly K (M * p) M).IsRoot y) :
    y ≠ TS K ((M * p) * (M * p * p)) 1 := by
  intro he
  obtain ⟨⟨a, b⟩, hs, hshape⟩ := original_lower_product_root_shape M p η hP y hy
  haveI : NeZero a := ⟨index_fst_ne_zero hs⟩
  rw [slotValue_eq, qExpand_TS] at hshape
  have hexp := (TS_injective (he.symm.trans hshape)).1
  have hsq : (M * p) * (M * p) = a * a := Nat.eq_of_mul_eq_mul_left hp.out.pos
    (by calc
      p * ((M * p) * (M * p)) = (M * p) * (M * p * p) := by ring
      _ = p * (a * a) := hexp)
  have ha : M * p = a := Nat.mul_self_inj.mp hsq
  have hle : a ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M))
    ((mem_indices M a b).mp hs).1
  have hlt : M < M * p := lt_mul_of_one_lt_right
    (Nat.pos_of_ne_zero (NeZero.ne M)) hp.out.one_lt
  omega

end
end Dubon2026.SourceFunctionField
