import Dubon2026.SourceCurveDivisors

/-! DUB-17/18 -> modular good reduction -> principal-divisor pushforward ->
equality of total chart orders. Finite support from existing principal-divisor
existence makes the restricted order sums precise and proves their product
laws. The same sums will compare an integral function with its integral
cofactor and reduce the comparison to normalized coordinate factors.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_RegularProlongation_sum_ord_eq_sum_ord_residue_of_isIntegral_adjoin. -/
namespace Dubon2026.SourceCurve
noncomputable section
open scoped Classical

section Zsum

variable (K : Type*) {F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]

/-- The literal finite order divisor supplied by principal-divisor existence. -/
def principalOrderDivisor (u : F) : Divisor K F :=
  if hu : u = 0 then 0 else (HasPrincipalDivisors.exists_divisor u hu).choose

variable {K}

theorem principalOrderDivisor_apply (u : F) (P : Place K F) : principalOrderDivisor K u P = P.ord u := by
  unfold principalOrderDivisor
  split_ifs with hu
  · subst hu
    simp
  · exact (HasPrincipalDivisors.exists_divisor u hu).choose_spec.1 P

theorem mem_support_principalOrderDivisor {u : F} {P : Place K F} : P ∈ (principalOrderDivisor K u).support ↔ P.ord u ≠ 0 := by
  rw [Finsupp.mem_support_iff, principalOrderDivisor_apply]

/-- The sum of literal function orders over the specified chart domain. -/
def chartOrderSum (I : Place K F → Prop) (u : F) : ℤ :=
  ∑ P ∈ (principalOrderDivisor K u).support.filter I, P.ord u

theorem chartOrderSum_eq_sum_filter (I : Place K F → Prop) (u : F) (S : Finset (Place K F))
    (hS : ∀ P, I P → P.ord u ≠ 0 → P ∈ S) :
    chartOrderSum I u = ∑ P ∈ S.filter I, P.ord u := by
  unfold chartOrderSum
  apply Finset.sum_subset
  · intro P hP
    rw [Finset.mem_filter] at hP ⊢
    exact ⟨hS P hP.2 (mem_support_principalOrderDivisor.mp hP.1), hP.2⟩
  · intro P hPS hPn
    rw [Finset.mem_filter] at hPS hPn
    by_contra h
    exact hPn ⟨mem_support_principalOrderDivisor.mpr h, hPS.2⟩

theorem chartOrderSum_eq_sum (I : Place K F → Prop) (u : F) (T : Finset (Place K F))
    (hT : ∀ P, P ∈ T ↔ (P.ord u ≠ 0 ∧ I P)) : chartOrderSum I u = ∑ P ∈ T, P.ord u := by
  unfold chartOrderSum
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext P
  rw [Finset.mem_filter, mem_support_principalOrderDivisor, hT]

theorem chartOrderSum_mul (I : Place K F → Prop) {u w : F} (hu : u ≠ 0) (hw : w ≠ 0) :
    chartOrderSum I (u * w) = chartOrderSum I u + chartOrderSum I w := by
  set S : Finset (Place K F) :=
    (principalOrderDivisor K (u * w)).support ∪ (principalOrderDivisor K u).support ∪ (principalOrderDivisor K w).support with hS
  have h1 : chartOrderSum I (u * w) = ∑ P ∈ S.filter I, P.ord (u * w) :=
    chartOrderSum_eq_sum_filter I (u * w) S fun P _ h =>
      Finset.mem_union_left _ (Finset.mem_union_left _ (mem_support_principalOrderDivisor.mpr h))
  have h2 : chartOrderSum I u = ∑ P ∈ S.filter I, P.ord u :=
    chartOrderSum_eq_sum_filter I u S fun P _ h =>
      Finset.mem_union_left _ (Finset.mem_union_right _ (mem_support_principalOrderDivisor.mpr h))
  have h3 : chartOrderSum I w = ∑ P ∈ S.filter I, P.ord w :=
    chartOrderSum_eq_sum_filter I w S fun P _ h => Finset.mem_union_right _ (mem_support_principalOrderDivisor.mpr h)
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun P _ => P.ord_mul hu hw

theorem chartOrderSum_eq_zero (I : Place K F → Prop) {u : F} (h : ∀ P, I P → P.ord u = 0) :
    chartOrderSum I u = 0 := by
  unfold chartOrderSum
  refine Finset.sum_eq_zero fun P hP => ?_
  rw [Finset.mem_filter] at hP
  exact h P hP.2

theorem chartOrderSum_one (I : Place K F → Prop) : chartOrderSum I (1 : F) = 0 :=
  chartOrderSum_eq_zero I fun P _ => P.ord_one

theorem chartOrderSum_multiset_prod (I : Place K F → Prop) (s : Multiset F) (hs : (0 : F) ∉ s) :
    chartOrderSum I s.prod = (s.map (chartOrderSum I)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [chartOrderSum_one]
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    have ha : a ≠ 0 := fun h => hs (h ▸ Multiset.mem_cons_self a s)
    have hs' : (0 : F) ∉ s := fun h => hs (Multiset.mem_cons_of_mem h)
    rw [chartOrderSum_mul I ha (Multiset.prod_ne_zero hs'), ih hs']

end Zsum

end
end Dubon2026.SourceCurve
