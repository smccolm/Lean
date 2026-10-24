import Dubon2026.SourceJointChartRootFactorNormalization

/-! DUB-17/18 -> Kummer power lifting -> finite overlap -> two-chart
decomposition. Split a monomial-reduction denominator into its small-root
monic factor and a good constant-reduction factor. The factorization argument
adapts Apache-2.0 FLT commit 6e837e75355538c7f80bab5b956861e86c4eacc2;
existing good-monomial multiplication supplies coefficient integrality. -/
namespace Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
noncomputable section
open Polynomial

variable {L : Type*} [Field L] (A : ValuationSubring L)

theorem goodAt_X_sub_C {c : L} (hc : A.valuation c < 1) :
    IsGoodAt A 1 (X - C c) := by
  refine ⟨by simp, fun j hj => ?_⟩
  rw [coeff_sub, coeff_X_of_ne_one hj, coeff_C]
  by_cases hj0 : j = 0
  · rw [if_pos hj0, zero_sub, Valuation.map_neg]
    exact hc
  · rw [if_neg hj0, sub_self, map_zero]
    exact zero_lt_one

theorem goodAt_prod_X_sub_C (cs : Multiset L)
    (hcs : ∀ c ∈ cs, A.valuation c < 1) :
    IsGoodAt A cs.card (cs.map fun c => (X - C c : L[X])).prod := by
  induction cs using Multiset.induction_on with
  | empty => simpa using (IsGoodAt.one (A := A))
  | cons c cs ih =>
    have hc := goodAt_X_sub_C A (hcs c (Multiset.mem_cons_self _ _))
    have hs := ih (fun d hd => hcs d (Multiset.mem_cons_of_mem hd))
    simpa [Nat.add_comm] using hc.mul hs

theorem valuation_ne_one_of_goodAt_root {t : L[X]} {d : ℕ}
    (ht : IsGoodAt A d t) {a : L} (ha : t.IsRoot a) : A.valuation a ≠ 1 := by
  intro h1
  have htd : t.coeff d ≠ 0 := by
    intro h
    have := ht.1
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hdle : d ≤ t.natDegree := le_natDegree_of_ne_zero htd
  have hev : t.eval a = 0 := ha
  rw [eval_eq_sum_range] at hev
  have hdmem : d ∈ Finset.range (t.natDegree + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hdle)
  rw [← Finset.add_sum_erase _ _ hdmem] at hev
  have hkey : t.coeff d * a ^ d =
      -∑ j ∈ (Finset.range (t.natDegree + 1)).erase d, t.coeff j * a ^ j := by
    linear_combination hev
  have hlt : A.valuation (∑ j ∈ (Finset.range (t.natDegree + 1)).erase d,
      t.coeff j * a ^ j) < 1 := by
    apply Valuation.map_sum_lt _ one_ne_zero
    intro j hj
    rw [map_mul, map_pow, h1, one_pow, mul_one]
    exact ht.2 j (Finset.mem_erase.mp hj).1
  have hval : A.valuation (t.coeff d * a ^ d) = 1 := by
    rw [map_mul, map_pow, ht.1, h1, one_pow, one_mul]
  rw [hkey, Valuation.map_neg] at hval
  exact absurd hval (ne_of_lt hlt)

theorem exists_monic_good_factors [IsAlgClosed L] {t : L[X]} {d : ℕ}
    (ht : IsGoodAt A d t) :
    ∃ (u : L) (a b : L[X]), u ≠ 0 ∧ u⁻¹ ∈ A ∧ a.Monic ∧
      IsGoodAt A a.natDegree a ∧ IsGood A b ∧ t = C u * a * b := by
  classical
  have ht0 : t ≠ 0 := by
    intro h
    have := ht.1
    rw [h, coeff_zero, map_zero] at this
    exact zero_ne_one this
  have hsplit : C t.leadingCoeff * (t.roots.map fun x => X - C x).prod = t :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  let sm := t.roots.filter fun x => A.valuation x < 1
  let lg := t.roots.filter fun x => ¬ A.valuation x < 1
  have hsplit2 : t.roots = sm + lg := (Multiset.filter_add_not _ _).symm
  have hlg1 : ∀ x ∈ lg, 1 < A.valuation x := by
    intro x hx
    obtain ⟨hxr, hxv⟩ := Multiset.mem_filter.mp hx
    have hne := valuation_ne_one_of_goodAt_root A ht ((mem_roots ht0).mp hxr)
    exact lt_of_le_of_ne (not_lt.mp hxv) (Ne.symm hne)
  have hlg0 : ∀ x ∈ lg, x ≠ 0 := by
    intro x hx h
    have := hlg1 x hx
    rw [h, map_zero] at this
    exact absurd this (not_lt.mpr zero_le')
  let u : L := t.leadingCoeff * (lg.map fun x => -x).prod
  let cs : Multiset L := lg.map fun x => x⁻¹
  have hcs : ∀ c ∈ cs, A.valuation c < 1 := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hc
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ (hlg1 x hx)
  have hsm : ∀ x ∈ sm, A.valuation x < 1 := fun _ hx => (Multiset.mem_filter.mp hx).2
  let a : L[X] := (sm.map fun x => X - C x).prod
  let b : L[X] := (cs.map fun c => 1 - C c * X).prod
  have ha : IsGoodAt A a.natDegree a := by
    simpa only [a, natDegree_multiset_prod_X_sub_C_eq_card] using goodAt_prod_X_sub_C A sm hsm
  have hb : IsGood A b := good_prod_one_sub A cs hcs
  have hfac : t = C u * (a * b) := by
    conv_lhs => rw [← hsplit, hsplit2, Multiset.map_add, Multiset.prod_add,
      prod_X_sub_C_eq_C_mul_prod_one_sub lg hlg0]
    dsimp [u, a, b, cs]
    rw [C_mul]
    ring
  have hu : u ≠ 0 := by
    intro h
    apply ht0
    rw [hfac, h, C_0, zero_mul]
  have hu1 : 1 ≤ A.valuation u := by
    have hP := ha.mul (show IsGoodAt A 0 b from hb)
    have he : t.coeff d = u * (a * b).coeff d := by rw [hfac, coeff_C_mul]
    calc 1 = A.valuation (t.coeff d) := ht.1.symm
      _ = A.valuation u * A.valuation ((a * b).coeff d) := by rw [he, map_mul]
      _ ≤ A.valuation u * 1 := by gcongr; exact hP.valuation_le d
      _ = A.valuation u := mul_one _
  refine ⟨u, a, b, hu, ?_, monic_multisetProd_X_sub_C sm, ha, hb, ?_⟩
  · rw [← A.valuation_le_one_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hu1
  · rw [hfac, mul_assoc]

end
end Dubon2026.SourceCurve.RegularProlongation.JointChartConstants
