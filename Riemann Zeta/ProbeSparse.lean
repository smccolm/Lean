import RiemannZeta.GuthMaynard.DFIEquation30

open Complex Finset Set Filter Topology MeasureTheory
open scoped BigOperators Topology
open Classical

namespace RiemannZeta.GuthMaynard

theorem sparse_term_factor
    (K d r q : ℕ) (hd : 0 < d) (hr : 0 < r) (hKr : K < q)
    (hq : q = d * r) (alpha theta : ℝ) :
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) =
      (q : ℝ) ^ (-alpha) * (d : ℝ) ^ (-theta) *
        (r : ℝ) ^ (-(1 + theta)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le K) hKr)
  have hqmul : (q : ℝ) = (d : ℝ) * r := by rw [hq]; norm_num
  rw [hqmul, Real.mul_rpow hdR.le hrR.le]
  rw [div_eq_mul_inv, mul_inv]
  rw [← Real.rpow_neg hdR.le, ← Real.rpow_neg hrR.le]
  rw [Real.mul_rpow hdR.le hrR.le]
  calc
    (d : ℝ) * ((d : ℝ) ^ (-(1 + alpha + theta)) *
        (r : ℝ) ^ (-(1 + alpha + theta))) =
      ((d : ℝ) ^ (1 : ℝ) * (d : ℝ) ^ (-(1 + alpha + theta))) *
        (r : ℝ) ^ (-(1 + alpha + theta)) := by rw [Real.rpow_one]; ring
    _ = (d : ℝ) ^ ((1 : ℝ) - (1 + alpha + theta)) *
        (r : ℝ) ^ (-(1 + alpha + theta)) := by
      rw [← Real.rpow_add hdR]
      ring_nf
    _ = ((d : ℝ) ^ (-alpha) * (d : ℝ) ^ (-theta)) *
        ((r : ℝ) ^ (-alpha) * (r : ℝ) ^ (-(1 + theta))) := by
      rw [← Real.rpow_add hdR, ← Real.rpow_add hrR]
      congr 1 <;> ring
    _ = (d : ℝ) ^ (-alpha) * (r : ℝ) ^ (-alpha) *
        (d : ℝ) ^ (-theta) * (r : ℝ) ^ (-(1 + theta)) := by ring

#check Real.rpow_le_rpow_of_nonpos
#check Real.rpow_le_one
#check Nat.mul_left_cancel
#check Nat.mul_right_cancel
#check Real.zero_rpow
#check Summable.of_nonneg_of_le
#check Summable.tsum_add

theorem probe_summable_finset_sum_apply
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    Summable (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

theorem probe_tsum_finset_sum_apply
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ)
    (hf : ∀ i ∈ s, Summable (f i)) :
    (∑' q, ∑ i ∈ s, f i q) = ∑ i ∈ s, ∑' q, f i q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [(hf i (by simp)).tsum_add
        (probe_summable_finset_sum_apply s f (fun j hj => hf j (by simp [hj])))]
      rw [ih (fun j hj => hf j (by simp [hj]))]

theorem sparse_term_le
    (K d r q : ℕ) (hd : 0 < d) (hr : 0 < r) (hKr : K < q)
    (hq : q = d * r) (alpha theta : ℝ) (ha : 0 < alpha) (ht : 0 < theta) :
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) ≤
      (K + 1 : ℝ) ^ (-alpha) * (r : ℝ) ^ (-(1 + theta)) := by
  rw [sparse_term_factor K d r q hd hr hKr hq alpha theta]
  have hKq : (K + 1 : ℝ) ≤ q := by exact_mod_cast hKr
  have hKpos : (0 : ℝ) < K + 1 := by positivity
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le hKpos hKq
  have hqpow : (q : ℝ) ^ (-alpha) ≤ (K + 1 : ℝ) ^ (-alpha) :=
    Real.rpow_le_rpow_of_nonpos hKpos hKq (by linarith)
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpow : (d : ℝ) ^ (-theta) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one hdOne
      (by linarith : -theta ≤ 0)
  have hrpow : 0 ≤ (r : ℝ) ^ (-(1 + theta)) := Real.rpow_nonneg (by positivity) _
  calc
    (q : ℝ) ^ (-alpha) * (d : ℝ) ^ (-theta) *
        (r : ℝ) ^ (-(1 + theta)) ≤
      (K + 1 : ℝ) ^ (-alpha) * 1 *
        (r : ℝ) ^ (-(1 + theta)) := by gcongr
    _ = _ := by ring

theorem tsum_sparse_multiples_rpow_le
    (K d : ℕ) (hd : 0 < d) (alpha theta : ℝ)
    (ha : 0 < alpha) (ht : 0 < theta) :
    (∑' q : ℕ, if K < q ∧ d ∣ q then
        (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0) ≤
      (K + 1 : ℝ) ^ (-alpha) * (1 + theta⁻¹) := by
  let f : ℕ → ℝ := fun q => if K < q ∧ d ∣ q then
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0
  let g : ℕ → ℕ := fun r => d * r
  have hg : Function.Injective g := by
    intro r s hrs
    dsimp [g] at hrs
    exact Nat.eq_of_mul_eq_mul_left (by omega) hrs
  have hfOutside : ∀ q ∉ Set.range g, f q = 0 := by
    intro q hq
    dsimp [f]
    split_ifs with h
    · exfalso
      apply hq
      obtain ⟨r, hr⟩ := h.2
      exact ⟨r, by simpa [g] using hr.symm⟩
    · rfl
  have htsum : (∑' q : ℕ, f q) = ∑' r : ℕ, f (g r) := by
    apply tsum_eq_tsum_of_hasSum_iff_hasSum
    intro x
    exact (hg.hasSum_iff hfOutside).symm
  have hsPower : Summable (fun r : ℕ => (r : ℝ) ^ (-(1 + theta))) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hmajorSummable : Summable (fun r : ℕ =>
      (K + 1 : ℝ) ^ (-alpha) *
        (r : ℝ) ^ (-(1 + theta))) := by
    apply Summable.mul_left
    exact hsPower
  rw [show (∑' q : ℕ, if K < q ∧ d ∣ q then
        (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0) =
      ∑' q : ℕ, f q by rfl, htsum]
  calc
    (∑' r : ℕ, f (g r)) ≤
        ∑' r : ℕ, (K + 1 : ℝ) ^ (-alpha) *
          (r : ℝ) ^ (-(1 + theta)) := by
      apply Summable.tsum_le_tsum
      · intro r
        by_cases hr0 : r = 0
        · subst r
          dsimp [f, g]
          simp only [Nat.cast_zero]
          rw [Real.zero_rpow (by linarith : -(1 + theta) ≠ 0)]
          positivity
        · have hr : 0 < r := Nat.pos_of_ne_zero hr0
          dsimp [f, g]
          simp only [dvd_mul_right]
          split_ifs with hKr
          · simpa [hr0] using sparse_term_le K d r (d * r) hd hr hKr.1 rfl
              alpha theta ha ht
          · positivity
      · have hcomp : Summable (f ∘ g) := by
          refine Summable.of_nonneg_of_le
            (f := fun r : ℕ => (K + 1 : ℝ) ^ (-alpha) *
              (r : ℝ) ^ (-(1 + theta)))
            (g := f ∘ g) ?_ ?_ hmajorSummable
          · intro r
            dsimp [f, g]
            split_ifs <;> positivity
          · intro r
            by_cases hr0 : r = 0
            · subst r
              dsimp [f, g]
              simp only [Nat.cast_zero]
              have hzero : (0 : ℝ) ^ (-(1 + theta)) = 0 :=
                Real.zero_rpow (by linarith)
              rw [hzero]
              positivity
            · have hr : 0 < r := Nat.pos_of_ne_zero hr0
              dsimp [f, g]
              simp only [dvd_mul_right]
              split_ifs with hKr
              · simpa [hr0] using sparse_term_le K d r (d * r) hd hr hKr.1 rfl
                  alpha theta ha ht
              · positivity
        exact hcomp
      · exact hmajorSummable
    _ = (K + 1 : ℝ) ^ (-alpha) *
        (∑' r : ℕ, (r : ℝ) ^ (-(1 + theta))) := by rw [tsum_mul_left]
    _ ≤ (K + 1 : ℝ) ^ (-alpha) * (1 + theta⁻¹) := by
      gcongr
      have htail := tsum_nat_add_one_rpow_neg_le
        (L := (1 : ℝ)) (p := 1 + theta) (by norm_num) (by linarith)
      have hsShift : Summable (fun j : ℕ =>
          ((j + 1 : ℕ) : ℝ) ^ (-(1 + theta))) := by
        simpa [Nat.add_comm] using (summable_nat_add_iff 1).2 hsPower
      have hsplit0 := hsPower.sum_add_tsum_nat_add 1
      have hsplit1 := hsShift.sum_add_tsum_nat_add 1
      have hrewrite : (∑' r : ℕ,
            (r : ℝ) ^ (-(1 + theta))) =
          1 + ∑' j : ℕ, ((1 : ℝ) + (j + 1 : ℕ)) ^ (-(1 + theta)) := by
        calc
          (∑' r : ℕ, (r : ℝ) ^ (-(1 + theta))) =
              ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ (-(1 + theta)) := by
            have hzero : (0 : ℝ) ^ (-(1 + theta)) = 0 :=
              Real.zero_rpow (by linarith)
            have hprefix : ∑ i ∈ Finset.range 1,
                (i : ℝ) ^ (-(1 + theta)) = 0 := by
              simp only [Finset.sum_range_succ, Finset.sum_range_zero,
                zero_add, Nat.cast_zero, hzero]
            rw [hprefix, zero_add] at hsplit0
            simpa [Nat.cast_add] using hsplit0.symm
          _ = 1 + ∑' j : ℕ,
              (((j + 1) + 1 : ℕ) : ℝ) ^ (-(1 + theta)) := by
            simpa using hsplit1.symm
          _ = _ := by
            congr 1
            apply tsum_congr
            intro j
            congr 1
            push_cast
            ring
      rw [hrewrite]
      calc
        1 + ∑' j : ℕ, ((1 : ℝ) + (j + 1 : ℕ)) ^ (-(1 + theta)) ≤
            1 + (1 : ℝ) ^ (1 - (1 + theta)) / ((1 + theta) - 1) := by
          gcongr
        _ = 1 + theta⁻¹ := by
          rw [Real.one_rpow]
          field_simp [ne_of_gt ht]
          ring

theorem divisor_rpow_weight_identity
    (d q : ℕ) (hq : 0 < q) (beta : ℝ) :
    ((d : ℝ) / (q : ℝ) ^ 2) * (q : ℝ) ^ beta =
      (d : ℝ) / (q : ℝ) ^ (2 - beta) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show (q : ℝ) ^ 2 = (q : ℝ) ^ (2 : ℝ) by
    exact (Real.rpow_natCast (q : ℝ) 2).symm]
  rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
  calc
    (d : ℝ) * (q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ beta =
        (d : ℝ) * ((q : ℝ) ^ (-(2 : ℝ)) * (q : ℝ) ^ beta) := by ring
    _ = (d : ℝ) * (q : ℝ) ^ (-(2 : ℝ) + beta) := by
      rw [Real.rpow_add hqR]
    _ = (d : ℝ) / (q : ℝ) ^ (2 - beta) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
      congr 1
      ring

theorem summable_sparse_multiples_rpow
    (K d : ℕ) (alpha theta : ℝ)
    (ha : 0 < alpha) (ht : 0 < theta) :
    Summable (fun q : ℕ => if K < q ∧ d ∣ q then
      (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0) := by
  have hp : 1 < 1 + alpha + theta := by linarith
  have hs : Summable (fun q : ℕ =>
      (d : ℝ) * (q : ℝ) ^ (-(1 + alpha + theta))) := by
    apply Summable.mul_left
    apply Real.summable_nat_rpow.mpr
    linarith
  refine Summable.of_nonneg_of_le
    (f := fun q : ℕ => (d : ℝ) * (q : ℝ) ^ (-(1 + alpha + theta)))
    ?_ ?_ hs
  · intro q
    split_ifs <;> positivity
  · intro q
    split_ifs with h
    · have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le K) h.1
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      rw [div_eq_mul_inv, ← Real.rpow_neg hqR.le]
    · positivity

theorem probe_tsum_norm_dfiEquation27ArithmeticCoefficient_mul_rpow_tail_le
    (K a b h : ℕ) (ha : 0 < a) (hb : 0 < b) (hh : 0 < h)
    (alpha theta beta : ℝ) (halpha : 0 < alpha) (htheta : 0 < theta)
    (hexp : 2 - beta = 1 + alpha + theta) :
    (∑' q : ℕ, if K < q then
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta
      else 0) ≤
      ((a * b : ℕ) : ℝ) * h.divisors.card *
        ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
  let g : ℕ → ℕ → ℝ := fun d q => if K < q ∧ d ∣ q then
    (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0
  let A : ℕ → ℝ := fun q => if K < q then
    ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta else 0
  let B : ℕ → ℝ := fun q =>
    ((a * b : ℕ) : ℝ) * ∑ d ∈ h.divisors, g d q
  have hgSummable (d : ℕ) (hd : d ∈ h.divisors) : Summable (g d) := by
    dsimp [g]
    exact summable_dfiSparseMultiples_rpow K d alpha theta halpha htheta
  have hsumGSummable : Summable (fun q => ∑ d ∈ h.divisors, g d q) :=
    probe_summable_finset_sum_apply h.divisors g hgSummable
  have hBSummable : Summable B := by
    dsimp [B]
    exact hsumGSummable.mul_left _
  have hAnonneg (q : ℕ) : 0 ≤ A q := by
    dsimp [A]
    split_ifs <;> positivity
  have hBnonneg (q : ℕ) : 0 ≤ B q := by
    dsimp [B, g]
    positivity
  have hAB (q : ℕ) : A q ≤ B q := by
    by_cases hKq : K < q
    · have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le K) hKq
      letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
      have harith :=
        norm_dfiEquation27ArithmeticCoefficient_le_divisorExpansion
          a b h q ha hb hh
      have hqpow : 0 ≤ (q : ℝ) ^ beta := Real.rpow_nonneg (by positivity) _
      dsimp [A, B, g]
      rw [if_pos hKq]
      calc
        ‖dfiEquation27ArithmeticCoefficient a b h q‖ * (q : ℝ) ^ beta ≤
            (((a * b : ℕ) : ℝ) *
              (∑ d ∈ h.divisors,
                if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0)) *
              (q : ℝ) ^ beta :=
          mul_le_mul_of_nonneg_right harith hqpow
        _ = ((a * b : ℕ) : ℝ) *
            ((∑ d ∈ h.divisors,
                if d ∣ q then (d : ℝ) / (q : ℝ) ^ 2 else 0) *
              (q : ℝ) ^ beta) := by ring
        _ = ((a * b : ℕ) : ℝ) *
            ∑ d ∈ h.divisors,
              if K < q ∧ d ∣ q then
                (d : ℝ) / (q : ℝ) ^ (1 + alpha + theta) else 0 := by
          rw [Finset.sum_mul]
          apply congrArg (((a * b : ℕ) : ℝ) * ·)
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdq : d ∣ q
          · simp only [hdq, hKq, and_self, if_true]
            rw [dfiDivisorRpowWeight_identity d q hq beta, hexp]
          · simp [hdq]
    · dsimp [A]
      rw [if_neg hKq]
      exact hBnonneg q
  have hASummable : Summable A :=
    Summable.of_nonneg_of_le hAnonneg hAB hBSummable
  have hsumG : (∑' q : ℕ, ∑ d ∈ h.divisors, g d q) =
      ∑ d ∈ h.divisors, ∑' q : ℕ, g d q :=
    probe_tsum_finset_sum_apply h.divisors g hgSummable
  change (∑' q : ℕ, A q) ≤ _
  calc
    (∑' q : ℕ, A q) ≤ ∑' q : ℕ, B q :=
      Summable.tsum_le_tsum hAB hASummable hBSummable
    _ = ((a * b : ℕ) : ℝ) *
        (∑ d ∈ h.divisors, ∑' q : ℕ, g d q) := by
      dsimp [B]
      rw [tsum_mul_left, hsumG]
    _ ≤ ((a * b : ℕ) : ℝ) *
        (∑ d ∈ h.divisors,
          ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹)) := by
      gcongr with d hd
      dsimp [g]
      exact tsum_dfiSparseMultiples_rpow_le K d
        (Nat.pos_of_mem_divisors hd) alpha theta halpha htheta
    _ = ((a * b : ℕ) : ℝ) * h.divisors.card *
        ((K : ℝ) + 1) ^ (-alpha) * (1 + theta⁻¹) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      push_cast
      ring

end RiemannZeta.GuthMaynard
