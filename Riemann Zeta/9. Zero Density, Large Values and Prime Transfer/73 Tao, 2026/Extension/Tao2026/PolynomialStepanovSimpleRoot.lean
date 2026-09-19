import Tao2026.PolynomialKummerIrreducibility
import Tao2026.PolynomialStepanovAuxiliary

/-!
# Stepanov nonvanishing and point counts at a simple root

Separated orders of vanishing make the auxiliary parametrization injective.
Combining this fact with the derivative constraints gives an explicit fiber
cardinality estimate, including a reduced integer parameter condition.
-/

namespace Tao2026
open Finset Polynomial
open scoped BigOperators
noncomputable section

theorem polynomial_sum_ne_zero_of_distinct_natTrailingDegrees
    {K ι : Type*} [Field K] (s : Finset ι) (P : ι → K[X])
    (hnonzero : ∃ i ∈ s, P i ≠ 0)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, P i ≠ 0 → P j ≠ 0 →
      (P i).natTrailingDegree = (P j).natTrailingDegree → i = j) :
    (∑ i ∈ s, P i) ≠ 0 := by
  classical
  let T := s.filter fun i => P i ≠ 0
  have hT : T.Nonempty := by
    obtain ⟨i, hi, hiP⟩ := hnonzero
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hiP⟩⟩
  obtain ⟨i, hi, hmin⟩ := T.exists_min_image (fun i => (P i).natTrailingDegree) hT
  have his : i ∈ s := (Finset.mem_filter.mp hi).1
  have hiP : P i ≠ 0 := (Finset.mem_filter.mp hi).2
  intro hsum
  have hcoeff := congrArg (fun Q : K[X] => Q.coeff (P i).natTrailingDegree) hsum
  change (∑ i ∈ s, P i).coeff (P i).natTrailingDegree = (0 : K[X]).coeff (P i).natTrailingDegree at hcoeff
  rw [finsetSum_coeff, coeff_zero, Finset.sum_eq_single i] at hcoeff
  · exact (coeff_natTrailingDegree_ne_zero.2 hiP) hcoeff
  · intro j hj hji
    by_cases hjP : P j = 0
    · simp [hjP]
    · apply coeff_eq_zero_of_lt_natTrailingDegree
      have hle := hmin j (Finset.mem_filter.mpr ⟨hj, hjP⟩)
      exact lt_of_le_of_ne hle (fun heq => hji (hinj i his j hj hiP hjP heq).symm)
  · exact fun h => (h his).elim

theorem polynomial_sum_ne_zero_of_distinct_rootMultiplicities
    {K ι : Type*} [Field K] (s : Finset ι) (P : ι → K[X])
    (hnonzero : ∃ i ∈ s, P i ≠ 0)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, P i ≠ 0 → P j ≠ 0 →
      (P i).rootMultiplicity 0 = (P j).rootMultiplicity 0 → i = j) :
    (∑ i ∈ s, P i) ≠ 0 := by
  apply polynomial_sum_ne_zero_of_distinct_natTrailingDegrees s P hnonzero
  simpa only [rootMultiplicity_eq_natTrailingDegree'] using hinj

theorem nat_two_scale_code_injective
    (e h Q S : ℕ) (hS : S < h) (hQ : e * h ≤ Q)
    (j j' : Fin e) (k k' t t' : ℕ) (ht : t ≤ S) (ht' : t' ≤ S)
    (heq : t + h * j.val + Q * k = t' + h * j'.val + Q * k') :
    j = j' ∧ k = k' := by
  have hh : 0 < h := by omega
  have he : 0 < e := Nat.zero_lt_of_lt j.isLt
  have hQpos : 0 < Q := lt_of_lt_of_le (Nat.mul_pos he hh) hQ
  letI : NeZero h := ⟨hh.ne'⟩
  letI : NeZero Q := ⟨hQpos.ne'⟩
  have hrem : t + h * j.val < Q := by nlinarith [j.isLt]
  have hrem' : t' + h * j'.val < Q := by nlinarith [j'.isLt]
  have hpair : (k, (⟨t + h * j.val, hrem⟩ : Fin Q)) =
      (k', (⟨t' + h * j'.val, hrem'⟩ : Fin Q)) := by
    apply (Nat.divModEquiv Q).symm.injective
    simpa only [Nat.divModEquiv, Equiv.coe_fn_symm_mk, Nat.mul_comm, Nat.add_comm] using heq
  have hsmall : t + h * j.val = t' + h * j'.val := congrArg (fun a : ℕ × Fin Q => a.2.val) hpair
  have hpair' : (j.val, (⟨t, lt_of_le_of_lt ht hS⟩ : Fin h)) =
      (j'.val, (⟨t', lt_of_le_of_lt ht' hS⟩ : Fin h)) := by
    apply (Nat.divModEquiv h).symm.injective
    simpa only [Nat.divModEquiv, Equiv.coe_fn_symm_mk, Nat.mul_comm, Nat.add_comm] using hsmall
  exact ⟨Fin.ext (congrArg Prod.fst hpair'), congrArg Prod.fst hpair⟩

theorem polynomialStepanovAuxiliary_ne_zero_of_simple_root
    {K : Type*} [Field K] (g : K[X]) (hg : g ≠ 0) (hroot : g.rootMultiplicity 0 = 1)
    (e B S h Q : ℕ) (hS : S < h) (hQ : e * h ≤ Q)
    (v : polynomialStepanovCoefficients K e B S) (hv : v ≠ 0) :
    polynomialStepanovAuxiliary g e B S h Q v ≠ 0 := by
  classical
  let P (i : Fin e × Fin (B + 1)) :=
    (v i.1 i.2 : K[X]) * g ^ (h * i.1.val) * X ^ (Q * i.2.val)
  have hPzero (i : Fin e × Fin (B + 1)) : P i = 0 ↔ (v i.1 i.2 : K[X]) = 0 := by
    simp [P, mul_eq_zero, pow_ne_zero _ hg]
  have hPmult (i : Fin e × Fin (B + 1)) (hi : P i ≠ 0) :
      (P i).rootMultiplicity 0 =
        (v i.1 i.2 : K[X]).rootMultiplicity 0 + h * i.1.val + Q * i.2.val := by
    have hvi : (v i.1 i.2 : K[X]) ≠ 0 := (hPzero i).not.1 hi
    have hfirst := mul_ne_zero hvi (pow_ne_zero (h * i.1.val) hg)
    change ((v i.1 i.2 : K[X]) * g ^ (h * i.1.val) * X ^ (Q * i.2.val)).rootMultiplicity 0 = _
    rw [rootMultiplicity_mul (mul_ne_zero hfirst (pow_ne_zero _ X_ne_zero)),
      rootMultiplicity_mul hfirst, polynomial_rootMultiplicity_pow, hroot, mul_one]
    simp only [rootMultiplicity_eq_natTrailingDegree', natTrailingDegree_X_pow]
  change (∑ j, ∑ k, P (j, k)) ≠ 0
  rw [← Fintype.sum_prod_type]
  apply polynomial_sum_ne_zero_of_distinct_rootMultiplicities univ P
  · have hex : ∃ j k, (v j k : K[X]) ≠ 0 := by
      by_contra hnot
      push Not at hnot
      apply hv
      funext j k
      exact Subtype.ext (hnot j k)
    obtain ⟨j, k, hjk⟩ := hex
    exact ⟨(j, k), mem_univ _, (hPzero _).not.2 hjk⟩
  · intro i _ j _ hi hj heq
    rw [hPmult i hi, hPmult j hj] at heq
    have hsmall (i : Fin e × Fin (B + 1)) : (v i.1 i.2 : K[X]).rootMultiplicity 0 ≤ S := by
      rw [rootMultiplicity_eq_natTrailingDegree']
      apply (natTrailingDegree_le_natDegree _).trans
      simpa only [degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le]
        using (v i.1 i.2).property
    obtain ⟨hij, hkk⟩ := nat_two_scale_code_injective e h Q S hS hQ
      i.1 j.1 i.2.val j.2.val _ _ (hsmall i) (hsmall j) heq
    exact Prod.ext hij (Fin.ext hkk)

theorem polynomialStepanovAuxiliary_injective_of_simple_root
    {K : Type*} [Field K] (g : K[X]) (hg : g ≠ 0) (hroot : g.rootMultiplicity 0 = 1)
    (e B S h Q : ℕ) (hS : S < h) (hQ : e * h ≤ Q) :
    Function.Injective (polynomialStepanovAuxiliary g e B S h Q) := by
  apply (injective_iff_map_eq_zero _).2
  intro v hv
  by_contra hne
  exact polynomialStepanovAuxiliary_ne_zero_of_simple_root g hg hroot e B S h Q hS hQ v hne hv

theorem polynomialStepanov_card_mul_le_of_simple_root
    {K : Type*} [Field K] (p : ℕ) [ExpChar K p]
    (g : K[X]) (hg : g ≠ 0) (hroot : g.rootMultiplicity 0 = 1)
    (e B S h n M : ℕ) (c : K) (hS : S < h) (hQ : e * h ≤ p ^ n)
    (hM : M ≤ p ^ n)
    (hdim : (∑ r : Fin M, (S + r.val * g.natDegree + B + 1)) < e * (B + 1) * (S + 1))
    (T : Finset K) (hT : ∀ x ∈ T, x ^ p ^ n = x ∧ g.eval x ≠ 0 ∧ g.eval x ^ h = c) :
    T.card * M ≤ S + h * (e - 1) * g.natDegree + p ^ n * B := by
  obtain ⟨F, hF, hdeg, hvan⟩ := polynomialStepanovAuxiliary_exists_of_injective
    p g hg e B S h n M c hM
    (polynomialStepanovAuxiliary_injective_of_simple_root g hg hroot e B S h (p ^ n) hS hQ) hdim
  apply le_trans (polynomial_card_mul_le_natDegree_of_hasseDeriv_vanishing F hF T M ?_) hdeg
  intro x hx
  exact hvan x (hT x hx).1 (hT x hx).2.1 (hT x hx).2.2

theorem nat_stepanov_dimension_lt
    (e d h k : ℕ) (he : 0 < e) (hk : k ^ 2 * (e * d + 1) < h) :
    (∑ r : Fin (e * k), (h - 1 + r.val * d + k + 1)) < e * (k + 1) * (h - 1 + 1) := by
  have hh : 0 < h := by omega
  have hsum : (∑ r : Fin (e * k), (h - 1 + r.val * d + k + 1)) ≤
      e * k * (h + e * k * d + k) := by
    calc
      _ ≤ ∑ _r : Fin (e * k), (h + e * k * d + k) := by
        apply Finset.sum_le_sum
        intro r _
        have hr := Nat.mul_le_mul_right d (Nat.le_of_lt r.isLt)
        omega
      _ = _ := by simp
  have hmul := Nat.mul_lt_mul_of_pos_left hk he
  have hdim : e * k * (h + e * k * d + k) < e * (k + 1) * h := by
    nlinarith only [hmul]
  simpa only [Nat.sub_add_cancel hh] using hsum.trans_lt hdim

theorem polynomialStepanov_card_mul_le_simple_parameters
    {K : Type*} [Field K] (p : ℕ) [ExpChar K p]
    (g : K[X]) (hg : g ≠ 0) (hroot : g.rootMultiplicity 0 = 1)
    (e h n k : ℕ) (c : K) (he : 0 < e) (hQ : e * h ≤ p ^ n)
    (hk : k ^ 2 * (e * g.natDegree + 1) < h)
    (T : Finset K) (hT : ∀ x ∈ T, x ^ p ^ n = x ∧ g.eval x ≠ 0 ∧ g.eval x ^ h = c) :
    T.card * (e * k) ≤ h - 1 + h * (e - 1) * g.natDegree + p ^ n * k := by
  have hh : 0 < h := by omega
  have hkk : k ≤ k ^ 2 := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hmul := Nat.mul_le_mul_left k (show 1 ≤ k by omega)
      simpa only [mul_one, pow_two] using hmul
  have hkh : k ≤ h := hkk.trans ((Nat.le_mul_of_pos_right (k ^ 2) (by omega)).trans hk.le)
  exact polynomialStepanov_card_mul_le_of_simple_root p g hg hroot e k (h - 1) h n (e * k) c
    (Nat.sub_lt hh (by decide)) hQ ((Nat.mul_le_mul_left e hkh).trans hQ)
    (nat_stepanov_dimension_lt e g.natDegree h k he hk) T hT

end
end Tao2026
