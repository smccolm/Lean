/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Adapted from Mathlib/RingTheory/Henselian.lean at
c5ea00351c28e24afc9f0f84379aa41082b1188f, IsAdicComplete.henselianRing.
The original Newton proof does not consume the monicity binder. Here its same
complete-ring construction is exposed for arbitrary actual polynomials.
-/
import Mathlib.RingTheory.Henselian

/-! # Simple roots of arbitrary polynomials in the original adically complete ring -/

namespace Dubon2026
noncomputable section

open Polynomial IsLocalRing Function List
open scoped Ring

/-- The original Newton sequence in the actual adically complete ring lifts
any simple residual root of the original polynomial. Monicity is unnecessary
for this construction; the proof is the pinned complete-ring proof with its
unused monicity binder removed. -/
theorem adicComplete_polynomial_simple_root
    {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (f : R[X]) (a₀ : R) (h₁ : f.eval a₀ ∈ I)
    (h₂ : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  classical
    let f' := derivative f
    -- we define a sequence `c n` by starting at `a₀` and then continually
    -- applying the function sending `b` to `b - f(b)/f'(b)` (Newton's method).
    -- Note that `f'.eval b` is a unit, because `b` has the same residue as `a₀` modulo `I`.
    let c : ℕ → R := fun n => Nat.recOn n a₀ fun _ b => b - f.eval b * (f'.eval b)⁻¹ʳ
    have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f'.eval (c n))⁻¹ʳ := by
      intro n
      simp only [c]
    -- we now spend some time determining properties of the sequence `c : ℕ → R`
    -- `hc_mod`: for every `n`, we have `c n ≡ a₀ [SMOD I]`
    -- `hf'c`  : for every `n`, `f'.eval (c n)` is a unit
    -- `hfcI`  : for every `n`, `f.eval (c n)` is contained in `I ^ (n+1)`
    have hc_mod : ∀ n, c n ≡ a₀ [SMOD I] := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => ?_
      rw [hc, sub_eq_add_neg, ← add_zero a₀]
      refine ih.add ?_
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine I.mul_mem_right _ ?_
      rw [← SModEq.zero] at h₁ ⊢
      exact (ih.eval f).trans h₁
    have hf'c : ∀ n, IsUnit (f'.eval (c n)) := by
      intro n
      haveI := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
      apply IsUnit.of_map (Ideal.Quotient.mk I)
      convert! h₂ using 1
      exact SModEq.def.mp ((hc_mod n).eval _)
    have hfcI : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
      intro n
      induction n with
      | zero => simpa only [Nat.rec_zero, zero_add, pow_one] using h₁
      | succ n ih => ?_
      rw [← taylor_eval_sub (c n), hc, sub_eq_add_neg, sub_eq_add_neg,
        add_neg_cancel_comm]
      rw [eval_eq_sum, sum_over_range' _ _ _ (lt_add_of_pos_right _ zero_lt_two), ←
        Finset.sum_range_add_sum_Ico _ (Nat.le_add_left _ _)]
      swap
      · intro i
        rw [zero_mul]
      refine Ideal.add_mem _ ?_ ?_
      · rw [← one_add_one_eq_two, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton,
          taylor_coeff_zero, taylor_coeff_one, pow_zero, pow_one, mul_one, mul_neg,
          mul_left_comm, Ring.mul_inverse_cancel _ (hf'c n), mul_one, add_neg_cancel]
        exact Ideal.zero_mem _
      · refine Submodule.sum_mem _ ?_
        simp only [Finset.mem_Ico]
        rintro i ⟨h2i, _⟩
        have aux : n + 2 ≤ i * (n + 1) := by trans 2 * (n + 1) <;> nlinarith only [h2i]
        refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right aux ?_)
        rw [pow_mul']
        exact Ideal.pow_mem_pow ((Ideal.neg_mem_iff _).2 <| Ideal.mul_mem_right _ _ ih) _
    -- we are now in the position to show that `c : ℕ → R` is a Cauchy sequence
    have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
      intro m n hmn
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      clear hmn
      induction k with
      | zero => rw [add_zero]
      | succ k ih => ?_
      rw [← add_assoc, hc, ← add_zero (c m), sub_eq_add_neg]
      refine ih.add ?_
      symm
      rw [SModEq.zero, Ideal.neg_mem_iff]
      refine Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right ?_ (hfcI _))
      rw [add_assoc]
      exact le_self_add
    -- hence the sequence converges to some limit point `a`, which is the `a` we are looking for
    obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
    refine ⟨a, ?_, ?_⟩
    · show f.IsRoot a
      suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
      intro n
      specialize ha n
      rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
      refine (ha.symm.eval f).trans ?_
      rw [SModEq.zero]
      exact Ideal.pow_le_pow_right le_self_add (hfcI _)
    · show a - a₀ ∈ I
      specialize ha (0 + 1)
      rw [hc, pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, sub_eq_add_neg] at ha
      rw [← SModEq.sub_mem, ← add_zero a₀]
      refine ha.symm.trans (SModEq.rfl.add ?_)
      rw [SModEq.zero, Ideal.neg_mem_iff]
      exact Ideal.mul_mem_right _ _ h₁

end
end Dubon2026
