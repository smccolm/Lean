import Dubon2026.SourceOriginalIndexedPrimeStep

/-! DUB-17/18 -> numerical modular genus -> all-level original degree
and generation. The exact expanded minimal polynomial equals the literal
primitive triangular product, provided generation and degree hold for its
divisor levels. Strong induction constructs every indexed root from the
actual full/reduced prime relations. The later joint degree/generation
induction uses this result only at proper divisor levels; no all-level
degree or generation is asserted by this conditional theorem.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean, rval_aux.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K]

theorem expandedJMinpoly_eq_slotProduct_of_divisor_induction (N : ℕ) :
    ∀ [NeZero N] (ζ : Kˣ), IsPrimitiveRoot (ζ : K) N →
      (∀ (d : ℕ), d ∣ N → ∀ [NeZero d],
        modularFunctionFieldFull d =
          IntermediateField.adjoin ℚ ({jq, qExpand ℚ d jq} : Set (LaurentSeries ℚ)) ∧
        relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull d) = dedekindPsi d) →
      expandedJMinpoly K N N = slotProduct N ζ := by
  induction N using Nat.strong_induction_on with
  | h N IH =>
    intro _ ζ hζ hall
    have hdegree : Module.finrank ℚ⟮jq⟯ ℚ⟮jq⟯⟮qExpand ℚ N jq⟯ = dedekindPsi N := by
      rw [original_j_simple_finrank_eq_minpoly,
        original_minpoly_degree_eq_full_relfinrank_of_generation N (hall N dvd_rfl).1]
      exact (hall N dvd_rfl).2
    apply expandedJMinpoly_eq_slotProduct_of_roots_and_degree N ζ hζ _ hdegree
    rintro ⟨a, b⟩ hs
    have h := (mem_indices N a b).mp hs
    have ha0 := index_fst_ne_zero hs
    haveI : NeZero a := ⟨ha0⟩
    have had : a * (N / a) = N := Nat.mul_div_cancel' h.1
    by_cases hd1 : N / a = 1
    · have haN : a = N := by simpa only [hd1, mul_one] using had
      have hb0 : b = 0 := by have := h.2.2.1; omega
      subst a
      subst b
      exact expandedJMinpoly_top_slot_root N ζ
    · have hp : (N / a).minFac.Prime := Nat.minFac_prime hd1
      let p := (N / a).minFac
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨d, hd⟩ := Nat.minFac_dvd (N / a)
      have hd0 : d ≠ 0 := by
        intro he
        rw [hd, he, mul_zero, mul_zero] at had
        exact NeZero.ne N had.symm
      haveI : NeZero d := ⟨hd0⟩
      have hN : N = a * d * p := by rw [← had, hd]; ring
      have hMN : a * d ∣ N := ⟨p, hN⟩
      have hlt : a * d < N := by
        rw [hN]
        exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne (a * d))) hp.one_lt
      have hζ' : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) (a * d) := by
        have h' := primitive_root_pow_div hζ hMN
        have hdiv : N / (a * d) = p := by
          rw [hN, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne (a * d)))]
        rwa [hdiv] at h'
      have hlower := IH (a * d) hlt (ζ ^ p) hζ'
        (fun e he _ => hall e (he.trans hMN))
      have hprev : ∀ (m : ℕ) [NeZero m], a * d = m * p →
          expandedJMinpoly K m m = slotProduct m (ζ ^ (p * p)) := by
        intro m _ hm
        have hmN : m ∣ N := ⟨p * p, by rw [hN, hm]; ring⟩
        have hmLt : m < N := lt_of_le_of_lt
          (by rw [hm]; exact Nat.le_mul_of_pos_right m hp.pos) hlt
        have hζ'' : IsPrimitiveRoot ((ζ ^ (p * p) : Kˣ) : K) m := by
          have h' := primitive_root_pow_div hζ hmN
          have hdiv : N / m = p * p := by
            rw [hN, hm, Nat.mul_assoc, Nat.mul_div_cancel_left _
              (Nat.pos_of_ne_zero (NeZero.ne m))]
          rwa [hdiv] at h'
        exact IH m hmLt (ζ ^ (p * p)) hζ'' (fun e he _ => hall e (he.trans hmN))
      have hgen := (hall (a * d) hMN).1
      have hM := (hall (a * d) hMN).2
      have htop := hall N dvd_rfl
      have hζtop : IsPrimitiveRoot (ζ : K) (a * d * p) := by simpa only [hN] using hζ
      have hstop : (⟨a, b⟩ : Σ _ : ℕ, ℕ) ∈ indices (a * d * p) := by
        simpa only [hN] using hs
      simp only [hN] at htop ⊢
      have hdeg := original_relative_prime_minpoly_degree_of_induction
        (a * d) p htop.1 hM htop.2
      exact original_indexed_prime_step_root a d p b ζ hζtop hstop hgen hdeg hlower hprev

end
end Dubon2026.SourceFunctionField
