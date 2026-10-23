import Dubon2026.SourceResidueIndexedPrimeStep

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> all-level
residue degree -> coprime nonmembership -> lower-level conjugate induction.
Adapt local SourceOriginalConjugateInduction to the actual coefficient-field j series and divisor field.
The same native minimal-polynomial, tower and primitive-slot arguments are used.
Every lower-level generation, degree and product hypothesis remains explicit;
the all-level consumer must derive them by induction. No new characteristic-zero
structure is imposed on the residue coefficient field. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Polynomial IntermediateField ConjugateSlots PrimeDegreeAux SourceLevelProjective
open scoped IntermediateField
variable {K : Type*} [Field K]

theorem residueExpandedJMinpoly_eq_slotProduct_of_divisor_induction (N : ℕ) :
    ∀ [NeZero N] (ζ : Kˣ), IsPrimitiveRoot (ζ : K) N →
      (∀ (d : ℕ), d ∣ N → ∀ [NeZero d],
        modularFunctionFieldCoeff d K =
          IntermediateField.adjoin K ({(jqModC K), qExpand K d (jqModC K)} : Set (LaurentSeries K)) ∧
        relfinrank K⟮(jqModC K)⟯ (modularFunctionFieldCoeff d K) = dedekindPsi d) →
      residueExpandedJMinpoly K N N = slotProduct N ζ := by
  induction N using Nat.strong_induction_on with
  | h N IH =>
    intro _ ζ hζ hall
    have hdegree : Module.finrank K⟮(jqModC K)⟯ K⟮(jqModC K)⟯⟮qExpand K N (jqModC K)⟯ = dedekindPsi N := by
      rw [residue_j_simple_finrank_eq_minpoly K,
        residue_minpoly_degree_eq_full_relfinrank_of_generation K N (hall N dvd_rfl).1]
      exact (hall N dvd_rfl).2
    apply residueExpandedJMinpoly_eq_slotProduct_of_roots_and_degree N ζ hζ _ hdegree
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
      exact residueExpandedJMinpoly_top_slot_root N ζ
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
          residueExpandedJMinpoly K m m = slotProduct m (ζ ^ (p * p)) := by
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
      have hdeg := residue_relative_prime_minpoly_degree_of_induction
        (a * d) p htop.1 hM htop.2
      exact residue_indexed_prime_step_root a d p b ζ hζtop hstop hgen hdeg hlower hprev

end
end Dubon2026.SourceFunctionField
