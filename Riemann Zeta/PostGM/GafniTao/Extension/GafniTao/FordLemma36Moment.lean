import GafniTao.FordLemma36Equation320

/-!
# Ford Lemma 3.6: moment-bound assembly

This file reconnects the canonical exponent sequence to the actual
Vinogradov moment recurrence.  The coefficient is existential: the audited
prime number theorem supplies Ford's narrow prime packet only eventually,
and the omitted finite endpoints are absorbed into one fixed coefficient.
No exponent loss is introduced.
-/

namespace GafniTao

noncomputable section

/-- The rounded choice remains admissible after the exponent has crossed
below `k`.  This is the branch Ford dispatches in one sentence. -/
theorem fordLemma35Admissible_below
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaPos : 0 < delta) (hdeltaUpper : delta ≤ k) :
    4 ≤ fordR36 k delta ∧ fordR36 k delta ≤ k ∧
      0 ≤ fordY35 k (fordR36 k delta) delta ∧
      2 * delta ≤ (k : ℝ) ^ 2 - k ∧
      1 / (((k + 1 : ℕ) : ℝ)) ≤
        fordPhiStar35 k (fordR36 k delta) delta := by
  have hk26 : 26 ≤ k := by omega
  have hk0 : (0 : ℝ) < k := by positivity
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hrEq := fordR36_eq_k_of_pos_le hk26 hdeltaPos hdeltaUpper
  have hy : 0 ≤ fordY35 k (fordR36 k delta) delta := by
    rw [hrEq]
    simp [fordY35]
    linarith
  have hdeltaRange : 2 * delta ≤ (k : ℝ) ^ 2 - k := by
    nlinarith
  have hden : 0 < 2 * (k : ℝ) * k +
      (2 * delta - ((k : ℝ) - k) * ((k : ℝ) - k + 1)) := by
    nlinarith
  have hstar : 1 / (((k + 1 : ℕ) : ℝ)) ≤
      fordPhiStar35 k (fordR36 k delta) delta := by
    rw [hrEq]
    unfold fordPhiStar35 fordY35
    rw [div_le_div_iff₀ (by positivity :
      (0 : ℝ) < (((k + 1 : ℕ) : ℝ))) hden]
    push_cast
    nlinarith
  rw [hrEq] at hy hstar ⊢
  exact ⟨by omega, le_rfl, hy, hdeltaRange, hstar⟩

/-- Every term of the canonical sequence is positive and no larger than its
initial term, including across the first crossing below `Delta = k`. -/
theorem fordDeltaSequence36_pos_le_initial
    {k n : ℕ} (hk : 1000 ≤ k) :
    0 < fordDeltaSequence36 k n ∧
      fordDeltaSequence36 k n ≤ fordDeltaInitial35 k := by
  by_cases habove : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m
  · have hnorm := fordDSequence36_bounds_of_above hk habove
    have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    constructor
    · unfold fordDSequence36 at hnorm
      rcases div_pos_iff.mp hnorm.1 with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge hkSq.le) hneg.2)
    · unfold fordDSequence36 at hnorm
      rw [fordDeltaSequence36_zero] at hnorm
      exact (div_le_div_iff_of_pos_right hkSq).mp hnorm.2
  · have hex : ∃ m, m < n ∧ fordDeltaSequence36 k m ≤ (k : ℝ) := by
      rw [not_forall] at habove
      obtain ⟨m, hm⟩ := habove
      rw [Classical.not_imp] at hm
      exact ⟨m, hm.1, le_of_not_gt hm.2⟩
    let m : ℕ := Nat.find hex
    have hmSpec := Nat.find_spec hex
    have hbefore : ∀ q, q < m → (k : ℝ) < fordDeltaSequence36 k q := by
      intro q hq
      by_contra hqNot
      have hqSpec : q < n ∧ fordDeltaSequence36 k q ≤ (k : ℝ) :=
        ⟨hq.trans hmSpec.1, le_of_not_gt hqNot⟩
      exact (not_lt_of_ge (Nat.find_min' hex hqSpec)) hq
    have hmNorm := fordDSequence36_bounds_of_above hk hbefore
    have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    have hmPos : 0 < fordDeltaSequence36 k m := by
      unfold fordDSequence36 at hmNorm
      rcases div_pos_iff.mp hmNorm.1 with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_lt_of_ge hkSq.le) hneg.2)
    have hmn : m ≤ n := hmSpec.1.le
    have hn := fordDeltaSequence36_pos_le_of_pos_le
      hk hmn hmPos hmSpec.2
    have hkLeInitial : (k : ℝ) ≤ fordDeltaInitial35 k := by
      unfold fordDeltaInitial35
      nlinarith [show (1000 : ℝ) ≤ k by exact_mod_cast hk]
    exact ⟨hn.1, hn.2.trans hkLeInitial⟩

/-- All arithmetic entry hypotheses of Lemma 3.5 hold at every term of the
canonical sequence. -/
theorem fordLemma35AdmissibleAt_rounded_all
    {k n : ℕ} (hk : 1000 ≤ k) :
    FordLemma35AdmissibleAt k (fordRSequence36 k) n := by
  have hb := fordDeltaSequence36_pos_le_initial (k := k) (n := n) hk
  by_cases hlarge : (k : ℝ) ≤ fordDeltaSequence36 k n
  · exact fordLemma35AdmissibleAt_rounded (by omega) hlarge hb.2
  · have hsmall : fordDeltaSequence36 k n ≤ (k : ℝ) := le_of_not_ge hlarge
    have h := fordLemma35Admissible_below hk hb.1 hsmall
    simpa [FordLemma35AdmissibleAt, fordRSequence36,
      fordDeltaSequence35_rounded_eq] using h

/-- Ford's canonical sequence supplies a genuine all-positive-endpoint
moment estimate at every source index in the recursion range.  The fixed
coefficient may depend on `k` and `n`, but the exponent is literal. -/
theorem fordLemma36_moment_bound_exists
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 1 ≤ n) (hnUpper : n ≤ k ^ 2) :
    ∃ C : ℝ, FordVinogradovMomentBound (n * k) k C
      (fordDeltaSequence36 k (n - 1)) := by
  have hlog := ford_log_k_lower hk
  have hlog0 : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have homegaLower : 1 / (3 * Real.log (k : ℝ)) ≤ (3 / 50 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 3 * Real.log (k : ℝ))]
    nlinarith
  have hmoment := ford_lemma_3_5_exponent_recursion
    (k := k) (n := n) (r := fordRSequence36 k)
    (eta := (53 / 50 : ℝ)) (omega := (3 / 50 : ℝ))
    (by omega) hnLower hnUpper
    (fun m _hm => fordLemma35AdmissibleAt_rounded_all hk)
    homegaLower (by norm_num) (by norm_num)
  simpa [fordDeltaSequence35_rounded_eq] using hmoment

/-- Exponent-and-moment form of the `k ≥ 1000` part of Ford Lemma 3.6.
The source index `n` is one-based. -/
theorem fordLemma36_moment_and_exponent
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 * k ≤ n)
    (hnRecursion : n ≤ k ^ 2)
    (hnSource : (n : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    ∃ C : ℝ,
      FordVinogradovMomentBound (n * k) k C
        (fordDeltaSequence36 k (n - 1)) ∧
      fordDeltaSequence36 k (n - 1) ≤
        (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
          (1 / 2 - 2 * (n : ℝ) / (k : ℝ) + 169 / (100 * (k : ℝ))) := by
  obtain ⟨C, hC⟩ := fordLemma36_moment_bound_exists hk (by omega) hnRecursion
  refine ⟨C, hC, ?_⟩
  have hindex : n - 1 + 1 = n := by omega
  have hsource : ((((n - 1) + 1 : ℕ) : ℝ)) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1 := by
    rw [hindex]
    exact hnSource
  simpa [hindex] using
    (fordLemma36_delta_exponent hk (n := n - 1) (by omega) hsource)

/-- Ford's printed upper range is automatically contained in the recursion
range `n ≤ k²`; this removes a formal-only premise from the public form. -/
theorem fordLemma36_source_range_le_square
    {k n : ℕ} (hk : 1000 ≤ k)
    (hnSource : (n : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    n ≤ k ^ 2 := by
  have hk0 : (0 : ℝ) < k := by positivity
  have harg : 0 < 3 * (k : ℝ) / 8 := by positivity
  have hlog := Real.log_le_sub_one_of_pos harg
  have hsourceUpper :
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1 ≤
        (k : ℝ) ^ 2 := by
    have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [sq_nonneg (k : ℝ)]
  have hnReal : (n : ℝ) ≤ ((k ^ 2 : ℕ) : ℝ) := by
    norm_num [Nat.cast_pow]
    exact hnSource.trans hsourceUpper
  exact_mod_cast hnReal

/-- Source-faithful `k ≥ 1000` form of Ford Lemma 3.6, with no auxiliary
recursion-range hypothesis. -/
theorem fordLemma36_native
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 * k ≤ n)
    (hnSource : (n : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    ∃ C : ℝ,
      FordVinogradovMomentBound (n * k) k C
        (fordDeltaSequence36 k (n - 1)) ∧
      fordDeltaSequence36 k (n - 1) ≤
        (3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
          (1 / 2 - 2 * (n : ℝ) / (k : ℝ) + 169 / (100 * (k : ℝ))) :=
  fordLemma36_moment_and_exponent hk hnLower
    (fordLemma36_source_range_le_square hk hnSource) hnSource

#print axioms fordLemma35Admissible_below
#print axioms fordDeltaSequence36_pos_le_initial
#print axioms fordLemma35AdmissibleAt_rounded_all
#print axioms fordLemma36_moment_bound_exists
#print axioms fordLemma36_moment_and_exponent
#print axioms fordLemma36_source_range_le_square
#print axioms fordLemma36_native

end

end GafniTao
