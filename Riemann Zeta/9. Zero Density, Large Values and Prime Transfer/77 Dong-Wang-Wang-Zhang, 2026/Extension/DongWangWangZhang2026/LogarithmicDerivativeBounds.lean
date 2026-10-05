import DongWangWangZhang2026.ZetaSum
import GuthMaynard.LogarithmicKernel

/-!
# Reused finite first- and second-derivative prefix estimates

The two proof bodies are adapted verbatim apart from their declaration
names from this repository's foundation TerminalTypeI and
TypeIFiniteEstimates modules. Their larger density/dichotomy imports are
unnecessary: only the proved finite LogarithmicKernel closure is used.
The source sum has the opposite phase sign, bridged by conjugation later.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Finset Set
open RiemannZeta.GuthMaynard
open scoped BigOperators

/-- Uniform first-derivative cancellation for every prefix beginning just
to the right of `A`.  The deliberately generous constant is uniform in the
prefix length. -/
theorem source_logarithmic_prefix_first_derivative
    (A L : ℕ) (t : ℝ) (hA : 0 < A) (hL : L ≤ A)
    (htOne : 1 ≤ t) (htA : t ≤ (A : ℝ)) :
    ‖∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
      6 * Real.pi * (A : ℝ) / t := by
  by_cases hL0 : L = 0
  · subst L
    simp only [Finset.range_zero, Finset.sum_empty, norm_zero]
    positivity
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have hAReal : 0 < (A : ℝ) := by exact_mod_cast hA
  let δ : ℝ := t / (3 * (A : ℝ))
  have hδ : 0 < δ := by
    dsimp only [δ]
    positivity
  have hinc (n : ℕ) (hn : n ≤ L - 1) :
      let m := A + 1 + n
      δ ≤ logarithmicPhase t (m + 1) - logarithmicPhase t m + 2 * Real.pi ∧
        logarithmicPhase t (m + 1) - logarithmicPhase t m + 2 * Real.pi ≤
          2 * Real.pi - δ := by
    dsimp only
    let m := A + 1 + n
    have hm : 0 < m := by dsimp only [m]; omega
    have hmLower : A ≤ m := by dsimp only [m]; omega
    have hmUpper : m + 1 ≤ 3 * A := by
      dsimp only [m]
      omega
    have hlogs :
        1 / ((m : ℝ) + 1) ≤
            Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ∧
          Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤
            1 / (m : ℝ) := by
      have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
      have hsuccReal : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
      have hratio : 0 < (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by positivity
      have hlog :
          Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) =
            Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) :=
        Real.log_div hsuccReal.ne' hmReal.ne'
      constructor
      · calc
          1 / ((m : ℝ) + 1) =
              1 - ((((m + 1 : ℕ) : ℝ) / (m : ℝ))⁻¹) := by
                push_cast
                field_simp [hmReal.ne']
                ring
          _ ≤ Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) :=
            Real.one_sub_inv_le_log_of_pos hratio
          _ = Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) := hlog
      · rw [← hlog]
        calc
          Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) ≤
              ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 :=
            Real.log_le_sub_one_of_pos hratio
          _ = 1 / (m : ℝ) := by
            push_cast
            field_simp [hmReal.ne']
            ring
    have hphase :
        logarithmicPhase t (m + 1) - logarithmicPhase t m =
          -t * (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
      simp only [logarithmicPhase, Nat.cast_add, Nat.cast_one]
      ring
    rw [hphase]
    have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmLowerReal : (A : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmLower
    have hmUpperReal : ((m : ℝ) + 1) ≤ 3 * (A : ℝ) := by
      exact_mod_cast hmUpper
    have htOverM : t / (m : ℝ) ≤ 1 := by
      rw [div_le_one hmReal]
      exact htA.trans hmLowerReal
    have hdeltaLeThird : δ ≤ 1 / 3 := by
      dsimp only [δ]
      rw [div_le_iff₀ (by positivity : 0 < 3 * (A : ℝ))]
      nlinarith
    have hdeltaLog : δ ≤ t *
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) := by
      have hrecip : 1 / (3 * (A : ℝ)) ≤ 1 / ((m : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hmUpperReal
      dsimp only [δ]
      simpa only [div_eq_mul_inv, one_mul] using
        (mul_le_mul_of_nonneg_left hrecip (zero_le_one.trans htOne)).trans
          (mul_le_mul_of_nonneg_left hlogs.1 (zero_le_one.trans htOne))
    constructor
    · have hlogUpper : t *
          (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) ≤ 1 := by
        exact (mul_le_mul_of_nonneg_left hlogs.2 (zero_le_one.trans htOne)).trans (by
          simpa only [div_eq_mul_inv, one_mul] using htOverM)
      nlinarith [Real.pi_gt_three]
    · linarith
  have hmono : ∀ n < L - 1,
      logarithmicPhase t (A + 1 + n + 1) - logarithmicPhase t (A + 1 + n) ≤
        logarithmicPhase t (A + 1 + n + 2) -
          logarithmicPhase t (A + 1 + n + 1) := by
    intro n hn
    let m := A + 1 + n
    have hm : 0 < m := by dsimp only [m]; omega
    have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
    have hmOneReal : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
    have hratioLe :
        ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
          ((m + 1 : ℕ) : ℝ) / (m : ℝ) := by
      rw [div_le_div_iff₀ hmOneReal hmReal]
      push_cast
      nlinarith
    have hlogLe := Real.strictMonoOn_log.monotoneOn
      (by show 0 < ((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ); positivity)
      (by show 0 < ((m + 1 : ℕ) : ℝ) / (m : ℝ); positivity) hratioLe
    have hphaseOne :
        logarithmicPhase t (m + 1) - logarithmicPhase t m =
          -t * Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
      rw [Real.log_div (by positivity) hmReal.ne']
      simp only [logarithmicPhase, Nat.cast_add, Nat.cast_one]
      ring
    have hphaseTwo :
        logarithmicPhase t (m + 2) - logarithmicPhase t (m + 1) =
          -t * Real.log (((m + 2 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
      rw [Real.log_div (by positivity) hmOneReal.ne']
      simp only [logarithmicPhase, Nat.cast_add, Nat.cast_ofNat]
      ring_nf
    have hfinal := mul_le_mul_of_nonpos_left hlogLe (by linarith : -t ≤ 0)
    rw [← hphaseOne, ← hphaseTwo] at hfinal
    simpa only [m, Nat.cast_add, Nat.cast_one, add_assoc] using hfinal
  have hKL := kusminLandau_interval (fun n : ℕ => logarithmicPhase t n)
    (A + 1) (L - 1) (-1) δ hδ
    (fun n hn => by
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add,
        Nat.cast_add, Nat.cast_one, add_assoc] using (hinc n hn).1)
    (fun n hn => by
      simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul, sub_neg_eq_add,
        Nat.cast_add, Nat.cast_one, add_assoc] using (hinc n hn).2)
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hmono n hn)
  have hpred : L - 1 + 1 = L := by omega
  rw [hpred] at hKL
  calc
    ‖∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
        2 * Real.pi / δ := by
          simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hKL
    _ = 6 * Real.pi * (A : ℝ) / t := by
      dsimp only [δ]
      field_simp [show t ≠ 0 by linarith, hAReal.ne']
      ring

/-- The finite van der Corput B-process uniformly controls every prefix of a
medium logarithmic block.  Unlike the full-kernel lemma, this prefix form is
strong enough for Abel summation with the weight `n^{-σ}`. -/
theorem source_logarithmic_prefix_second_derivative
    (A L : ℕ) (t : ℝ) (hA : 0 < A) (hL : L ≤ A)
    (hAt : (A : ℝ) ≤ t) (htA : t ≤ (A : ℝ) ^ 2) :
    ‖∑ n ∈ Finset.range L,
        unitaryPhase (logarithmicPhase t (A + 1 + n))‖ ≤
      100 * Real.sqrt t := by
  by_cases hL0 : L = 0
  · subst L
    simp
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have ht : 0 < t := lt_of_lt_of_le (by exact_mod_cast hA) hAt
  have hlambda : 0 < t / (9 * (A : ℝ) ^ 2) := by positivity
  have hcurvLower : ∀ n < L - 1,
      t / (9 * (A : ℝ) ^ 2) ≤
        (logarithmicPhase t (A + 1 + (n + 2)) -
          logarithmicPhase t (A + 1 + (n + 1))) -
          (logarithmicPhase t (A + 1 + (n + 1)) -
            logarithmicPhase t (A + 1 + n)) := by
    intro n hn
    exact (logarithmicPhase_secondDifference_bounds A n t hA ht
      (lt_of_lt_of_le hn (Nat.sub_le_sub_right hL 1))).1
  have hcurvUpper : ∀ n < L - 1,
      (logarithmicPhase t (A + 1 + (n + 2)) -
          logarithmicPhase t (A + 1 + (n + 1))) -
          (logarithmicPhase t (A + 1 + (n + 1)) -
            logarithmicPhase t (A + 1 + n)) ≤ t / (A : ℝ) ^ 2 := by
    intro n hn
    exact (logarithmicPhase_secondDifference_bounds A n t hA ht
      (lt_of_lt_of_le hn (Nat.sub_le_sub_right hL 1))).2
  have hB := vanDerCorput_B_process
    (fun n => logarithmicPhase t (A + 1 + n)) (L - 1)
    (t / (9 * (A : ℝ) ^ 2)) (t / (A : ℝ) ^ 2) hlambda
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.add_assoc] using
        hcurvLower n hn)
    (fun n hn => by
      simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.add_assoc] using
        hcurvUpper n hn)
  have hpred : L - 1 + 1 = L := by omega
  rw [hpred] at hB
  have hfirst :
      (((L - 1 : ℕ) : ℝ) * (t / (A : ℝ) ^ 2) / (2 * Real.pi) + 2) ≤
        (((A - 1 : ℕ) : ℝ) * (t / (A : ℝ) ^ 2) / (2 * Real.pi) + 2) := by
    gcongr
  have hsecondNonneg :
      0 ≤ 2 * Real.pi / Real.sqrt (t / (9 * (A : ℝ) ^ 2)) +
        2 * (Real.sqrt (t / (9 * (A : ℝ) ^ 2)) /
          (t / (9 * (A : ℝ) ^ 2)) + 1) := by positivity
  exact hB.trans <| (mul_le_mul_of_nonneg_right hfirst hsecondNonneg).trans
    (logarithmic_B_process_majorant_le A t hA hAt htA)


end
end DongWangWangZhang2026

