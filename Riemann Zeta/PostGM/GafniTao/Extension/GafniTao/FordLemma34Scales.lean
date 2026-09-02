import GafniTao.FordLemma32Real

/-!
# Ford Lemma 3.4: physical real scales

This file defines the literal scales in the proof of Ford's Lemma 3.4 and
proves their algebraic relations.  In particular, `Q_i` is not an unrelated
formal parameter: it is tied to `P` and the complete prefix of the recursively
defined `phi` schedule.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

def fordPhiPrefix {k r j : ℕ} {delta : ℝ}
    (Φ : FordPhiSchedule k r j delta) (i : ℕ) : ℝ :=
  ∑ n ∈ Finset.range i, Φ.phi (n + 1)

def fordMScale {k r j : ℕ} {delta : ℝ}
    (P : ℝ) (Φ : FordPhiSchedule k r j delta) (i : ℕ) : ℝ :=
  P ^ Φ.phi i

def fordQScale {k r j : ℕ} {delta : ℝ}
    (P : ℝ) (Φ : FordPhiSchedule k r j delta) (i : ℕ) : ℝ :=
  P ^ (1 - fordPhiPrefix Φ i)

@[simp] theorem fordPhiPrefix_zero
    {k r j : ℕ} {delta : ℝ} (Φ : FordPhiSchedule k r j delta) :
    fordPhiPrefix Φ 0 = 0 := by
  simp [fordPhiPrefix]

theorem fordPhiPrefix_succ
    {k r j : ℕ} {delta : ℝ} (Φ : FordPhiSchedule k r j delta) (i : ℕ) :
    fordPhiPrefix Φ (i + 1) = fordPhiPrefix Φ i + Φ.phi (i + 1) := by
  simp [fordPhiPrefix, Finset.sum_range_succ]

@[simp] theorem fordQScale_zero
    {k r j : ℕ} {delta : ℝ} {P : ℝ}
    (Φ : FordPhiSchedule k r j delta) :
    fordQScale P Φ 0 = P := by
  simp [fordQScale, fordPhiPrefix, Real.rpow_one]

theorem fordMScale_pos
    {k r j : ℕ} {delta P : ℝ} (hP : 0 < P)
    (Φ : FordPhiSchedule k r j delta) (i : ℕ) :
    0 < fordMScale P Φ i := by
  exact Real.rpow_pos_of_pos hP _

theorem fordQScale_pos
    {k r j : ℕ} {delta P : ℝ} (hP : 0 < P)
    (Φ : FordPhiSchedule k r j delta) (i : ℕ) :
    0 < fordQScale P Φ i := by
  exact Real.rpow_pos_of_pos hP _

/-- The exact quotient relation `Q_i / M_{i+1}=Q_{i+1}`. -/
theorem fordQScale_div_MScale
    {k r j : ℕ} {delta P : ℝ} (hP : 0 < P)
    (Φ : FordPhiSchedule k r j delta) (i : ℕ) :
    fordQScale P Φ i / fordMScale P Φ (i + 1) =
      fordQScale P Φ (i + 1) := by
  change P ^ (1 - fordPhiPrefix Φ i) / P ^ Φ.phi (i + 1) =
    P ^ (1 - fordPhiPrefix Φ (i + 1))
  rw [fordPhiPrefix_succ]
  rw [← Real.rpow_sub hP]
  congr 1
  ring

/-- Equivalent multiplicative form of the scale recurrence. -/
theorem fordQScale_eq_MScale_mul_succ
    {k r j : ℕ} {delta P : ℝ} (hP : 0 < P)
    (Φ : FordPhiSchedule k r j delta) (i : ℕ) :
    fordQScale P Φ i = fordMScale P Φ (i + 1) *
      fordQScale P Φ (i + 1) := by
  have hM := fordMScale_pos hP Φ (i + 1)
  calc
    fordQScale P Φ i =
        (fordQScale P Φ i / fordMScale P Φ (i + 1)) *
          fordMScale P Φ (i + 1) := (div_mul_cancel₀ _ hM.ne').symm
    _ = fordQScale P Φ (i + 1) * fordMScale P Φ (i + 1) := by
      rw [fordQScale_div_MScale hP]
    _ = fordMScale P Φ (i + 1) * fordQScale P Φ (i + 1) := mul_comm _ _

theorem fordPhiPrefix_le_index_div_r
    {k r j : ℕ} {delta : ℝ} (Φ : FordPhiSchedule k r j delta)
    (hupper : ∀ n, 1 ≤ n → n ≤ j → Φ.phi n ≤ 1 / (r : ℝ))
    {i : ℕ} (hij : i ≤ j) :
    fordPhiPrefix Φ i ≤ (i : ℝ) / r := by
  calc
    fordPhiPrefix Φ i ≤ ∑ _n ∈ Finset.range i, (1 / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hni : n < i := Finset.mem_range.mp hn
      exact hupper (n + 1) (by omega) (by omega)
    _ = (i : ℝ) / r := by
      simp [div_eq_mul_inv, mul_comm]

theorem fordMScale_rpow_nat
    {k r j : ℕ} {delta P : ℝ} (hP : 0 ≤ P)
    (Φ : FordPhiSchedule k r j delta) (i n : ℕ) :
    (fordMScale P Φ i) ^ n = P ^ (Φ.phi i * n) := by
  rw [fordMScale, ← Real.rpow_natCast, ← Real.rpow_mul hP]

/-- The terminal source identity `M_j^r=P`. -/
theorem fordMScale_terminal_rpow
    {k r j : ℕ} {delta P : ℝ} (hP : 0 < P)
    (hr : 1 ≤ r) (Φ : FordPhiSchedule k r j delta) :
    (fordMScale P Φ j) ^ r = P := by
  rw [fordMScale_rpow_nat hP.le, Φ.terminal]
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  have hexp : (1 / (r : ℝ)) * (r : ℝ) = 1 := by field_simp
  rw [hexp, Real.rpow_one]

theorem fordMScale_mono_exponent
    {k r j : ℕ} {delta P : ℝ} (hP : 1 ≤ P)
    (Φ : FordPhiSchedule k r j delta) {a b : ℕ}
    (hab : Φ.phi a ≤ Φ.phi b) :
    fordMScale P Φ a ≤ fordMScale P Φ b := by
  exact Real.rpow_le_rpow_of_exponent_le hP hab

#print axioms fordPhiPrefix_succ
#print axioms fordQScale_div_MScale
#print axioms fordQScale_eq_MScale_mul_succ
#print axioms fordPhiPrefix_le_index_div_r
#print axioms fordMScale_terminal_rpow

end

end GafniTao
