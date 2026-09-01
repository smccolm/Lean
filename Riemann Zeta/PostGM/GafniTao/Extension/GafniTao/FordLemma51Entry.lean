import GafniTao.FordTaylorPhase

/-!
# Entry to Ford's Lemma 5.1

This module applies the exact phase remainder to Ford's source ranges
`1 ≤ a ≤ M₁`, `b ∈ B`, `ab/z ≤ M₁M₂/N`.  It proves both the unnormalized
double-sum error and the normalized term occurring in equation (5.2), with
the source denominator `k+1` retained.
-/

open Finset

namespace GafniTao

noncomputable section

/-- The Taylor replacement error in the double sum preceding Ford (5.2). -/
theorem ford_equation_5_2_taylor_error
    {k M₁ M₂ N : ℕ} {B : Finset ℕ} {t z : ℝ}
    (hN : 0 < N) (hz : (N : ℝ) ≤ z) (hM : M₁ * M₂ ≤ N)
    (hB : ∀ b ∈ B, b ≤ M₂) (ht : 0 ≤ t) :
    ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
          fordLogOscillation t (((a * b : ℕ) : ℝ) / z) -
        ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
          fordTaylorOscillation k t (((a * b : ℕ) : ℝ) / z)‖ ≤
      (M₁ : ℝ) * B.card *
        (t * (((((M₁ * M₂ : ℕ) : ℝ) / N) ^ (k + 1)) / (k + 1))) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hzpos : 0 < z := hNreal.trans_le hz
  have hx (a : ℕ) (ha : a ∈ Finset.Icc 1 M₁)
      (b : ℕ) (hb : b ∈ B) :
      (((a * b : ℕ) : ℝ) / z) ∈ Set.Icc (0 : ℝ) 1 := by
    have ha' := Finset.mem_Icc.mp ha
    have habNat : a * b ≤ M₁ * M₂ := Nat.mul_le_mul ha'.2 (hB b hb)
    have habReal : (((a * b : ℕ) : ℝ)) ≤ ((M₁ * M₂ : ℕ) : ℝ) := by
      exact_mod_cast habNat
    have hMNreal : (((M₁ * M₂ : ℕ) : ℝ)) ≤ (N : ℝ) := by
      exact_mod_cast hM
    constructor
    · exact div_nonneg (by positivity) hzpos.le
    · rw [div_le_one hzpos]
      exact habReal.trans (hMNreal.trans hz)
  have hratio (a : ℕ) (ha : a ∈ Finset.Icc 1 M₁)
      (b : ℕ) (hb : b ∈ B) :
      (((a * b : ℕ) : ℝ) / z) ≤ (((M₁ * M₂ : ℕ) : ℝ) / N) := by
    have ha' := Finset.mem_Icc.mp ha
    have habNat : a * b ≤ M₁ * M₂ := Nat.mul_le_mul ha'.2 (hB b hb)
    have habReal : (((a * b : ℕ) : ℝ)) ≤ ((M₁ * M₂ : ℕ) : ℝ) := by
      exact_mod_cast habNat
    calc
      (((a * b : ℕ) : ℝ) / z) ≤ (((M₁ * M₂ : ℕ) : ℝ) / z) :=
        div_le_div_of_nonneg_right habReal hzpos.le
      _ ≤ (((M₁ * M₂ : ℕ) : ℝ) / N) := by
        exact div_le_div_of_nonneg_left (by positivity) hNreal hz
  have hpow (a : ℕ) (ha : a ∈ Finset.Icc 1 M₁)
      (b : ℕ) (hb : b ∈ B) :
      ((((a * b : ℕ) : ℝ) / z) ^ (k + 1)) ≤
        ((((M₁ * M₂ : ℕ) : ℝ) / N) ^ (k + 1)) := by
    exact pow_le_pow_left₀ (hx a ha b hb).1 (hratio a ha b hb) _
  have hmain := ford_taylor_phase_double_sum_uniform
    (Finset.Icc 1 M₁) B k
    (fun a b => (((a * b : ℕ) : ℝ) / z)) ht hx hpow
  simpa [Nat.card_Icc] using hmain

/-- The fully normalized Taylor error in Ford (5.2). -/
theorem ford_equation_5_2_normalized_taylor_error
    {k M₁ M₂ N : ℕ} {B : Finset ℕ} {t z : ℝ}
    (hN : 0 < N) (hM₁ : 0 < M₁) (hBne : B.Nonempty)
    (hz : (N : ℝ) ≤ z) (hM : M₁ * M₂ ≤ N)
    (hB : ∀ b ∈ B, b ≤ M₂) (ht : 0 ≤ t) :
    ((N : ℝ) / ((M₁ : ℝ) * B.card)) *
      ‖∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
          fordLogOscillation t (((a * b : ℕ) : ℝ) / z) -
        ∑ a ∈ Finset.Icc 1 M₁, ∑ b ∈ B,
          fordTaylorOscillation k t (((a * b : ℕ) : ℝ) / z)‖ ≤
      t * (((M₁ * M₂ : ℕ) : ℝ) ^ (k + 1)) /
        (((k + 1 : ℕ) : ℝ) * (N : ℝ) ^ k) := by
  have hbase := ford_equation_5_2_taylor_error (k := k) hN hz hM hB ht
  have hM₁real : 0 < (M₁ : ℝ) := by exact_mod_cast hM₁
  have hBreal : 0 < (B.card : ℝ) := by exact_mod_cast hBne.card_pos
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hfactor : 0 ≤ (N : ℝ) / ((M₁ : ℝ) * B.card) := by positivity
  refine (mul_le_mul_of_nonneg_left hbase hfactor).trans_eq ?_
  rw [div_pow, pow_succ]
  field_simp
  push_cast
  ring

#print axioms ford_equation_5_2_taylor_error
#print axioms ford_equation_5_2_normalized_taylor_error

end

end GafniTao
