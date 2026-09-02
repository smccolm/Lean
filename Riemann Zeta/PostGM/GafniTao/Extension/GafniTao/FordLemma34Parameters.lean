import GafniTao.FordLemma33Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Ford Lemma 3.4: the source recurrence and exponent ledger

This file records the backwards `phi` recurrence in Ford Lemma 3.4 and
kernel-checks the two exact exponent cancellations used in the iteration.
All powers in the analytic statement are real powers, so the parameter
ledger is kept in `ℝ` from the outset.
-/

namespace GafniTao

noncomputable section

/-- One backwards step in the `phi_J` recurrence of Ford Lemma 3.4. -/
def fordPhiStep (k r J : ℕ) (delta next : ℝ) : ℝ :=
  1 / (2 * (r : ℝ)) +
    (((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J - 2 * delta) /
      (4 * k * r)) * next

/-- The terminal value `phi_j=1/r` and the exact backwards recurrence.
The function is deliberately total on naturals; only indices `1 ≤ J ≤ j`
are used by the source proof. -/
structure FordPhiSchedule (k r j : ℕ) (delta : ℝ) where
  phi : ℕ → ℝ
  terminal : phi j = 1 / (r : ℝ)
  recurrence : ∀ J, 1 ≤ J → J < j →
    phi J = fordPhiStep k r J delta (phi (J + 1))

theorem ford_square_pred_mono {a b : ℕ} (hab : a ≤ b) :
    a * (a - 1) ≤ b * (b - 1) := by
  exact Nat.mul_le_mul hab (Nat.sub_le_sub_right hab 1)

/-- Ford's assertion following (3.8): every recursively defined `phi_i` is
at most `1/r`.  The proof uses the advertised lower bound on every `phi_i`;
when the affine coefficient is negative that positivity controls the sign,
and when it is nonnegative the `(3.8)` inequality controls its size. -/
theorem FordPhiSchedule.le_inv_r
    {k r j : ℕ} {delta : ℝ} (Φ : FordPhiSchedule k r j delta)
    (hk : 1 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k) (hj : 2 ≤ j)
    (h38 : (((j - 1) * (j - 2) : ℕ) : ℝ) ≤
      2 * delta - (((k - r) * (k - r + 1) : ℕ) : ℝ))
    (hlower : ∀ i, 1 ≤ i → i ≤ j →
      1 / ((k + 1 : ℕ) : ℝ) ≤ Φ.phi i) :
    ∀ i, 1 ≤ i → i ≤ j → Φ.phi i ≤ 1 / (r : ℝ) := by
  intro i hi hij
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  refine Nat.decreasingInduction (motive := fun i _ =>
    1 ≤ i → Φ.phi i ≤ 1 / (r : ℝ)) ?_ ?_ hij hi
  · intro J hJlt ih hJpos
    have hJ1 : 1 ≤ J + 1 := by omega
    have hJj : J + 1 ≤ j := by omega
    have hrec := Φ.recurrence J hJpos (by omega)
    rw [hrec]
    unfold fordPhiStep
    let A : ℝ := (k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r +
      (J : ℝ) ^ 2 - J - 2 * delta
    have hJnat : J * (J - 1) ≤ (j - 1) * (j - 2) := by
      have hle : J ≤ j - 1 := by omega
      simpa [show j - 2 = (j - 1) - 1 by omega] using ford_square_pred_mono hle
    have hJreal : (J : ℝ) ^ 2 - J ≤
        (((j - 1) * (j - 2) : ℕ) : ℝ) := by
      calc
        (J : ℝ) ^ 2 - J = (J : ℝ) * ((J - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub hJpos]
          ring
        _ ≤ (((j - 1) * (j - 2) : ℕ) : ℝ) := by exact_mod_cast hJnat
    have hAupper : A ≤ 2 * (k : ℝ) * r := by
      dsimp [A]
      push_cast at h38 hJreal
      have hkr : ((k - r : ℕ) : ℝ) = (k : ℝ) - r := by
        rw [Nat.cast_sub hrk]
      rw [hkr] at h38
      nlinarith [sq_nonneg ((k : ℝ) - r)]
    have hphiNonneg : 0 ≤ Φ.phi (J + 1) := by
      have := hlower (J + 1) hJ1 hJj
      exact (by positivity : 0 ≤ 1 / (((k + 1 : ℕ) : ℝ))).trans this
    by_cases hA : 0 ≤ A
    · have hcoeff : 0 ≤ A / (4 * (k : ℝ) * r) := by positivity
      have hnext := ih hJ1
      calc
        1 / (2 * (r : ℝ)) + A / (4 * (k : ℝ) * r) * Φ.phi (J + 1) ≤
            1 / (2 * (r : ℝ)) + A / (4 * (k : ℝ) * r) * (1 / (r : ℝ)) := by
          gcongr
        _ ≤ 1 / (r : ℝ) := by
          field_simp
          nlinarith
    · have hprod : A / (4 * (k : ℝ) * r) * Φ.phi (J + 1) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg
          (le_of_not_ge hA) (by positivity)) hphiNonneg
      have hhalf : 1 / (2 * (r : ℝ)) ≤ 1 / (r : ℝ) := by
        exact one_div_le_one_div_of_le hrR (by linarith)
      linarith
  · intro _
    rw [Φ.terminal]

/-- Ford's exponent `lambda` in equation (3.10). -/
def fordLambda34 (s k : ℕ) (delta : ℝ) : ℝ :=
  2 * (s : ℝ) - ((k : ℝ) * (k + 1)) / 2 + delta

/-- Ford's updated permissible exponent `Delta'`. -/
def fordDeltaPrime34 (k r : ℕ) (delta phiOne : ℝ) : ℝ :=
  delta * (1 - phiOne) - k +
    phiOne / 2 * ((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r)

/-- The inner `M_{J+1}` exponent in the displayed cancellation following
equation (3.10). -/
theorem ford_lemma_3_4_inner_exponent_eq
    (s k r J : ℕ) (delta : ℝ) :
    (s : ℝ) - fordLambda34 s k delta / 2 +
        ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 4 =
      ((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r +
          (J : ℝ) ^ 2 - J - 2 * delta) / 4 := by
  unfold fordLambda34
  ring

/-- Exact algebraic cancellation produced by the backwards `phi` recurrence.
This is the equality immediately before Ford's assertion that the relevant
product of powers is one. -/
theorem ford_lemma_3_4_exponent_cancellation
    {k r J : ℕ} {delta phiJ phiNext : ℝ}
    (hk : 0 < k) (hr : 0 < r)
    (hphi : phiJ = fordPhiStep k r J delta phiNext) :
    (k : ℝ) / 2 - (k : ℝ) * r * phiJ +
        (((k : ℝ) * (k + 1)) / 2 - delta +
          ((r : ℝ) ^ 2 - r + (J : ℝ) ^ 2 - J) / 2) / 2 * phiNext = 0 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  rw [hphi]
  unfold fordPhiStep
  field_simp [hk0, hr0]
  ring

/-- The terminal exponent after the last application of Lemma 3.2 is exactly
the source exponent containing `Delta'`; no asymptotic `o(1)` is hidden here. -/
theorem ford_lemma_3_4_final_exponent_eq
    (s k r : ℕ) (delta phiOne : ℝ) :
    fordLambda34 s k delta + k +
        phiOne * (((k : ℝ) ^ 2 + k + (r : ℝ) ^ 2 - r) / 2 - delta) =
      2 * ((s : ℝ) + k) - ((k : ℝ) * (k + 1)) / 2 +
        fordDeltaPrime34 k r delta phiOne := by
  unfold fordLambda34 fordDeltaPrime34
  ring

#print axioms ford_lemma_3_4_inner_exponent_eq
#print axioms FordPhiSchedule.le_inv_r
#print axioms ford_lemma_3_4_exponent_cancellation
#print axioms ford_lemma_3_4_final_exponent_eq

end

end GafniTao
