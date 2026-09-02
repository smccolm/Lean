import GafniTao.FordEquation61Real
import GafniTao.FordEquation67

/-!
# Ford's equation (6.7) at a real shift length

This is the finite Holder step applied to the exact real-cutoff equation
(6.1).  The moment still contains the actual integer cutoff `floor P`, while
the source prefactor and boundary losses retain `P`.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem ford_equation_6_7_real_cutoff
    {P : ℝ} {N R s : ℕ} {u t : ℝ}
    (hP : 1 ≤ P) (hN : 1 ≤ N) (hs : 1 ≤ s)
    (hRlower : N < R) (hR : R ≤ 2 * N) (hu : 0 < u) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) / P *
          (fordLemma63Moment ⌊P⌋₊ N u t s) ^ (1 / (2 * s : ℝ)) +
        (N : ℝ) / P + P := by
  have h61 := ford_equation_6_1_real_cutoff
    (P := P) (N := N) (R := R) (u := u) (t := t)
    hP hN hRlower hR hu
  let A := Finset.Ioc N (2 * N - 1)
  let f : ℕ → ℝ := fun n => ‖fordLemma63T ⌊P⌋₊ n u t‖
  have hrs : 1 ≤ 2 * s := by omega
  have hholder := ford_sum_le_card_rpow_mul_moment_root A f hrs
    (fun n hn => norm_nonneg _)
  have hcard : A.card ≤ N := by
    dsimp [A]
    rw [Nat.card_Ioc]
    omega
  have hexp : (0 : ℝ) ≤ 1 - 1 / (2 * s : ℝ) := by
    have hsR : (1 : ℝ) ≤ 2 * s := by exact_mod_cast hrs
    have hpos : (0 : ℝ) < 2 * s := lt_of_lt_of_le zero_lt_one hsR
    have hinv : 1 / (2 * s : ℝ) ≤ 1 := (div_le_one hpos).2 hsR
    linarith
  have hcardR : (A.card : ℝ) ≤ N := by exact_mod_cast hcard
  have hcardPow :
      (A.card : ℝ) ^ (1 - 1 / (2 * s : ℝ)) ≤
        (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcardR hexp
  have hsum :
      (∑ n ∈ Finset.Ioc N (2 * N - 1), ‖fordLemma63T ⌊P⌋₊ n u t‖) ≤
        (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) *
          (fordLemma63Moment ⌊P⌋₊ N u t s) ^ (1 / (2 * s : ℝ)) := by
    calc
      _ ≤ (A.card : ℝ) ^ (1 - 1 / (2 * s : ℝ)) *
          (∑ n ∈ A, f n ^ (2 * s)) ^ (1 / (2 * s : ℝ)) := by
        simpa only [A, f, Nat.cast_mul, Nat.cast_ofNat] using hholder
      _ ≤ (N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) *
          (∑ n ∈ A, f n ^ (2 * s)) ^ (1 / (2 * s : ℝ)) := by
        gcongr
      _ = _ := by rfl
  calc
    ‖fordShiftedExponentialSum N R u t‖ ≤
        (1 / P) *
            (∑ n ∈ Finset.Ioc N (2 * N - 1),
              ‖fordLemma63T ⌊P⌋₊ n u t‖) +
          (N : ℝ) / P + P := h61
    _ ≤ (1 / P) *
          ((N : ℝ) ^ (1 - 1 / (2 * s : ℝ)) *
            (fordLemma63Moment ⌊P⌋₊ N u t s) ^ (1 / (2 * s : ℝ))) +
          (N : ℝ) / P + P := by gcongr
    _ = _ := by ring

#print axioms ford_equation_6_7_real_cutoff

end

end GafniTao
