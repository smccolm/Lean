import GafniTao.FordLemma34Numerics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Ford Lemma 3.4: the explicit eta inequality

Ford uses `k ≥ 26` and `omega ≥ 1/(3 log k)` to absorb the `2^k`
alternative in the induction.  This file proves the underlying logarithmic
inequality with explicit constants; no numerical oracle is used.
-/

namespace GafniTao

noncomputable section

def fordEtaCore (k : ℕ) : ℝ :=
  ((k : ℝ) + 3) / (2 * (1 + 6 * Real.log k))

theorem fordEtaCore_step {k : ℕ} (hk : 26 ≤ k) :
    fordEtaCore k ≤ fordEtaCore (k + 1) := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hkp1 : (0 : ℝ) < k + 1 := by positivity
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  have hlog2 : (69 / 100 : ℝ) < Real.log 2 :=
    (by norm_num : (69 / 100 : ℝ) < 0.6931471803) |>.trans Real.log_two_gt_d9
  have hk16 : (16 : ℝ) ≤ k := by exact_mod_cast (show 16 ≤ k by omega)
  have hlogLower : 4 * Real.log 2 ≤ Real.log (k : ℝ) := by
    calc
      4 * Real.log 2 = Real.log ((2 : ℝ) ^ 4) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) (by norm_num at hk16 ⊢; exact hk16)
  have hlogOne : Real.log (1 + (k : ℝ)⁻¹) ≤ (k : ℝ)⁻¹ := by
    have hpos : 0 < 1 + (k : ℝ)⁻¹ := by positivity
    simpa using Real.log_le_sub_one_of_pos hpos
  have hlogOneNonneg : 0 ≤ Real.log (1 + (k : ℝ)⁻¹) :=
    Real.log_nonneg (by
      have : 0 ≤ (k : ℝ)⁻¹ := inv_nonneg.mpr hk0.le
      linarith)
  have hklogOne : (k : ℝ) * Real.log (1 + (k : ℝ)⁻¹) ≤ 1 := by
    calc
      (k : ℝ) * Real.log (1 + (k : ℝ)⁻¹) ≤ k * (k : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hlogOne hk0.le
      _ = 1 := mul_inv_cancel₀ hk0.ne'
  have hinvK : (k : ℝ)⁻¹ ≤ 1 / 26 := by
    simpa [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 26)
        (by exact_mod_cast hk : (26 : ℝ) ≤ k))
  have hlogOneSmall : Real.log (1 + (k : ℝ)⁻¹) ≤ 1 / 26 :=
    hlogOne.trans hinvK
  have hbudget :
      6 * ((k : ℝ) + 3) * Real.log (1 + (k : ℝ)⁻¹) ≤
        1 + 6 * Real.log k := by
    have hleft :
        6 * ((k : ℝ) + 3) * Real.log (1 + (k : ℝ)⁻¹) ≤
          6 * (1 + 3 / 26) := by
      calc
        6 * ((k : ℝ) + 3) * Real.log (1 + (k : ℝ)⁻¹) =
            6 * ((k : ℝ) * Real.log (1 + (k : ℝ)⁻¹) +
              3 * Real.log (1 + (k : ℝ)⁻¹)) := by ring
        _ ≤ 6 * (1 + 3 / 26) := by
          gcongr
          exact mul_le_mul_of_nonneg_left (by simpa [one_div] using hlogOneSmall) (by norm_num)
    have hright : 6 * (1 + 3 / 26 : ℝ) ≤ 1 + 6 * Real.log k := by
      nlinarith
    exact hleft.trans hright
  have hlogSucc : Real.log ((k + 1 : ℕ) : ℝ) =
      Real.log (k : ℝ) + Real.log (1 + (k : ℝ)⁻¹) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    rw [show (k : ℝ) + 1 = (k : ℝ) * (1 + (k : ℝ)⁻¹) by
      field_simp]
    exact Real.log_mul hk0.ne' (by positivity : (1 + (k : ℝ)⁻¹) ≠ 0)
  have hden1 : 0 < 2 * (1 + 6 * Real.log (k : ℝ)) := by positivity
  have hden2 : 0 < 2 * (1 + 6 * Real.log ((k + 1 : ℕ) : ℝ)) := by
    have : 0 < Real.log (((k + 1 : ℕ) : ℝ)) :=
      Real.log_pos (by exact_mod_cast (show 1 < k + 1 by omega))
    positivity
  unfold fordEtaCore
  rw [div_le_div_iff₀ hden1 hden2, hlogSucc]
  norm_num only [Nat.cast_add, Nat.cast_one]
  nlinarith [hbudget]

theorem fordEtaCore_monotone_from_26 {k : ℕ} (hk : 26 ≤ k) :
    fordEtaCore 26 ≤ fordEtaCore k := by
  exact Nat.le_induction (le_rfl)
    (fun n hn hprev => hprev.trans (fordEtaCore_step hn)) k hk

theorem log_two_le_fordEtaCore_26 :
    Real.log 2 ≤ fordEtaCore 26 := by
  have hlog2 : Real.log 2 ≤ (0.6931471808 : ℝ) := Real.log_two_lt_d9.le
  have hlog26 : Real.log (26 : ℝ) < 3 * (1.0986122888 : ℝ) := by
    calc
      Real.log (26 : ℝ) < Real.log (27 : ℝ) :=
        Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
      _ = 3 * Real.log 3 := by
        rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]
        norm_num
      _ < 3 * (1.0986122888 : ℝ) := by
        gcongr
        exact Real.log_three_lt_d9
  have hdenPos : 0 < 2 * (1 + 6 * Real.log (26 : ℝ)) := by
    have : 0 < Real.log (26 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hdenUpper :
      2 * (1 + 6 * Real.log (26 : ℝ)) ≤
        2 * (1 + 6 * (3 * (1.0986122888 : ℝ))) := by
    gcongr
  have hprod :
      Real.log 2 * (2 * (1 + 6 * Real.log (26 : ℝ))) ≤
        (0.6931471808 : ℝ) *
          (2 * (1 + 6 * (3 * (1.0986122888 : ℝ)))) :=
    mul_le_mul hlog2 hdenUpper (by positivity) (by norm_num)
  have hnum :
      (0.6931471808 : ℝ) *
          (2 * (1 + 6 * (3 * (1.0986122888 : ℝ)))) < 29 := by
    norm_num
  unfold fordEtaCore
  norm_num only [Nat.cast_ofNat]
  exact (le_div_iff₀ hdenPos).2 (hprod.trans hnum.le)

theorem log_two_le_ford_eta_power_log
    {k : ℕ} (hk : 26 ≤ k) :
    Real.log 2 ≤
      (((k : ℝ) + 3) / 4) *
        Real.log (1 + 1 / (3 * Real.log k)) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hlogk : 0 < Real.log (k : ℝ) := Real.log_pos hk1
  let x : ℝ := 1 / (3 * Real.log k)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hlogLower := Real.le_log_one_add_of_nonneg hx
  have hcoreEq :
      (((k : ℝ) + 3) / 4) * (2 * x / (x + 2)) = fordEtaCore k := by
    dsimp [x, fordEtaCore]
    field_simp
    ring
  calc
    Real.log 2 ≤ fordEtaCore 26 := log_two_le_fordEtaCore_26
    _ ≤ fordEtaCore k := fordEtaCore_monotone_from_26 hk
    _ = (((k : ℝ) + 3) / 4) * (2 * x / (x + 2)) := hcoreEq.symm
    _ ≤ (((k : ℝ) + 3) / 4) * Real.log (1 + x) := by
      exact mul_le_mul_of_nonneg_left hlogLower (by positivity)
    _ = (((k : ℝ) + 3) / 4) *
        Real.log (1 + 1 / (3 * Real.log k)) := by rfl

theorem two_le_ford_eta_base_power
    {k : ℕ} (hk : 26 ≤ k) :
    (2 : ℝ) ≤
      (1 + 1 / (3 * Real.log k)) ^ (((k : ℝ) + 3) / 4) := by
  have hbase : 0 < 1 + 1 / (3 * Real.log (k : ℝ)) := by
    have : 0 < Real.log (k : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    positivity
  rw [Real.le_rpow_iff_log_le (by norm_num) hbase]
  exact log_two_le_ford_eta_power_log hk

/-- The exact absorption used after equation (3.10): under Ford's lower
bound on `omega`, the eta factor dominates `2^k`. -/
theorem two_pow_le_ford_eta_absorption
    {k s : ℕ} {omega eta : ℝ}
    (hk : 26 ≤ k) (hks : k ≤ s)
    (homega : 1 / (3 * Real.log k) ≤ omega)
    (heta : eta = 1 + omega) :
    (2 : ℝ) ^ k ≤
      eta ^ ((s : ℝ) + ((k : ℝ) ^ 2 - k) / 4) := by
  let b : ℝ := 1 + 1 / (3 * Real.log k)
  let a : ℝ := ((k : ℝ) + 3) / 4
  let e : ℝ := (s : ℝ) + ((k : ℝ) ^ 2 - k) / 4
  have hlogk : 0 < Real.log (k : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < k by omega))
  have hb1 : 1 ≤ b := by
    dsimp [b]
    have : 0 ≤ 1 / (3 * Real.log (k : ℝ)) := by positivity
    linarith
  have hb0 : 0 ≤ b := hb1.trans' zero_le_one
  have hetaBase : b ≤ eta := by
    rw [heta]
    dsimp [b]
    linarith
  have heta1 : 1 ≤ eta := hb1.trans hetaBase
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hak0 : 0 ≤ a * (k : ℝ) := mul_nonneg ha0 (Nat.cast_nonneg k)
  have hae : a * (k : ℝ) ≤ e := by
    dsimp [a, e]
    have hksR : (k : ℝ) ≤ s := by exact_mod_cast hks
    nlinarith
  have htwo : (2 : ℝ) ≤ b ^ a := by
    simpa [b, a] using two_le_ford_eta_base_power hk
  calc
    (2 : ℝ) ^ k ≤ (b ^ a) ^ k :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo k
    _ = b ^ (a * (k : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]
    _ ≤ eta ^ (a * (k : ℝ)) :=
      Real.rpow_le_rpow hb0 hetaBase hak0
    _ ≤ eta ^ e := Real.rpow_le_rpow_of_exponent_le heta1 hae
    _ = eta ^ ((s : ℝ) + ((k : ℝ) ^ 2 - k) / 4) := rfl

#print axioms fordEtaCore_step
#print axioms fordEtaCore_monotone_from_26
#print axioms log_two_le_fordEtaCore_26
#print axioms log_two_le_ford_eta_power_log
#print axioms two_le_ford_eta_base_power
#print axioms two_pow_le_ford_eta_absorption

end

end GafniTao
