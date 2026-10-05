import DongWangWangZhang2026.LogarithmicBlockBound
import DongWangWangZhang2026.MeanValueSmoothing

/-!
# Uniform cancellation of the actual finite sum

A halving induction sums the geometric block bounds and retains the
terminal partial block. There is no upper restriction on the cutoff.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Finset
open RiemannZeta.GuthMaynard

/-- The finite derivative prefix is the actual negative-height source increment. -/
theorem zetaSum_nat_increment_logarithmic (t : ℝ) (A N : ℕ) :
    zetaSum (A + N : ℕ) (-t) - zetaSum A (-t) =
      ∑ n ∈ Finset.range N, unitaryPhase (logarithmicPhase t (A + 1 + n)) := by
  rw [zetaSum_sub_eq_sum_Ioc (-t) (by exact_mod_cast Nat.le_add_right A N)]
  simp only [Nat.floor_natCast]
  have hI : Finset.Ioc A (A + N) = Finset.Ico (A + 1) (A + 1 + N) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro n _
  rw [zetaTerm_eq_cpow _ (by omega)]
  have h := unitaryPhase_logarithmicPhase_eq_cpow t (A + 1 + n) (by omega)
  simpa only [Nat.cast_add, Nat.cast_one, ofReal_neg] using h.symm

/-- Geometric aggregation of all actual integer-cutoff sums, including arbitrarily large x. -/
theorem norm_zetaSum_nat_twelfth_scale {Z : ℝ} (hZ : 2 ≤ Z) (M : ℕ) :
    ‖zetaSum M (Z ^ (12 : ℕ))‖ ≤
      1000 * (Z ^ (2 : ℕ) * Real.sqrt M + (M : ℝ) / Z) := by
  rw [← norm_zetaSum_neg]
  have hZ0 : 0 < Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases hMsmall : M ≤ 1
    · interval_cases M
      · simp [zetaSum]
      · have hZsq : 1 ≤ Z ^ (2 : ℕ) := one_le_pow₀ hZ1
        have hinv : 0 ≤ 1 / Z := by positivity
        simp only [Nat.cast_one, zetaSum, Nat.floor_one, Finset.Icc_self, Finset.sum_singleton,
          zetaTerm_one, norm_one, Real.sqrt_one, mul_one]
        linarith
    · have hM2 : 2 ≤ M := by omega
      let A := (M + 1) / 2
      let N := M - A
      have hA : 0 < A := by dsimp only [A]; omega
      have hAM : A < M := by dsimp only [A]; omega
      have hNA : N ≤ A := by dsimp only [N, A]; omega
      have hsum : A + N = M := by dsimp only [N]; omega
      have hMreal : (2 : ℝ) ≤ M := by exact_mod_cast hM2
      have hAupper : (A : ℝ) ≤ (3 / 4) * (M : ℝ) := by
        have h : 2 * A ≤ M + 1 := by dsimp only [A]; omega
        have h' : 2 * (A : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast h
        linarith
      have hroot : Real.sqrt (A : ℝ) ≤ (7 / 8) * Real.sqrt (M : ℝ) := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · positivity
        · have hsq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M)
          nlinarith only [hsq, hAupper, hMreal]
      have hroot' := mul_le_mul_of_nonneg_left hroot (sq_nonneg Z)
      have hdiv : (A : ℝ) / Z ≤ (3 / 4) * ((M : ℝ) / Z) := by
        have h := div_le_div_of_nonneg_right hAupper hZ0.le
        simpa only [mul_div_assoc] using h
      have hblock := source_logarithmic_prefix_uniform hZ A N hA hNA
      rw [← zetaSum_nat_increment_logarithmic, hsum] at hblock
      have hind := ih A hAM
      have hnorm : ‖zetaSum M (-(Z ^ (12 : ℕ)))‖ ≤
          ‖zetaSum A (-(Z ^ (12 : ℕ)))‖ +
            ‖zetaSum M (-(Z ^ (12 : ℕ))) - zetaSum A (-(Z ^ (12 : ℕ)))‖ := by
        simpa only [add_sub_cancel] using
          norm_add_le (zetaSum A (-(Z ^ (12 : ℕ))))
            (zetaSum M (-(Z ^ (12 : ℕ))) - zetaSum A (-(Z ^ (12 : ℕ))))
      have hfirst : 0 ≤ Z ^ (2 : ℕ) * Real.sqrt (M : ℝ) := by positivity
      have hlast : 0 ≤ (M : ℝ) / Z := by positivity
      linarith

/-- Natural-floor transfer preserves the full real cutoff range. -/
theorem norm_zetaSum_twelfth_scale {Z : ℝ} (hZ : 2 ≤ Z) {x : ℝ} (hx : 0 ≤ x) :
    ‖zetaSum x (Z ^ (12 : ℕ))‖ ≤
      1000 * (Z ^ (2 : ℕ) * Real.sqrt x + x / Z) := by
  have h := norm_zetaSum_nat_twelfth_scale hZ ⌊x⌋₊
  have he : zetaSum (⌊x⌋₊ : ℝ) (Z ^ (12 : ℕ)) = zetaSum x (Z ^ (12 : ℕ)) := by
    simp only [zetaSum, Nat.floor_natCast]
  rw [he] at h
  apply h.trans
  have hfloor := Nat.floor_le hx
  gcongr

/-- The actual source norm is invariant under taking the absolute height. -/
theorem norm_zetaSum_abs_height (x t : ℝ) : ‖zetaSum x |t|‖ = ‖zetaSum x t‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), norm_zetaSum_neg]

/-- Lemma 5.1 with an explicit absolute constant and no upper restriction on x. -/
theorem large_x_zeta_sum_bound {T t x : ℝ} (hT : 4096 ≤ T)
    (htlow : T ≤ |t|) (httop : |t| ≤ 2 * T) (hx : Real.sqrt T ≤ x) :
    ‖zetaSum x t‖ ≤ 3000 * x * T ^ (-1 / 13 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < |t| := hT0.trans_le htlow
  let Z := |t| ^ (1 / 12 : ℝ)
  have hZ0 : 0 < Z := Real.rpow_pos_of_pos ht0 _
  have hZ : 2 ≤ Z := by
    have hp : (2 : ℝ) ^ (12 : ℝ) ≤ |t| := by norm_num; linarith
    have hr := (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 2)
      ht0.le (by norm_num : (0 : ℝ) < 12)).mpr hp
    simpa only [Z, one_div] using hr
  have hZpow : Z ^ (12 : ℕ) = |t| := by
    dsimp only [Z]
    rw [← Real.rpow_mul_natCast ht0.le]
    norm_num
  have hx0 : 0 < x := (Real.sqrt_pos.mpr hT0).trans_le hx
  have hmain := norm_zetaSum_twelfth_scale hZ hx0.le
  rw [hZpow, norm_zetaSum_abs_height] at hmain
  have hTxx : T ≤ x ^ (2 : ℕ) :=
    (Real.sqrt_le_iff.mp hx).2
  have hZ12 : Z ^ (12 : ℕ) ≤ 2 * x ^ (2 : ℕ) := hZpow.le.trans (httop.trans (by linarith))
  have hZ6 : Z ^ (6 : ℕ) ≤ 2 * x := by
    nlinarith only [hZ12, pow_nonneg hZ0.le 6, hx0]
  have hZ3 : Z ^ (3 : ℕ) ≤ 2 * Real.sqrt x := by
    have hs := Real.sq_sqrt hx0.le
    nlinarith only [hZ6, hs, pow_nonneg hZ0.le 3, Real.sqrt_nonneg x, hx0]
  have hfirst : Z ^ (2 : ℕ) * Real.sqrt x ≤ 2 * x / Z := by
    apply (le_div_iff₀ hZ0).mpr
    have h := mul_le_mul_of_nonneg_right hZ3 (Real.sqrt_nonneg x)
    have hs := Real.sq_sqrt hx0.le
    nlinarith only [h, hs]
  have hinv : 1 / Z ≤ T ^ (-1 / 13 : ℝ) := by
    have hbase : T ^ (1 / 13 : ℝ) ≤ Z := by
      apply (Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num : (1 / 13 : ℝ) ≤ 1 / 12)).trans
      exact Real.rpow_le_rpow hT0.le htlow (by norm_num)
    have h := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hT0 _) hbase
    rw [show (-1 / 13 : ℝ) = -(1 / 13 : ℝ) by ring, Real.rpow_neg hT0.le]
    simpa only [one_div] using h
  have hpre : ‖zetaSum x t‖ ≤ 3000 * x / Z := by
    rw [mul_div_assoc] at hfirst ⊢
    linarith
  calc
    _ ≤ 3000 * x / Z := hpre
    _ = (3000 * x) * (1 / Z) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)

/-- Absolute-constant source form of Lemma 5.1. -/
theorem exists_large_x_zeta_sum_bound :
    ∃ K T₀ : ℝ, 0 < K ∧ 3 ≤ T₀ ∧ ∀ T t x : ℝ,
      T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T → Real.sqrt T ≤ x →
      ‖zetaSum x t‖ ≤ K * x * T ^ (-1 / 13 : ℝ) := by
  exact ⟨3000, 4096, by norm_num, by norm_num,
    fun _ _ _ hT hlo hhi hx => large_x_zeta_sum_bound hT hlo hhi hx⟩


end
end DongWangWangZhang2026
