import GafniTao.Pintz2023DyadicHeightShell
import GafniTao.Pintz2023LargeMLocalizedBound

/-!
# Pintz Corollary 3: physical scale verification

The common split point and the localized right endpoint are compared with
the actual displaced ordinate on a dyadic height shell.  This supplies the
physical `N ≪ |t|^(2/k)` hypothesis rather than assuming it at ambient
height `T`.
-/

open Filter Finset

namespace GafniTao

noncomputable section

noncomputable def pintz2023CorThreePhysicalConstant : ℝ :=
  4 * (Real.exp 3 + 2)

theorem pintz2023CriticalScaleExponent_lt_two_div
    {k : ℕ} {eta xi epsilon : ℝ}
    (hk : 4 ≤ k) (heta : 0 ≤ eta) (hxi : xi ≤ eta)
    (hAlpha : eta + 6 * epsilon < pintz2023HBAlpha k) :
    pintz2023CriticalScaleExponent k xi epsilon < 2 / (k : ℝ) := by
  have hkReal : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by linarith
  have hkMinusPos : (0 : ℝ) < (k : ℝ) - 1 := by linarith
  have hAlpha' : eta + 6 * epsilon <
      1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
    simpa only [pintz2023HBAlpha] using hAlpha
  have hEtaEps : ((k : ℝ) - 1) * (eta + 6 * epsilon) < 1 / (k : ℝ) := by
    rw [lt_div_iff₀ hkPos]
    rw [div_eq_mul_inv] at hAlpha'
    have hprod := mul_lt_mul_of_pos_left hAlpha'
      (mul_pos hkPos hkMinusPos)
    field_simp [hkPos.ne', hkMinusPos.ne'] at hprod ⊢
    nlinarith
  have hSixEps : 6 * epsilon <
      1 / ((k : ℝ) * ((k : ℝ) - 1)) := by
    nlinarith [heta]
  have hsum : ((k : ℝ) - 1) * xi + 6 * (k : ℝ) * epsilon < 1 / 2 := by
    have hxiScaled := mul_le_mul_of_nonneg_left hxi hkMinusPos.le
    have hrecip : 1 / ((k : ℝ) - 1) ≤ 1 / 3 := by
      exact one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hcombine : ((k : ℝ) - 1) * eta + 6 * (k : ℝ) * epsilon <
        1 / ((k : ℝ) - 1) := by
      have hrewrite :
          ((k : ℝ) - 1) * eta + 6 * (k : ℝ) * epsilon =
            ((k : ℝ) - 1) * (eta + 6 * epsilon) + 6 * epsilon := by ring
      rw [hrewrite]
      have hadd := add_lt_add hEtaEps hSixEps
      have hid : 1 / (k : ℝ) +
          1 / ((k : ℝ) * ((k : ℝ) - 1)) =
            1 / ((k : ℝ) - 1) := by field_simp; ring
      simpa only [hid] using hadd
    linarith
  have hden : 1 / 2 <
      1 - ((k : ℝ) - 1) * xi - 6 * (k : ℝ) * epsilon := by
    linarith
  unfold pintz2023CriticalScaleExponent
  rw [div_lt_div_iff₀ (mul_pos hkPos (by linarith :
    0 < 1 - ((k : ℝ) - 1) * xi - 6 * (k : ℝ) * epsilon)) hkPos]
  nlinarith

theorem pintz2023CriticalScale_lt_source_power
    {k : ℕ} {T eta xi epsilon : ℝ}
    (hk : 4 ≤ k) (hT : 1 < T) (heta : 0 ≤ eta) (hxi : xi ≤ eta)
    (hAlpha : eta + 6 * epsilon < pintz2023HBAlpha k) :
    pintz2023CriticalScale k xi epsilon T < T ^ (2 / (k : ℝ)) := by
  unfold pintz2023CriticalScale
  exact Real.rpow_lt_rpow_of_exponent_lt hT
    (pintz2023CriticalScaleExponent_lt_two_div hk heta hxi hAlpha)

theorem pintz2023Cutoff_cast_lt_source_power
    {k : ℕ} {T : ℝ} (hT : 1 ≤ T) (hTPos : 0 < T) :
    (pintz2023Cutoff (pintz2023SourceLambda T k) : ℝ) <
      (Real.exp 3 + 1) * T ^ (2 / (k : ℝ)) := by
  have hpowOne : 1 ≤ T ^ (2 / (k : ℝ)) := by
    by_cases hk : k = 0
    · subst k
      simp
    · have hkPos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
      exact Real.one_le_rpow hT (by positivity)
  have hceil :
      (pintz2023Cutoff (pintz2023SourceLambda T k) : ℝ) <
        Real.exp (pintz2023SourceLambda T k + 3) + 1 := by
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hexp : Real.exp (pintz2023SourceLambda T k + 3) =
      T ^ (2 / (k : ℝ)) * Real.exp 3 := by
    rw [Real.exp_add, exp_pintz2023SourceLambda hTPos]
  rw [hexp] at hceil
  calc
    (pintz2023Cutoff (pintz2023SourceLambda T k) : ℝ) <
        T ^ (2 / (k : ℝ)) * Real.exp 3 + 1 := hceil
    _ ≤ (Real.exp 3 + 1) * T ^ (2 / (k : ℝ)) := by
      nlinarith [hpowOne]

theorem pintz2023_source_power_le_four_mul_displaced_power
    {k : ℕ} {T t : ℝ} (hk : 2 ≤ k) (hT : 0 ≤ T)
    (hPhysical : T / 4 ≤ |t|) :
    T ^ (2 / (k : ℝ)) ≤ 4 * |t| ^ (2 / (k : ℝ)) := by
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkPos : (0 : ℝ) < k := by linarith
  have hexpNonneg : 0 ≤ 2 / (k : ℝ) := by positivity
  have hexpOne : 2 / (k : ℝ) ≤ 1 :=
    (div_le_one hkPos).2 hkReal
  have hbase : T ≤ 4 * |t| := by linarith
  have hpow := Real.rpow_le_rpow hT hbase hexpNonneg
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (abs_nonneg t)] at hpow
  have hfour : (4 : ℝ) ^ (2 / (k : ℝ)) ≤ 4 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hexpOne
  exact hpow.trans
    (mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (abs_nonneg t) _))

theorem pintz2023_localized_physical_scale
    {k q X d : ℕ} {T eta epsilon t : ℝ}
    (hk : 4 ≤ k) (hT : 4 ≤ T) (heta : 0 ≤ eta)
    (hAlpha : eta + 6 * epsilon < pintz2023HBAlpha k)
    (hNonempty : 2 ^ q * X ≤
      min (2 * (2 ^ q * X))
        (pintz2023Cutoff (pintz2023SourceLambda T k)) + 1)
    (hd : 0 < d) (hdX : d ≤ X) (hPhysical : T / 4 ≤ |t|) :
    ((max ((2 ^ q * X) / d)
        (Nat.ceil (pintz2023CriticalScale k eta epsilon T)) : ℕ) : ℝ) ≤
      pintz2023CorThreePhysicalConstant * |t| ^ (2 / (k : ℝ)) := by
  have hTPos : 0 < T := by linarith
  have hTOne : 1 < T := by linarith
  have hpowOne : 1 ≤ T ^ (2 / (k : ℝ)) := by
    have hkPos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega) hk)
    exact Real.one_le_rpow hTOne.le (by positivity)
  have hcutoff := pintz2023Cutoff_cast_lt_source_power
    (k := k) hTOne.le hTPos
  have hA : 2 ^ q * X ≤
      pintz2023Cutoff (pintz2023SourceLambda T k) + 1 := by
    omega
  have hACast : ((2 ^ q * X : ℕ) : ℝ) <
      (Real.exp 3 + 2) * T ^ (2 / (k : ℝ)) := by
    have hACastLe : ((2 ^ q * X : ℕ) : ℝ) ≤
        (pintz2023Cutoff (pintz2023SourceLambda T k) : ℝ) + 1 := by
      exact_mod_cast hA
    calc
      ((2 ^ q * X : ℕ) : ℝ) ≤
          (pintz2023Cutoff (pintz2023SourceLambda T k) : ℝ) + 1 := hACastLe
      _ < (Real.exp 3 + 1) * T ^ (2 / (k : ℝ)) + 1 := by linarith
      _ ≤ (Real.exp 3 + 2) * T ^ (2 / (k : ℝ)) := by
        nlinarith [hpowOne]
  have hDiv : (((2 ^ q * X) / d : ℕ) : ℝ) ≤
      (Real.exp 3 + 2) * T ^ (2 / (k : ℝ)) := by
    have : (2 ^ q * X) / d ≤ 2 ^ q * X := Nat.div_le_self _ _
    have hcast : (((2 ^ q * X) / d : ℕ) : ℝ) ≤
        ((2 ^ q * X : ℕ) : ℝ) := by exact_mod_cast this
    exact hcast.trans hACast.le
  have hcritical := pintz2023CriticalScale_lt_source_power
    hk hTOne heta le_rfl hAlpha
  have hceil :
      (Nat.ceil (pintz2023CriticalScale k eta epsilon T) : ℝ) <
        pintz2023CriticalScale k eta epsilon T + 1 := by
    exact Nat.ceil_lt_add_one
      (Real.rpow_nonneg hTPos.le _)
  have hceilBound :
      (Nat.ceil (pintz2023CriticalScale k eta epsilon T) : ℝ) ≤
        (Real.exp 3 + 2) * T ^ (2 / (k : ℝ)) := by
    have hExpThree : 1 ≤ Real.exp 3 := by
      rw [← Real.exp_zero]
      exact (Real.exp_lt_exp.mpr (by norm_num)).le
    calc
      (Nat.ceil (pintz2023CriticalScale k eta epsilon T) : ℝ) <
          pintz2023CriticalScale k eta epsilon T + 1 := hceil
      _ < T ^ (2 / (k : ℝ)) + 1 := by linarith
      _ ≤ (Real.exp 3 + 2) * T ^ (2 / (k : ℝ)) := by
        nlinarith [hpowOne]
    exact this.le
  have hMax :
      ((max ((2 ^ q * X) / d)
          (Nat.ceil (pintz2023CriticalScale k eta epsilon T)) : ℕ) : ℝ) ≤
        (Real.exp 3 + 2) * T ^ (2 / (k : ℝ)) := by
    rw [Nat.cast_max]
    exact max_le hDiv hceilBound
  have hHeight := pintz2023_source_power_le_four_mul_displaced_power
    (show 2 ≤ k by omega) hTPos.le hPhysical
  unfold pintz2023CorThreePhysicalConstant
  calc
    ((max ((2 ^ q * X) / d)
        (Nat.ceil (pintz2023CriticalScale k eta epsilon T)) : ℕ) : ℝ) ≤
        (Real.exp 3 + 2) * T ^ (2 / (k : ℝ)) := hMax
    _ ≤ (Real.exp 3 + 2) * (4 * |t| ^ (2 / (k : ℝ))) := by
      gcongr
      positivity
    _ = 4 * (Real.exp 3 + 2) * |t| ^ (2 / (k : ℝ)) := by ring

#print axioms pintz2023CriticalScaleExponent_lt_two_div
#print axioms pintz2023CriticalScale_lt_source_power
#print axioms pintz2023Cutoff_cast_lt_source_power
#print axioms pintz2023_source_power_le_four_mul_displaced_power
#print axioms pintz2023_localized_physical_scale

end

end GafniTao
