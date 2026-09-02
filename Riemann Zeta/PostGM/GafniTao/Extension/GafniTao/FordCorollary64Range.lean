import GafniTao.FordCorollary64PowerSaving
import GafniTao.FordModerateLambdaSelection
import GafniTao.FordSmallLambdaBound

/-!
# A uniform qualitative Corollary-6.4 range

For `4 ≤ λ ≤ 49` we use `k = ⌈λ⌉` and the already proved fifteen-block
Lemma-6.5 moment.  The constants are deliberately not identified with the
optimized decimals in Ford's Table 6.1; this is the source-faithful
qualitative Vinogradov--Korobov input needed by the Gafni--Tao right edge.
-/

namespace GafniTao

noncomputable section

def fordCor64Degree (lambda : ℝ) : ℕ := max 4 ⌈lambda⌉₊

theorem fordCor64Degree_bounds
    {lambda : ℝ} (hlower : 4 ≤ lambda) (hupper : lambda ≤ 49) :
    4 ≤ fordCor64Degree lambda ∧
      (fordCor64Degree lambda : ℝ) - 1 ≤ lambda ∧
      lambda ≤ fordCor64Degree lambda ∧
      fordCor64Degree lambda < 50 ∧
      (fordCor64Degree lambda : ℝ) ≤ (5 / 4 : ℝ) * lambda := by
  have hlambda0 : 0 ≤ lambda := by linarith
  have hceil4 : 4 ≤ ⌈lambda⌉₊ := by
    exact_mod_cast hlower.trans (Nat.le_ceil lambda)
  have hkEq : fordCor64Degree lambda = ⌈lambda⌉₊ := by
    simp [fordCor64Degree, max_eq_right hceil4]
  have hceilLower : lambda ≤ (⌈lambda⌉₊ : ℝ) := Nat.le_ceil _
  have hceilUpper : (⌈lambda⌉₊ : ℝ) < lambda + 1 :=
    Nat.ceil_lt_add_one hlambda0
  have hceil49 : ⌈lambda⌉₊ ≤ 49 := Nat.ceil_le.mpr hupper
  rw [hkEq]
  refine ⟨hceil4, by linarith, hceilLower, by omega, ?_⟩
  nlinarith

def fordCor64MomentCoefficient (k : ℕ) : ℝ :=
  if hk : 4 ≤ k then Classical.choose (ford_moderate_moment_bound hk) else 1

theorem fordCor64MomentCoefficient_bound
    {k : ℕ} (hk : 4 ≤ k) :
    FordVinogradovMomentBound (fordModerateMomentDegree k) k
      (fordCor64MomentCoefficient k) (fordModerateMomentDelta k) := by
  simp only [fordCor64MomentCoefficient, dif_pos hk]
  exact Classical.choose_spec (ford_moderate_moment_bound hk)

theorem fordCor64MomentCoefficient_nonneg (k : ℕ) :
    0 ≤ fordCor64MomentCoefficient k := by
  by_cases hk : 4 ≤ k
  · exact zero_le_one.trans
      (fordCor64MomentCoefficient_bound hk).one_le_coefficient
  · simp [fordCor64MomentCoefficient, hk]

def fordCor64Coefficient (k : ℕ) : ℝ :=
  fordCorollary64PowerCoefficient (fordModerateMomentDegree k) k
    (fordCor64MomentCoefficient k)

theorem fordCor64Coefficient_nonneg (k : ℕ) :
    0 ≤ fordCor64Coefficient k := by
  unfold fordCor64Coefficient fordCorollary64PowerCoefficient
  have hbase : 0 ≤ fordCor64MomentCoefficient k *
      (2 * Real.pi * k) ^ k * (k.factorial : ℝ) := by
    exact mul_nonneg
      (mul_nonneg (fordCor64MomentCoefficient_nonneg k) (by positivity))
      (by positivity)
  positivity

def fordCor64AbsoluteCoefficient : ℝ :=
  ∑ k ∈ Finset.range 50, fordCor64Coefficient k

theorem fordCor64Coefficient_le_absolute
    {k : ℕ} (hk : k < 50) :
    fordCor64Coefficient k ≤ fordCor64AbsoluteCoefficient := by
  unfold fordCor64AbsoluteCoefficient
  exact Finset.single_le_sum
    (fun i _ => fordCor64Coefficient_nonneg i) (Finset.mem_range.mpr hk)

theorem fordCor64AbsoluteCoefficient_nonneg :
    0 ≤ fordCor64AbsoluteCoefficient := by
  unfold fordCor64AbsoluteCoefficient
  exact Finset.sum_nonneg fun k _ => fordCor64Coefficient_nonneg k

theorem fordCor64_saving_bounds
    {k : ℕ} (hk : 4 ≤ k) (hkTop : k < 50) :
    0 < fordCorollary64Saving (fordModerateMomentDegree k) k
        (fordModerateMomentDelta k) ∧
      1 / (64 * (k : ℝ) ^ 2) ≤
        fordCorollary64Saving (fordModerateMomentDegree k) k
          (fordModerateMomentDelta k) ∧
      fordCorollary64Saving (fordModerateMomentDegree k) k
          (fordModerateMomentDelta k) ≤ 1 / (k + 1 : ℝ) ∧
      fordCorollary64Saving (fordModerateMomentDegree k) k
          (fordModerateMomentDelta k) ≤ 1 - 2 / (k + 1 : ℝ) := by
  let delta := fordModerateMomentDelta k
  let s := fordModerateMomentDegree k
  let e : ℝ := (2 + 2 * delta) / (k + 1 : ℝ)
  let c : ℝ := fordCorollary64Saving s k delta
  have hkR : (4 : ℝ) ≤ k := by exact_mod_cast hk
  have hkTopR : (k : ℝ) ≤ 49 := by exact_mod_cast (show k ≤ 49 by omega)
  have hkPos : (0 : ℝ) < k := by positivity
  have hdenK : (0 : ℝ) < k + 1 := by positivity
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    exact fordModerateMomentDelta_nonneg hk
  have hdeltaTop : delta ≤ (k : ℝ) ^ 2 / 65536 := by
    dsimp [delta]
    exact fordModerateMomentDelta_le hk
  have hkSq : (k : ℝ) ^ 2 ≤ 49 ^ 2 := by nlinarith
  have he0 : 0 ≤ e := by dsimp [e]; positivity
  have heHalf : e ≤ 1 / 2 := by
    dsimp [e]
    apply (div_le_iff₀ hdenK).2
    have : delta ≤ (49 : ℝ) ^ 2 / 65536 := hdeltaTop.trans (by gcongr)
    nlinarith
  have hsEq : (s : ℝ) = (15 * (k : ℝ) + 1) * k := by
    dsimp [s, fordModerateMomentDegree]
    push_cast
    ring
  have hsPos : (0 : ℝ) < s := by rw [hsEq]; positivity
  have hsTop : (s : ℝ) ≤ 16 * (k : ℝ) ^ 2 := by
    rw [hsEq]
    nlinarith
  have hcEq : c = (1 - e) / (2 * s : ℝ) := by
    rfl
  have hcPos : 0 < c := by
    rw [hcEq]
    exact div_pos (by linarith) (by positivity)
  have hcLower : 1 / (64 * (k : ℝ) ^ 2) ≤ c := by
    rw [hcEq]
    have hnum : (1 / 2 : ℝ) ≤ 1 - e := by linarith
    have hdenPos : (0 : ℝ) < 2 * (s : ℝ) := by positivity
    have hfirst : (1 / 2 : ℝ) / (2 * (s : ℝ)) ≤
        (1 - e) / (2 * (s : ℝ)) :=
      div_le_div_of_nonneg_right hnum hdenPos.le
    have hdenCompare : 4 * (s : ℝ) ≤ 64 * (k : ℝ) ^ 2 := by linarith
    have hrecip : 1 / (64 * (k : ℝ) ^ 2) ≤ 1 / (4 * (s : ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hdenCompare
    have heq : (1 / 2 : ℝ) / (2 * (s : ℝ)) = 1 / (4 * (s : ℝ)) := by
      field_simp [ne_of_gt hsPos]
      norm_num
    exact hrecip.trans (heq ▸ hfirst)
  have hcUnit : c ≤ 1 / (2 * (s : ℝ)) := by
    rw [hcEq]
    have hnum : 1 - e ≤ 1 := by linarith
    exact div_le_div_of_nonneg_right hnum (by positivity)
  have hsK : (k : ℝ) + 1 ≤ 2 * (s : ℝ) := by
    rw [hsEq]
    nlinarith
  have hunitK : 1 / (2 * (s : ℝ)) ≤ 1 / ((k : ℝ) + 1) :=
    one_div_le_one_div_of_le hdenK hsK
  have hcK := hcUnit.trans hunitK
  have hcTwo : c ≤ 1 - 2 / ((k : ℝ) + 1) := by
    apply hcK.trans
    rw [le_sub_iff_add_le, ← add_div]
    exact (div_le_one hdenK).2 (by nlinarith)
  dsimp [c, s, delta] at hcPos hcLower hcK hcTwo
  exact ⟨hcPos, hcLower, hcK, hcTwo⟩

theorem fordCor64_target_saving_le
    {lambda : ℝ} {k : ℕ}
    (hlambda : 4 ≤ lambda) (hkPos : 0 < k)
    (hk : (k : ℝ) ≤ (5 / 4 : ℝ) * lambda) :
    1 / (100 * lambda ^ 2) ≤ 1 / (64 * (k : ℝ) ^ 2) := by
  have hlambdaPos : 0 < lambda := by linarith
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hsquare : (k : ℝ) ^ 2 ≤ (25 / 16 : ℝ) * lambda ^ 2 := by
    nlinarith
  have hden : 64 * (k : ℝ) ^ 2 ≤ 100 * lambda ^ 2 := by nlinarith
  exact one_div_le_one_div_of_le (by positivity) hden

theorem ford_shifted_exponential_sum_cor64_range
    {N R : ℕ} {u t : ℝ}
    (hN : 2 ≤ N) (hRlower : N < R) (hR : R ≤ 2 * N)
    (hu0 : 0 < u) (hu1 : u ≤ 1) (ht : 0 < t)
    (hlambda : 4 ≤ fordLambda N t)
    (hlambdaTop : fordLambda N t ≤ 49) :
    ‖fordShiftedExponentialSum N R u t‖ ≤
      fordCor64AbsoluteCoefficient * (N : ℝ) ^
        (1 - 1 / (100 * fordLambda N t ^ 2)) := by
  let lambda := fordLambda N t
  let k := fordCor64Degree lambda
  let C := fordCor64MomentCoefficient k
  let delta := fordModerateMomentDelta k
  let n := 15 * k + 1
  let P : ℝ := (N : ℝ) ^ fordCorollary64Mu k lambda
  obtain ⟨hk, hlower, hupper, hkTop, hkLambda⟩ :=
    fordCor64Degree_bounds hlambda hlambdaTop
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hmoment : FordVinogradovMomentBound (n * k) k C delta := by
    simpa [n, C, delta, fordModerateMomentDegree] using
      fordCor64MomentCoefficient_bound hk
  have hC : 0 ≤ C := by
    dsimp [C]
    exact fordCor64MomentCoefficient_nonneg k
  have hdelta : 0 ≤ delta := by
    dsimp [delta]
    exact fordModerateMomentDelta_nonneg hk
  obtain ⟨hcPos, hcLower, hcK, hcTwo⟩ := fordCor64_saving_bounds hk hkTop
  have hnDegree : n * k = fordModerateMomentDegree k := by
    simp [n, fordModerateMomentDegree]
  have hdLower : 1 / (100 * lambda ^ 2) ≤
      fordCorollary64Saving (n * k) k delta := by
    rw [hnDegree]
    exact (fordCor64_target_saving_le hlambda (by omega) hkLambda).trans hcLower
  have hsource := fordCorollary64_le_power_saving
    (k := k) (n := n) (N := N) (R := R) (P := P)
    (u := u) (t := t) (lambda := lambda) (C := C) (delta := delta)
    hk hn (by omega) hRlower hR hu0 hu1 hlower hupper
      (ford_rpow_lambda_eq_height (by omega) ht).symm rfl hC hdelta hmoment
      (by simpa [hnDegree] using hcK) (by simpa [hnDegree] using hcTwo)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow : (N : ℝ) ^
      (1 - fordCorollary64Saving (n * k) k delta) ≤
      (N : ℝ) ^ (1 - 1 / (100 * lambda ^ 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hNreal
    linarith
  have hcoef : fordCor64Coefficient k ≤ fordCor64AbsoluteCoefficient :=
    fordCor64Coefficient_le_absolute hkTop
  have hB0 : 0 ≤ fordCor64Coefficient k := fordCor64Coefficient_nonneg k
  apply hsource.trans
  calc
    fordCorollary64PowerCoefficient (n * k) k C *
        (N : ℝ) ^ (1 - fordCorollary64Saving (n * k) k delta) =
      fordCor64Coefficient k *
        (N : ℝ) ^ (1 - fordCorollary64Saving (n * k) k delta) := by
      rw [hnDegree]
      rfl
    _ ≤ fordCor64Coefficient k *
        (N : ℝ) ^ (1 - 1 / (100 * lambda ^ 2)) := by gcongr
    _ ≤ fordCor64AbsoluteCoefficient *
        (N : ℝ) ^ (1 - 1 / (100 * lambda ^ 2)) := by gcongr
    _ = _ := by rfl

#print axioms fordCor64Degree_bounds
#print axioms fordCor64_saving_bounds
#print axioms ford_shifted_exponential_sum_cor64_range

end

end GafniTao
