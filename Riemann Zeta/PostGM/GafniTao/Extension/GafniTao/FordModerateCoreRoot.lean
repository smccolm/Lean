import GafniTao.FordModerateCore

/-!
# Uniform rooted saving for Ford's moderate-degree core

The one-degree estimate handles `40 <= k < 50`; the linear-cardinality
estimate handles `k >= 50`.  Both branches yield the same conservative rooted
saving `1/(665600 k^2)` in the literal `(2rs)^{-1}` power of Lemma 5.1.
-/

namespace GafniTao

noncomputable section

theorem fordModerateCoreCoefficient_nonneg (k : ℕ) (C : ℝ) :
    0 ≤ fordModerateCoreCoefficient k C := by
  unfold fordModerateCoreCoefficient
  positivity

theorem fordModerateMomentDegree_le
    {k : ℕ} (hk : 1 ≤ k) :
    fordModerateMomentDegree k ≤ 16 * k ^ 2 := by
  unfold fordModerateMomentDegree
  nlinarith

theorem ford_moderate_root_exponent_le
    {k : ℕ} (hk : 40 ≤ k) :
    (-((k : ℝ) ^ 2 / 1300)) *
        (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) ≤
      -(1 / ((665600 : ℝ) * (k : ℝ) ^ 2)) := by
  have hkPos : (0 : ℝ) < k := by positivity
  have hsPos : 0 < fordModerateMomentDegree k := by
    unfold fordModerateMomentDegree
    positivity
  have hsBound := fordModerateMomentDegree_le (by omega : 1 ≤ k)
  have hsBoundR : (fordModerateMomentDegree k : ℝ) ≤
      16 * (k : ℝ) ^ 2 := by
    exact_mod_cast hsBound
  have hden : (2 * fordModerateMomentDegree k ^ 2 : ℕ) ≤
      512 * k ^ 4 := by nlinarith
  have hdenR : ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ) ≤
      512 * (k : ℝ) ^ 4 := by
    exact_mod_cast hden
  have hq :
      1 / (512 * (k : ℝ) ^ 4) ≤
        1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ) := by
    exact one_div_le_one_div_of_le (by positivity) hdenR
  have hcoeffNonpos : -((k : ℝ) ^ 2 / 1300) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by norm_num))
  have hmul := mul_le_mul_of_nonpos_left hq hcoeffNonpos
  calc
    (-((k : ℝ) ^ 2 / 1300)) *
          (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) ≤
        (-((k : ℝ) ^ 2 / 1300)) *
          (1 / (512 * (k : ℝ) ^ 4)) := hmul
    _ = -(1 / ((665600 : ℝ) * (k : ℝ) ^ 2)) := by
      field_simp
      ring

theorem ford_moderate_small_root_exponent_le
    {k : ℕ} (hk : 40 ≤ k) (hkTop : k < 50) :
    (-(k : ℝ) / 20) *
        (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) ≤
      -(1 / ((665600 : ℝ) * (k : ℝ) ^ 2)) := by
  have hkPos : (0 : ℝ) < k := by positivity
  have hsBound := fordModerateMomentDegree_le (by omega : 1 ≤ k)
  have hden : (2 * fordModerateMomentDegree k ^ 2 : ℕ) ≤
      512 * k ^ 4 := by nlinarith
  have hdenR : ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ) ≤
      512 * (k : ℝ) ^ 4 := by exact_mod_cast hden
  have hsPosNat : 0 < fordModerateMomentDegree k := by
    unfold fordModerateMomentDegree
    positivity
  have hdenPosNat : 0 < 2 * fordModerateMomentDegree k ^ 2 := by positivity
  have hdenPosReal :
      (0 : ℝ) < ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hdenPosNat
  have hq : 1 / (512 * (k : ℝ) ^ 4) ≤
      1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ) :=
    one_div_le_one_div_of_le hdenPosReal hdenR
  have hcoeffNonpos : -(k : ℝ) / 20 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkPos.le) (by norm_num)
  have hmul := mul_le_mul_of_nonpos_left hq
    hcoeffNonpos
  have hkTopR : (k : ℝ) ≤ 49 := by exact_mod_cast (show k ≤ 49 by omega)
  calc
    (-(k : ℝ) / 20) *
          (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) ≤
        (-(k : ℝ) / 20) * (1 / (512 * (k : ℝ) ^ 4)) := hmul
    _ ≤ -(1 / ((665600 : ℝ) * (k : ℝ) ^ 2)) := by
      rw [div_eq_mul_inv]
      field_simp
      nlinarith

theorem fordLemma51SourceCore_moderate_power_saving
    {k N : ℕ} {t C : ℝ} (hk : 40 ≤ k)
    (hN : 1024 ≤ N) (ht : 0 < t) (hC : 0 ≤ C)
    (hmoment : FordVinogradovMomentBound
      (fordModerateMomentDegree k) k C (fordModerateMomentDelta k))
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    fordLemma51SourceCore k 1 k
        (fordModerateMomentDegree k) (fordModerateMomentDegree k)
        ((N : ℝ) ^ (1 / 5 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ)) N
        (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) t ≤
      fordModerateCoreCoefficient k C *
        (N : ℝ) ^ (if k < 50 then -(k : ℝ) / 20
          else -((k : ℝ) ^ 2 / 1300)) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdelta := fordModerateMomentDelta_le (by omega : 4 ≤ k)
  by_cases hk50 : k < 50
  · rw [if_pos hk50]
    have hsource := fordLemma51SourceCore_moderate_le hk hN ht hC hmoment
      hlower hupper
    have hexponent :
        (3 / 10 : ℝ) * fordModerateMomentDelta k - (2 / 25 : ℝ) * k ≤
          -(k : ℝ) / 20 := by
      have hkR : (40 : ℝ) ≤ k := by exact_mod_cast hk
      have hkTopR : (k : ℝ) ≤ 49 := by exact_mod_cast (show k ≤ 49 by omega)
      nlinarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hexponent
    apply hsource.trans
    calc
      fordModerateCoreCoefficient k C *
            (N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k) *
            (N : ℝ) ^ (-(2 / 25 : ℝ) * k) =
          fordModerateCoreCoefficient k C *
            ((N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k) *
              (N : ℝ) ^ (-(2 / 25 : ℝ) * k)) := by ring
      _ = fordModerateCoreCoefficient k C *
            (N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k -
              (2 / 25 : ℝ) * k) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
        congr 2
        ring
      _ ≤ fordModerateCoreCoefficient k C * (N : ℝ) ^ (-(k : ℝ) / 20) :=
        mul_le_mul_of_nonneg_left hpow (fordModerateCoreCoefficient_nonneg k C)
  · rw [if_neg hk50]
    have hk50' : 50 ≤ k := by omega
    have hsource := fordLemma51SourceCore_moderate_linear_le hk50' hN ht hC
      hmoment hlower hupper
    have hexponent :
        (3 / 10 : ℝ) * fordModerateMomentDelta k - (k : ℝ) ^ 2 / 1250 ≤
          -((k : ℝ) ^ 2 / 1300) := by
      have hkR : (0 : ℝ) ≤ k := by positivity
      nlinarith
    have hpow := Real.rpow_le_rpow_of_exponent_le hNreal hexponent
    apply hsource.trans
    calc
      fordModerateCoreCoefficient k C *
            (N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k) *
            (N : ℝ) ^ (-((k : ℝ) ^ 2 / 1250)) =
          fordModerateCoreCoefficient k C *
            ((N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k) *
              (N : ℝ) ^ (-((k : ℝ) ^ 2 / 1250))) := by ring
      _ = fordModerateCoreCoefficient k C *
            (N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k -
              (k : ℝ) ^ 2 / 1250) := by
        rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
        congr 2
      _ ≤ fordModerateCoreCoefficient k C *
            (N : ℝ) ^ (-((k : ℝ) ^ 2 / 1300)) :=
        mul_le_mul_of_nonneg_left hpow (fordModerateCoreCoefficient_nonneg k C)

theorem fordLemma51SourceCore_moderate_root_le
    {k N : ℕ} {t C : ℝ} (hk : 40 ≤ k)
    (hN : 1024 ≤ N) (ht : 0 < t) (hC : 0 ≤ C)
    (hmoment : FordVinogradovMomentBound
      (fordModerateMomentDegree k) k C (fordModerateMomentDelta k))
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    (fordLemma51SourceCore k 1 k
        (fordModerateMomentDegree k) (fordModerateMomentDegree k)
        ((N : ℝ) ^ (1 / 5 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ)) N
        (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) t) ^
          (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) ≤
      (fordModerateCoreCoefficient k C) ^
          (1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)) *
        (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by
  let q : ℝ := 1 / ((2 * fordModerateMomentDegree k ^ 2 : ℕ) : ℝ)
  let a : ℝ := if k < 50 then -(k : ℝ) / 20
    else -((k : ℝ) ^ 2 / 1300)
  have hsource0 : 0 ≤ fordLemma51SourceCore k 1 k
      (fordModerateMomentDegree k) (fordModerateMomentDegree k)
      ((N : ℝ) ^ (1 / 5 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ)) N
      (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) t := by
    apply fordLemma51SourceCore_nonneg
    · exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
    · positivity
    · unfold fordModerateMomentDegree; positivity
    · unfold fordModerateMomentDegree; positivity
    · positivity
    · exact ht
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hroot := Real.rpow_le_rpow hsource0
    (fordLemma51SourceCore_moderate_power_saving hk hN ht hC hmoment
      hlower hupper) hq0
  have hcoeff0 := fordModerateCoreCoefficient_nonneg k C
  have hexponent : a * q ≤
      -(1 / ((665600 : ℝ) * (k : ℝ) ^ 2)) := by
    dsimp [a, q]
    by_cases hk50 : k < 50
    · rw [if_pos hk50]
      exact ford_moderate_small_root_exponent_le hk hk50
    · rw [if_neg hk50]
      exact ford_moderate_root_exponent_le hk
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpow := Real.rpow_le_rpow_of_exponent_le hNreal hexponent
  calc
    _ ≤ (fordModerateCoreCoefficient k C * (N : ℝ) ^ a) ^ q := by
      simpa [a, q] using hroot
    _ = (fordModerateCoreCoefficient k C) ^ q *
          ((N : ℝ) ^ a) ^ q := by
      rw [Real.mul_rpow hcoeff0 (Real.rpow_nonneg (by positivity) _)]
    _ = (fordModerateCoreCoefficient k C) ^ q * (N : ℝ) ^ (a * q) := by
      rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    _ ≤ (fordModerateCoreCoefficient k C) ^ q *
          (N : ℝ) ^ (-(1 / ((665600 : ℝ) * (k : ℝ) ^ 2))) := by
      gcongr
    _ = _ := by rfl

#print axioms fordModerateMomentDegree_le
#print axioms ford_moderate_root_exponent_le
#print axioms ford_moderate_small_root_exponent_le
#print axioms fordLemma51SourceCore_moderate_power_saving
#print axioms fordLemma51SourceCore_moderate_root_le

end

end GafniTao
