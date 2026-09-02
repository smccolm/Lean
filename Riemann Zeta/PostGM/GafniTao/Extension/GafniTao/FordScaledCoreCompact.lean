import GafniTao.FordLemma51ScaledCore
import GafniTao.FordExpCertificate

/-!
# Compacting the scaled Ford source core

The mean-value exponents cancel the two negative normalization powers.  This
file performs that cancellation explicitly, including the cast bridge for
`k(k+1)/2`.
-/

namespace GafniTao

noncomputable section

theorem fordVinogradovKappa_cast (k : ℕ) :
    (fordVinogradovKappa k : ℝ) = (k : ℝ) * (k + 1) / 2 := by
  unfold fordVinogradovKappa
  rw [Nat.cast_div_charZero
    (even_iff_two_dvd.mp (Nat.even_mul_succ_self k))]
  norm_num

theorem ford_scaled_core_power_cancellation
    {k s M g : ℕ} {M₂ C delta E : ℝ}
    (hM : 0 < M) (hM₂ : 0 < M₂) :
    (5 * (s : ℝ)) ^ k * M₂ ^ (-(2 * s : ℝ)) *
        (M : ℝ) ^ (-(2 * s : ℝ) + fordVinogradovKappa k) *
        (C * (M : ℝ) ^ fordLambda34 s k delta) *
        (C * M₂ ^ fordLambda34 s k delta) *
        ((2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k * E ^ g) =
      (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
        (M : ℝ) ^ delta * M₂ ^ delta * E ^ g := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hkappa := fordVinogradovKappa_cast k
  have hMcombine :
      (M : ℝ) ^ (-(2 * s : ℝ) + fordVinogradovKappa k) *
          (M : ℝ) ^ fordLambda34 s k delta =
        (M : ℝ) ^ delta := by
    rw [← Real.rpow_add hMr]
    congr 1
    unfold fordLambda34
    rw [hkappa]
    ring
  have hM₂combine :
      M₂ ^ (-(2 * s : ℝ)) * M₂ ^ fordLambda34 s k delta *
          M₂ ^ fordVinogradovKappa k =
        M₂ ^ delta := by
    rw [← Real.rpow_add hM₂ (-(2 * s : ℝ)) (fordLambda34 s k delta)]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hM₂
      (-(2 * s : ℝ) + fordLambda34 s k delta)
      (fordVinogradovKappa k : ℝ)]
    congr 1
    unfold fordLambda34
    rw [hkappa]
    ring
  calc
    (5 * (s : ℝ)) ^ k * M₂ ^ (-(2 * s : ℝ)) *
          (M : ℝ) ^ (-(2 * s : ℝ) + fordVinogradovKappa k) *
          (C * (M : ℝ) ^ fordLambda34 s k delta) *
          (C * M₂ ^ fordLambda34 s k delta) *
          ((2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k * E ^ g) =
        ((5 * (s : ℝ)) ^ k * (2 * (s : ℝ)) ^ k) * C ^ 2 *
          ((M : ℝ) ^ (-(2 * s : ℝ) + fordVinogradovKappa k) *
            (M : ℝ) ^ fordLambda34 s k delta) *
          (M₂ ^ (-(2 * s : ℝ)) * M₂ ^ fordLambda34 s k delta *
            M₂ ^ fordVinogradovKappa k) * E ^ g := by ring
    _ = ((5 * (s : ℝ)) ^ k * (2 * (s : ℝ)) ^ k) * C ^ 2 *
          (M : ℝ) ^ delta * M₂ ^ delta * E ^ g := by
      rw [hMcombine, hM₂combine]
    _ = (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (M : ℝ) ^ delta * M₂ ^ delta * E ^ g := by
      rw [← mul_pow]
      congr 1
      ring

theorem fordScaledSourceCoreMajorant_le_compact
    {k N : ℕ} (hk : 1000 ≤ k) (hN : 1024 ≤ N) :
    fordScaledSourceCoreMajorant k N ≤
      (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
        fordDoubleSquareCoefficient k ^ 2 *
        (N : ℝ) ^ ((3 / 10 : ℝ) * fordDoubleSquareDelta k) *
        fordWGoodEnvelope k N ^ (fordGoodDegreeSet k).card := by
  let s := fordDoubleSquareDegree k
  let M₁ : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)
  let M₂ : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  let M : ℕ := ⌊M₁⌋₊
  let Q : ℕ := ⌊M₂⌋₊
  let C : ℝ := fordDoubleSquareCoefficient k
  let delta : ℝ := fordDoubleSquareDelta k
  let E : ℝ := fordWGoodEnvelope k N
  let g : ℕ := (fordGoodDegreeSet k).card
  have hk1000 : 1000 ≤ k := hk
  have hkpos : 0 < k := by omega
  have hNpos : (0 : ℝ) < N := by positivity
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  obtain ⟨_hM₁two, hM₂two, _hMhalf, hMone, _hQone,
      _hM₁top, _hM₂top, _hprodTop⟩ :=
    ford_basic_scale_data (x := (N : ℝ)) (by exact_mod_cast hN)
  have hMpos : 0 < M := by
    dsimp [M, M₁]
    omega
  have hM₂pos : 0 < M₂ := by dsimp [M₂]; positivity
  have hdelta : 0 ≤ delta := by
    dsimp [delta, fordDoubleSquareDelta]
    positivity
  have hkappa := fordVinogradovKappa_cast k
  have hlambda : 0 ≤ fordLambda34 s k delta := by
    dsimp [s, fordDoubleSquareDegree]
    unfold fordLambda34
    rw [show ((k : ℝ) * ((k : ℝ) + 1)) / 2 =
      (fordVinogradovKappa k : ℝ) by exact hkappa.symm]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
    have hkappaUpper : (fordVinogradovKappa k : ℝ) ≤ 2 * (2 * k ^ 2 : ℕ) := by
      rw [hkappa]
      push_cast
      nlinarith
    exact add_nonneg (sub_nonneg.mpr hkappaUpper) hdelta
  have hQcast : (Q : ℝ) ≤ M₂ := by
    dsimp [Q, M₂]
    exact Nat.floor_le (by positivity)
  have hQpow : (Q : ℝ) ^ fordLambda34 s k delta ≤
      M₂ ^ fordLambda34 s k delta :=
    Real.rpow_le_rpow (by positivity) hQcast hlambda
  have hC : 0 ≤ C := by
    dsimp [C, fordDoubleSquareCoefficient]
    exact fordMomentCoefficient36_nonneg _ _
  have hE : 0 ≤ E := by
    dsimp [E, fordWGoodEnvelope]
    positivity
  have hreplace : fordScaledSourceCoreMajorant k N ≤
      (5 * (s : ℝ)) ^ k * M₂ ^ (-(2 * s : ℝ)) *
        (M : ℝ) ^ (-(2 * s : ℝ) + fordVinogradovKappa k) *
        (C * (M : ℝ) ^ fordLambda34 s k delta) *
        (C * M₂ ^ fordLambda34 s k delta) *
        ((2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k * E ^ g) := by
    dsimp [fordScaledSourceCoreMajorant, s, M₁, M₂, M, Q, C, delta, E, g]
    gcongr
  have hcancel := ford_scaled_core_power_cancellation
    (k := k) (s := s) (M := M) (g := g) (M₂ := M₂)
    (C := C) (delta := delta) (E := E) hMpos hM₂pos
  rw [hcancel] at hreplace
  have hMcast : (M : ℝ) ≤ M₁ := by
    dsimp [M]
    exact Nat.floor_le (by dsimp [M₁]; positivity)
  have hMpow : (M : ℝ) ^ delta ≤ M₁ ^ delta :=
    Real.rpow_le_rpow (by positivity) hMcast hdelta
  have hscaleEq : M₁ ^ delta * M₂ ^ delta =
      (N : ℝ) ^ ((3 / 10 : ℝ) * delta) := by
    dsimp [M₁, M₂]
    rw [← Real.rpow_mul hN0, ← Real.rpow_mul hN0,
      ← Real.rpow_add hNpos]
    congr 1
    ring
  calc
    fordScaledSourceCoreMajorant k N ≤
        (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (M : ℝ) ^ delta * M₂ ^ delta * E ^ g := hreplace
    _ ≤ (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          M₁ ^ delta * M₂ ^ delta * E ^ g := by gcongr
    _ = (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (M₁ ^ delta * M₂ ^ delta) * E ^ g := by ring
    _ = (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (N : ℝ) ^ ((3 / 10 : ℝ) * delta) * E ^ g := by rw [hscaleEq]
    _ = (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
          fordDoubleSquareCoefficient k ^ 2 *
          (N : ℝ) ^ ((3 / 10 : ℝ) * fordDoubleSquareDelta k) *
          fordWGoodEnvelope k N ^ (fordGoodDegreeSet k).card := by
      rfl

def fordScaledCoreCoefficient (k : ℕ) : ℝ :=
  (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
    fordDoubleSquareCoefficient k ^ 2 *
    (4 * (8 : ℝ) ^ k) ^ k

def fordScaledCoreDecayExponent (k : ℕ) : ℝ :=
  (3 / 10 : ℝ) * fordDoubleSquareDelta k - (k : ℝ) ^ 2 / 275

theorem fordGoodDegreeSet_card_real_lower
    {k : ℕ} (hk : 1000 ≤ k) :
    (k : ℝ) / 22 ≤ ((fordGoodDegreeSet k).card : ℝ) := by
  have hq47 : 47 ≤ k / 21 := by
    exact (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  have hmod : k % 21 < 21 := Nat.mod_lt _ (by norm_num)
  have hdecomp : 21 * (k / 21) + k % 21 = k := Nat.div_add_mod k 21
  have hhalfNat : k ≤ 22 * (k / 21) := by omega
  have hcard := fordGoodDegreeSet_card_lower hk
  have hhalf : (k : ℝ) / 22 ≤ (k / 21 : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 22)]
    exact_mod_cast (by simpa [Nat.mul_comm] using hhalfNat)
  exact hhalf.trans (by exact_mod_cast hcard)

theorem fordGoodDegreeSet_card_upper (k : ℕ) :
    (fordGoodDegreeSet k).card ≤ k := by
  calc
    (fordGoodDegreeSet k).card ≤ (Finset.univ : Finset (Fin k)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = k := by simp

theorem fordWGoodEnvelope_pow_card_le
    {k N : ℕ} (hk : 1000 ≤ k) (hN : 1 ≤ N) :
    fordWGoodEnvelope k N ^ (fordGoodDegreeSet k).card ≤
      (4 * (8 : ℝ) ^ k) ^ k *
        (N : ℝ) ^ (-((k : ℝ) ^ 2 / 275)) := by
  let g : ℕ := (fordGoodDegreeSet k).card
  let B : ℝ := (2 : ℝ) ^ k + 1 + (8 : ℝ) ^ k + 1
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := zero_lt_one.trans_le hNreal
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  have htwoEight : (2 : ℝ) ^ k ≤ (8 : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) (by norm_num) _
  have honeEight : (1 : ℝ) ≤ (8 : ℝ) ^ k :=
    one_le_pow₀ (by norm_num)
  have hB : B ≤ 4 * (8 : ℝ) ^ k := by
    dsimp [B]
    linarith
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  have hBtopOne : 1 ≤ 4 * (8 : ℝ) ^ k := by linarith
  have hgUpper : g ≤ k := by
    dsimp [g]
    exact fordGoodDegreeSet_card_upper k
  have hBpow : B ^ g ≤ (4 * (8 : ℝ) ^ k) ^ k := by
    calc
      B ^ g ≤ (4 * (8 : ℝ) ^ k) ^ g :=
        pow_le_pow_left₀ hBnonneg hB _
      _ ≤ (4 * (8 : ℝ) ^ k) ^ k :=
        pow_le_pow_right₀ hBtopOne hgUpper
  have hgLower := fordGoodDegreeSet_card_real_lower hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hexponent :
      -(2 / 25 : ℝ) * k * (g : ℝ) ≤ -((k : ℝ) ^ 2 / 275) := by
    dsimp [g] at hgLower ⊢
    nlinarith
  have hNpow := Real.rpow_le_rpow_of_exponent_le hNreal hexponent
  unfold fordWGoodEnvelope
  rw [mul_pow]
  have hpowerEq :
      (((N : ℝ) ^ (-(2 / 25 : ℝ) * k)) ^ g) =
        (N : ℝ) ^ (-(2 / 25 : ℝ) * k * g) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
  rw [hpowerEq]
  exact mul_le_mul hBpow hNpow (Real.rpow_nonneg hN0 _)
    (pow_nonneg (by positivity) _)

theorem fordScaledSourceCoreMajorant_le_decay
    {k N : ℕ} (hk : 1000 ≤ k) (hN : 1024 ≤ N) :
    fordScaledSourceCoreMajorant k N ≤
      fordScaledCoreCoefficient k *
        (N : ℝ) ^ fordScaledCoreDecayExponent k := by
  have hk1000 : 1000 ≤ k := hk
  have hcompact := fordScaledSourceCoreMajorant_le_compact hk hN
  have henvelope := fordWGoodEnvelope_pow_card_le hk1000 (by omega : 1 ≤ N)
  have hprefix : 0 ≤
      (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
        fordDoubleSquareCoefficient k ^ 2 *
        (N : ℝ) ^ ((3 / 10 : ℝ) * fordDoubleSquareDelta k) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left henvelope hprefix
  have hNpos : (0 : ℝ) < N := by positivity
  calc
    fordScaledSourceCoreMajorant k N ≤
        (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
          fordDoubleSquareCoefficient k ^ 2 *
          (N : ℝ) ^ ((3 / 10 : ℝ) * fordDoubleSquareDelta k) *
          fordWGoodEnvelope k N ^ (fordGoodDegreeSet k).card := hcompact
    _ ≤ (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
          fordDoubleSquareCoefficient k ^ 2 *
          (N : ℝ) ^ ((3 / 10 : ℝ) * fordDoubleSquareDelta k) *
          ((4 * (8 : ℝ) ^ k) ^ k *
            (N : ℝ) ^ (-((k : ℝ) ^ 2 / 275))) := by
      simpa [mul_assoc] using hscaled
    _ = fordScaledCoreCoefficient k *
          (N : ℝ) ^ fordScaledCoreDecayExponent k := by
      unfold fordScaledCoreCoefficient fordScaledCoreDecayExponent
      rw [show
        (10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
              fordDoubleSquareCoefficient k ^ 2 *
              (N : ℝ) ^ ((3 / 10 : ℝ) * fordDoubleSquareDelta k) *
              ((4 * (8 : ℝ) ^ k) ^ k *
                (N : ℝ) ^ (-((k : ℝ) ^ 2 / 275))) =
            ((10 * (fordDoubleSquareDegree k : ℝ) ^ 2) ^ k *
              fordDoubleSquareCoefficient k ^ 2 *
              (4 * (8 : ℝ) ^ k) ^ k) *
              ((N : ℝ) ^ ((3 / 10 : ℝ) * fordDoubleSquareDelta k) *
                (N : ℝ) ^ (-((k : ℝ) ^ 2 / 275))) by ring]
      rw [← Real.rpow_add hNpos]
      ring_nf

theorem ford_exp_neg_sixty_nine_twentieth_le :
    Real.exp (-(69 / 20 : ℝ)) ≤ 1 / 31 := by
  have h := real_exp_neg_le_scaledTaylor
    (z := (69 / 20 : ℝ)) (m := 4) (n := 12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [fordExpTaylorUpper] at h ⊢
  exact h.trans (by norm_num)

theorem fordDoubleSquareDelta_le
    {k : ℕ} (hk : 1000 ≤ k) :
    fordDoubleSquareDelta k ≤ (3 / 248 : ℝ) * (k : ℝ) ^ 2 := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < k := by positivity
  have harg :
      (1 / 2 - 4 + 17 / (10 * (k : ℝ)) : ℝ) ≤ -(69 / 20 : ℝ) := by
    field_simp
    nlinarith
  have hexp := (Real.exp_le_exp.mpr harg).trans
    ford_exp_neg_sixty_nine_twentieth_le
  unfold fordDoubleSquareDelta
  have hfactor : 0 ≤ (3 / 8 : ℝ) * (k : ℝ) ^ 2 := by positivity
  calc
    (3 / 8 : ℝ) * (k : ℝ) ^ 2 *
        Real.exp (1 / 2 - 4 + 17 / (10 * (k : ℝ))) ≤
      (3 / 8 : ℝ) * (k : ℝ) ^ 2 * (1 / 31 : ℝ) := by gcongr
    _ = (3 / 248 : ℝ) * (k : ℝ) ^ 2 := by ring

theorem fordScaledCoreDecayExponent_le
    {k : ℕ} (hk : 1000 ≤ k) :
    fordScaledCoreDecayExponent k ≤ -((k : ℝ) ^ 2 / 136400) := by
  have hdelta := fordDoubleSquareDelta_le hk
  have hk0 : (0 : ℝ) ≤ k := by positivity
  unfold fordScaledCoreDecayExponent
  nlinarith

#print axioms fordVinogradovKappa_cast
#print axioms ford_scaled_core_power_cancellation
#print axioms fordScaledSourceCoreMajorant_le_compact
#print axioms fordScaledSourceCoreMajorant_le_decay
#print axioms fordScaledCoreDecayExponent_le

end

end GafniTao
