import GafniTao.FordGoodDegreesModerate
import GafniTao.FordLemma65Decay
import GafniTao.FordScaledCoreCompact

/-!
# The Lemma 5.1 core with the Lemma 6.5 moment input

This is the source consumer for Ford's moderate degrees.  It inserts the
fifteen-block Lemma 6.5 moment estimate into the literal complete-window
Lemma 5.1 core and keeps the coefficient separate from the exact `N` power.
-/

namespace GafniTao

noncomputable section

def fordModerateCoreCoefficient (k : ℕ) (C : ℝ) : ℝ :=
  (10 * (fordModerateMomentDegree k : ℝ) ^ 2) ^ k * C ^ 2 *
    (4 * (8 : ℝ) ^ k) ^ k

theorem fordWGoodEnvelope_pow_card_le_nonempty
    {k N : ℕ} (hk : 40 ≤ k) (hN : 1 ≤ N) :
    fordWGoodEnvelope k N ^ (fordGoodDegreeSet k).card ≤
      (4 * (8 : ℝ) ^ k) ^ k * (N : ℝ) ^ (-(2 / 25 : ℝ) * k) := by
  let g : ℕ := (fordGoodDegreeSet k).card
  let B : ℝ := (2 : ℝ) ^ k + 1 + (8 : ℝ) ^ k + 1
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have htwoEight : (2 : ℝ) ^ k ≤ (8 : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) (by norm_num) _
  have honeEight : (1 : ℝ) ≤ (8 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hB : B ≤ 4 * (8 : ℝ) ^ k := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ 4 * (8 : ℝ) ^ k := by linarith
  have hgUpper : g ≤ k := by
    dsimp [g]
    exact fordGoodDegreeSet_card_upper k
  have hgLower : 1 ≤ g := by
    dsimp [g]
    exact one_le_fordGoodDegreeSet_card hk
  have hBpow : B ^ g ≤ (4 * (8 : ℝ) ^ k) ^ k := by
    exact (pow_le_pow_left₀ hB0 hB g).trans
      (pow_le_pow_right₀ hB1 hgUpper)
  have hexponent :
      -(2 / 25 : ℝ) * k * (g : ℝ) ≤ -(2 / 25 : ℝ) * k := by
    have hk0 : (0 : ℝ) ≤ k := by positivity
    have hgLowerR : (1 : ℝ) ≤ g := by exact_mod_cast hgLower
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

theorem fordWGoodEnvelope_pow_card_le_moderate
    {k N : ℕ} (hk : 50 ≤ k) (hN : 1 ≤ N) :
    fordWGoodEnvelope k N ^ (fordGoodDegreeSet k).card ≤
      (4 * (8 : ℝ) ^ k) ^ k *
        (N : ℝ) ^ (-((k : ℝ) ^ 2 / 1250)) := by
  let g : ℕ := (fordGoodDegreeSet k).card
  let B : ℝ := (2 : ℝ) ^ k + 1 + (8 : ℝ) ^ k + 1
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have htwoEight : (2 : ℝ) ^ k ≤ (8 : ℝ) ^ k :=
    pow_le_pow_left₀ (by positivity) (by norm_num) _
  have honeEight : (1 : ℝ) ≤ (8 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hB : B ≤ 4 * (8 : ℝ) ^ k := by dsimp [B]; linarith
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 1 ≤ 4 * (8 : ℝ) ^ k := by linarith
  have hgUpper : g ≤ k := by
    dsimp [g]
    exact fordGoodDegreeSet_card_upper k
  have hBpow : B ^ g ≤ (4 * (8 : ℝ) ^ k) ^ k :=
    (pow_le_pow_left₀ hB0 hB g).trans (pow_le_pow_right₀ hB1 hgUpper)
  have hgLower := fordGoodDegreeSet_card_real_lower_moderate hk
  have hexponent :
      -(2 / 25 : ℝ) * k * (g : ℝ) ≤ -((k : ℝ) ^ 2 / 1250) := by
    dsimp [g] at hgLower ⊢
    have hk0 : (0 : ℝ) ≤ k := by positivity
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

theorem fordLemma51SourceCore_moderate_le_of_envelope
    {k N : ℕ} {t C a : ℝ} (hk : 40 ≤ k)
    (hN : 1024 ≤ N) (ht : 0 < t) (hC : 0 ≤ C)
    (hmoment : FordVinogradovMomentBound
      (fordModerateMomentDegree k) k C (fordModerateMomentDelta k))
    (henvelope : fordWGoodEnvelope k N ^ (fordGoodDegreeSet k).card ≤
      (4 * (8 : ℝ) ^ k) ^ k * (N : ℝ) ^ a)
    (hlower : (69 / 100 : ℝ) * k ≤ fordLambda N t)
    (hupper : fordLambda N t ≤ (7 / 10 : ℝ) * k) :
    fordLemma51SourceCore k 1 k
        (fordModerateMomentDegree k) (fordModerateMomentDegree k)
        ((N : ℝ) ^ (1 / 5 : ℝ)) ((N : ℝ) ^ (1 / 10 : ℝ)) N
        (Finset.Icc 1 ⌊(N : ℝ) ^ (1 / 10 : ℝ)⌋₊) t ≤
      fordModerateCoreCoefficient k C *
        (N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k) *
        (N : ℝ) ^ a := by
  let s := fordModerateMomentDegree k
  let M₁ : ℝ := (N : ℝ) ^ (1 / 5 : ℝ)
  let M₂ : ℝ := (N : ℝ) ^ (1 / 10 : ℝ)
  let M : ℕ := ⌊M₁⌋₊
  let Q : ℕ := ⌊M₂⌋₊
  let delta := fordModerateMomentDelta k
  let E := fordWGoodEnvelope k N
  let g := (fordGoodDegreeSet k).card
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < N := by positivity
  have hN0 : (0 : ℝ) ≤ N := hNpos.le
  obtain ⟨_hM₁two, _hM₂two, hMhalf, hMone, hQone,
      _hM₁top, _hM₂top, _hprodTop⟩ :=
    ford_basic_scale_data (x := (N : ℝ)) (by exact_mod_cast hN)
  obtain ⟨htBottom, htTop⟩ :=
    ford_lambda_band_t_bounds (by omega : 1 < N) ht hlower hupper
  have hsOne : 1 ≤ s := by
    dsimp [s, fordModerateMomentDegree]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hsPos : 0 < s := by omega
  have hMone' : 1 ≤ M := by
    dsimp [M, M₁]
    exact hMone
  have hQone' : 1 ≤ Q := by
    dsimp [Q, M₂]
    exact hQone
  have hgood : ∀ j ∈ fordGoodDegreeSet k,
      fordWNormalizedFactor s M₂ s M N t j ≤ E := by
    intro j hj
    exact fordWNormalizedFactor_good_le (by omega : 6 ≤ k) hNreal ht
      htBottom htTop (by simpa [M, M₁] using hMhalf) hsOne hsOne hj
  have hcore := fordLemma51SourceCore_full_le
    (k := k) (r := s) (s := s) (M := M) (Q := Q) (N := N)
    (M₁ := M₁) (M₂ := M₂) (t := t) (C := C) (delta := delta)
    (q := E) rfl (by dsimp [M₂]; positivity) hsPos hsPos
    hMone' hQone'
    (by positivity) ht hC (by simpa [s, delta] using hmoment)
    (by simpa [s, delta] using hmoment) hgood
  have hMpos : 0 < M := by omega
  have hM₂pos : 0 < M₂ := by dsimp [M₂]; positivity
  have hcancel := ford_scaled_core_power_cancellation
    (k := k) (s := s) (M := M) (g := g) (M₂ := M₂)
    (C := C) (delta := delta) (E := E) hMpos hM₂pos
  have hdelta0 : 0 ≤ delta := by
    dsimp [delta]
    exact fordModerateMomentDelta_nonneg (by omega : 4 ≤ k)
  have hQcast : (Q : ℝ) ≤ M₂ := by
    dsimp [Q]
    exact Nat.floor_le (by positivity)
  have hlambda0 : 0 ≤ fordLambda34 s k delta := by
    unfold fordLambda34
    dsimp [s, fordModerateMomentDegree]
    have hkR : (40 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    nlinarith
  have hQpow : (Q : ℝ) ^ fordLambda34 s k delta ≤
      M₂ ^ fordLambda34 s k delta :=
    Real.rpow_le_rpow (by positivity) hQcast hlambda0
  have hE0 : 0 ≤ E := by
    dsimp [E, fordWGoodEnvelope]
    positivity
  have hEpow0 : 0 ≤ E ^ g := pow_nonneg hE0 _
  have hreplace :
      fordLemma51SourceCore k 1 k s s M₁ M₂ N (Finset.Icc 1 Q) t ≤
        (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (M : ℝ) ^ delta * M₂ ^ delta * E ^ g := by
    apply hcore.trans
    calc
      _ ≤ (5 * (s : ℝ)) ^ k * M₂ ^ (-(2 * s : ℝ)) *
          (M : ℝ) ^ (-(2 * s : ℝ) + fordVinogradovKappa k) *
          (C * (M : ℝ) ^ fordLambda34 s k delta) *
          (C * M₂ ^ fordLambda34 s k delta) *
          ((2 * (s : ℝ)) ^ k * M₂ ^ fordVinogradovKappa k * E ^ g) := by
            gcongr
      _ = _ := hcancel
  have hMcast : (M : ℝ) ≤ M₁ := by
    dsimp [M]
    exact Nat.floor_le (by dsimp [M₁]; positivity)
  have hMpow : (M : ℝ) ^ delta ≤ M₁ ^ delta :=
    Real.rpow_le_rpow (by positivity) hMcast hdelta0
  have hscaleEq : M₁ ^ delta * M₂ ^ delta =
      (N : ℝ) ^ ((3 / 10 : ℝ) * delta) := by
    dsimp [M₁, M₂]
    rw [← Real.rpow_mul hN0, ← Real.rpow_mul hN0,
      ← Real.rpow_add hNpos]
    congr 1
    ring
  calc
    fordLemma51SourceCore k 1 k s s M₁ M₂ N (Finset.Icc 1 Q) t ≤
        (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (M : ℝ) ^ delta * M₂ ^ delta * E ^ g := hreplace
    _ ≤ (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          M₁ ^ delta * M₂ ^ delta * E ^ g := by
            gcongr
    _ = (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (M₁ ^ delta * M₂ ^ delta) * E ^ g := by ring
    _ = (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (N : ℝ) ^ ((3 / 10 : ℝ) * delta) * E ^ g := by
            rw [hscaleEq]
    _ ≤ (10 * (s : ℝ) ^ 2) ^ k * C ^ 2 *
          (N : ℝ) ^ ((3 / 10 : ℝ) * delta) *
          ((4 * (8 : ℝ) ^ k) ^ k *
            (N : ℝ) ^ a) := by gcongr
    _ = fordModerateCoreCoefficient k C *
          (N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k) *
          (N : ℝ) ^ a := by
            dsimp [fordModerateCoreCoefficient, s, delta]
            ring

theorem fordLemma51SourceCore_moderate_le
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
        (N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k) *
        (N : ℝ) ^ (-(2 / 25 : ℝ) * k) := by
  apply fordLemma51SourceCore_moderate_le_of_envelope hk hN ht hC hmoment
  · exact fordWGoodEnvelope_pow_card_le_nonempty hk (by omega)
  · exact hlower
  · exact hupper

theorem fordLemma51SourceCore_moderate_linear_le
    {k N : ℕ} {t C : ℝ} (hk : 50 ≤ k)
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
        (N : ℝ) ^ ((3 / 10 : ℝ) * fordModerateMomentDelta k) *
        (N : ℝ) ^ (-((k : ℝ) ^ 2 / 1250)) := by
  apply fordLemma51SourceCore_moderate_le_of_envelope (by omega) hN ht hC hmoment
  · exact fordWGoodEnvelope_pow_card_le_moderate hk (by omega)
  · exact hlower
  · exact hupper

#print axioms fordWGoodEnvelope_pow_card_le_nonempty
#print axioms fordWGoodEnvelope_pow_card_le_moderate
#print axioms fordLemma51SourceCore_moderate_le_of_envelope
#print axioms fordLemma51SourceCore_moderate_le
#print axioms fordLemma51SourceCore_moderate_linear_le

end

end GafniTao
