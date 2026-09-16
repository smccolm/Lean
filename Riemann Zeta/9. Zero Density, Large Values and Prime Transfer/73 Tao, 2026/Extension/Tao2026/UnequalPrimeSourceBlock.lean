import Tao2026.UnequalMangoldtSourceBlock
import Tao2026.PrimeSourceBlock

open ArithmeticFunction Complex Finset Filter Topology
open scoped BigOperators

namespace Tao2026

noncomputable section

theorem sixtyFour_le_log_rpow_vaughanTypeIILogSavingPhaseExponent
    {B : ℕ} {S : ℝ} (hS : 0 ≤ S) (hlog : 2 ≤ Real.log B) :
    (64 : ℝ) ≤
      (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S := by
  have hd : (6 : ℝ) ≤ vaughanTypeIILogSavingPhaseExponent S := by
    unfold vaughanTypeIILogSavingPhaseExponent
    linarith
  calc
    (64 : ℝ) = (2 : ℝ) ^ (6 : ℝ) := by norm_num
    _ ≤ (Real.log B) ^ (6 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hlog (by norm_num)
    _ ≤ (Real.log B) ^ vaughanTypeIILogSavingPhaseExponent S :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hd

/-- High-frequency prime reciprocal-phase estimate for independent linear and
quadratic coefficients. The same lower scale at `4P` works uniformly for all
initial prefixes used by reverse Abel summation. -/
theorem eventually_norm_primeReciprocalPhaseSum_le_sourceRange_unequal
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A₀ ε S : ℝ} (hA₀ : 0 < A₀) (hε : 0 < ε)
    (haexp : 0 ≤ 3 / 2 - ε) (hS : 0 ≤ S) :
    ∀ᶠ P : ℕ in atTop, ∀ (a b : ℕ) (N M : ℝ),
      P ≤ a → a < b → b ≤ 2 * P → M ≠ 0 →
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) ≤
        reciprocalPhaseScale N M 2 (4 * (P : ℝ)) →
      |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      |M| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
      ‖primeReciprocalPhaseSum a b N M 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
          (Real.log P) ^ (-S) := by
  have hSone : 0 ≤ S + 1 := by linarith
  have hMangoldt :=
    eventually_norm_mangoldtReciprocalPhaseSum_le_sourceRange_unequal
      hVinogradov hA₀ hε haexp hSone
  obtain ⟨K, hK⟩ := eventually_atTop.1 hMangoldt
  have htail :=
    eventually_norm_primePowerTailReciprocalPhaseSum_Ico_le_logSaving (S + 1)
  have hlogLarge : ∀ᶠ P : ℕ in atTop, 2 ≤ Real.log P :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [htail, hlogLarge, eventually_ge_atTop K] with
      P htailP hlogP hPK
  intro a b N M hPa hab hbP hM hlower hNupper hMupper
  have hPpos : 0 < P := by
    by_contra h
    have : P = 0 := Nat.eq_zero_of_not_pos h
    subst P
    norm_num at hlogP
  have haTwo : 2 ≤ a := by
    have hPgt : 2 < P := by
      by_contra h
      have hPle : P ≤ 2 := Nat.le_of_not_gt h
      have hlogle : Real.log P ≤ Real.log 2 := by
        exact Real.log_le_log (by exact_mod_cast hPpos) (by exact_mod_cast hPle)
      nlinarith [Real.log_two_lt_d9]
    omega
  have hPB : P ≤ b := hPa.trans hab.le
  have hPRealPos : (0 : ℝ) < P := by exact_mod_cast hPpos
  have hlogPpos : 0 < Real.log P := by linarith
  have hphaseExp : 0 ≤ vaughanTypeIILogSavingPhaseExponent (S + 1) := by
    unfold vaughanTypeIILogSavingPhaseExponent
    linarith
  have hparameterExp : 0 ≤ 3 / 2 - ε := haexp
  have h64log : (64 : ℝ) ≤
      (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) := by
    have hlogb : 2 ≤ Real.log b := by
      have hlogPb : Real.log P ≤ Real.log b :=
        Real.log_le_log hPRealPos (by exact_mod_cast hPB)
      linarith
    exact sixtyFour_le_log_rpow_vaughanTypeIILogSavingPhaseExponent hSone hlogb
  have h64 : (64 : ℝ) ≤ reciprocalPhaseScale N M 2 (4 * (P : ℝ)) :=
    h64log.trans hlower
  have hpartial : ∀ k, a < k → k ≤ b →
      ‖primeLogReciprocalPhaseSum (Finset.Ico a k) N M 2‖ ≤
        vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
          (Real.log P) ^ (-(S + 1)) := by
    intro k hak hkb
    have hPk : P ≤ k := hPa.trans hak.le
    have hkK : K ≤ k := hPK.trans hPk
    have hkP : k ≤ 2 * P := hkb.trans hbP
    have hkpos : 0 < k := hPpos.trans_le hPk
    have hlogkpos : 0 < Real.log k := by
      apply Real.log_pos
      exact_mod_cast (show 1 < k by omega)
    have hlogkb : Real.log k ≤ Real.log b :=
      Real.log_le_log (by positivity) (by exact_mod_cast hkb)
    have hlogPk : Real.log P ≤ Real.log k :=
      Real.log_le_log hPRealPos (by exact_mod_cast hPk)
    have hpowkb : (Real.log k) ^
          vaughanTypeIILogSavingPhaseExponent (S + 1) ≤
        (Real.log b) ^ vaughanTypeIILogSavingPhaseExponent (S + 1) :=
      Real.rpow_le_rpow hlogkpos.le hlogkb hphaseExp
    have hlowerk : (Real.log k) ^
          vaughanTypeIILogSavingPhaseExponent (S + 1) ≤
        reciprocalPhaseScale N M 2 (4 * (P : ℝ)) := hpowkb.trans hlower
    have hNupperk : |N| ≤
        A₀ * Real.exp ((Real.log k) ^ (3 / 2 - ε)) := by
      have hpowPk : (Real.log P) ^ (3 / 2 - ε) ≤
          (Real.log k) ^ (3 / 2 - ε) :=
        Real.rpow_le_rpow hlogPpos.le hlogPk hparameterExp
      exact hNupper.trans (by gcongr)
    have hMupperk : |M| ≤
        A₀ * Real.exp ((Real.log k) ^ (3 / 2 - ε)) := by
      have hpowPk : (Real.log P) ^ (3 / 2 - ε) ≤
          (Real.log k) ^ (3 / 2 - ε) :=
        Real.rpow_le_rpow hlogPpos.le hlogPk hparameterExp
      exact hMupper.trans (by gcongr)
    have hMangoldtk := hK k hkK P a N M hPpos hPa hak.le hkP hM h64
      hlowerk hNupperk hMupperk
    have hMangoldtUniform :
        ‖mangoldtReciprocalPhaseSum N M 2 a k‖ ≤
          vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1)) := by
      calc
        ‖mangoldtReciprocalPhaseSum N M 2 a k‖ ≤
            vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
              (Real.log k) ^ (-(S + 1)) := hMangoldtk
        _ ≤ vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
              (Real.log P) ^ (-(S + 1)) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hlogPpos hlogPk (by linarith))
            (mul_nonneg (le_of_lt vaughanMangoldtQuadraticDecayConstant_pos)
              (by positivity))
    have htailk := htailP a k N M 2 hPa hak.le hkP
    have hprimeLog := norm_primeLogReciprocalPhaseSum_Ico_le_mangoldt_add_tail
      a k N M 2
    calc
      ‖primeLogReciprocalPhaseSum (Finset.Ico a k) N M 2‖ ≤
          ‖mangoldtReciprocalPhaseSum N M 2 a k‖ +
            ‖primePowerTailReciprocalPhaseSum (Finset.Ico a k) N M 2‖ :=
        hprimeLog
      _ ≤ vaughanMangoldtQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1)) +
          (P : ℝ) * (Real.log P) ^ (-(S + 1)) :=
        add_le_add hMangoldtUniform htailk
      _ = vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1)) := by
        unfold vaughanPrimeQuadraticDecayConstant
        ring
  have habel := norm_primeReciprocalPhaseSum_Ico_le
    N M 2 haTwo hab (B :=
      vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
        (Real.log P) ^ (-(S + 1))) hpartial
  have hlogPa : Real.log P ≤ Real.log a :=
    Real.log_le_log hPRealPos (by exact_mod_cast hPa)
  have hinv : (Real.log a)⁻¹ ≤ (Real.log P)⁻¹ :=
    inv_anti₀ hlogPpos hlogPa
  have hconstant0 : 0 ≤ vaughanPrimeQuadraticDecayConstant * (P : ℝ) :=
    mul_nonneg (le_of_lt vaughanPrimeQuadraticDecayConstant_pos) (by positivity)
  have hpowEq : (Real.log P) ^ (-1 : ℝ) *
      (Real.log P) ^ (-(S + 1)) = (Real.log P) ^ (-(S + 2)) := by
    rw [← Real.rpow_add hlogPpos]
    congr 1
    ring
  calc
    ‖primeReciprocalPhaseSum a b N M 2‖ ≤
        (Real.log a)⁻¹ *
          (vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1))) := habel
    _ ≤ (Real.log P)⁻¹ *
          (vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
            (Real.log P) ^ (-(S + 1))) := by gcongr
    _ = (vaughanPrimeQuadraticDecayConstant * (P : ℝ)) *
          ((Real.log P) ^ (-1 : ℝ) *
            (Real.log P) ^ (-(S + 1))) := by
      rw [Real.rpow_neg_one]
      ring
    _ = vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
          (Real.log P) ^ (-(S + 2)) := by rw [hpowEq]
    _ ≤ vaughanPrimeQuadraticDecayConstant * (P : ℝ) *
          (Real.log P) ^ (-S) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
        hconstant0

end

end Tao2026
