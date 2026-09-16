import Tao2026.TypeIWeylBridge
import Tao2026.TypeIISourceBlock

/-!
# Canonical source-scale Type I assembly

This module specializes the exact hybrid Type I estimate to the canonical
cube-root Vaughan cutoffs.  It begins with the arithmetic fact that every
active outer fiber retains a quarter-power inner scale.
-/

open ArithmeticFunction Complex Finset Filter Topology
open scoped BigOperators zeta

namespace Tao2026

noncomputable section

/-- The natural cube-root cutoff has cube at most its source scale. -/
theorem vaughanSourceTailCutoff_pow_three_le (B : ℕ) :
    (vaughanSourceTailCutoff B) ^ 3 ≤ B := by
  by_cases hB : B = 0
  · simp [hB, vaughanSourceTailCutoff]
  · have hBpos : (0 : ℝ) < B := by exact_mod_cast (Nat.pos_of_ne_zero hB)
    have hfloor : (vaughanSourceTailCutoff B : ℝ) ≤
        (B : ℝ) ^ (1 / 3 : ℝ) := by
      exact_mod_cast Nat.floor_le (Real.rpow_nonneg hBpos.le _)
    have hpow : (vaughanSourceTailCutoff B : ℝ) ^ 3 ≤
        ((B : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) hfloor 3
    have hright : ((B : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = B := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBpos.le]
      norm_num
    exact_mod_cast hpow.trans_eq hright

/-- The square of the canonical cube-root cutoff is still bounded by the
ambient scale. -/
theorem vaughanSourceTailCutoff_sq_le (B : ℕ) :
    (vaughanSourceTailCutoff B) ^ 2 ≤ B := by
  let U := vaughanSourceTailCutoff B
  have hcube : U ^ 3 ≤ B := vaughanSourceTailCutoff_pow_three_le B
  by_cases hU : U = 0
  · change U ^ 2 ≤ B
    simp [hU]
  · have hone : 1 ≤ U := Nat.one_le_iff_ne_zero.mpr hU
    calc
      U ^ 2 = U ^ 2 * 1 := by simp
      _ ≤ U ^ 2 * U := Nat.mul_le_mul_left (U ^ 2) hone
      _ = U ^ 3 := by ring
      _ ≤ B := hcube

/-- In particular the canonical cutoff itself is bounded by the ambient
scale. -/
theorem vaughanSourceTailCutoff_le (B : ℕ) :
    vaughanSourceTailCutoff B ≤ B := by
  let U := vaughanSourceTailCutoff B
  by_cases hU : U = 0
  · simp [U, hU]
  · have hone : 1 ≤ U := Nat.one_le_iff_ne_zero.mpr hU
    calc
      U = U * 1 := by simp
      _ ≤ U * U := Nat.mul_le_mul_left U hone
      _ = U ^ 2 := by ring
      _ ≤ B := vaughanSourceTailCutoff_sq_le B

theorem harmonic_cast_mono_nat {m n : ℕ} (hmn : m ≤ n) :
    ((harmonic m : ℚ) : ℝ) ≤ ((harmonic n : ℚ) : ℝ) := by
  calc
    ((harmonic m : ℚ) : ℝ) =
        ∑ i ∈ Finset.Icc 1 m, ((i : ℝ)⁻¹) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ ∑ i ∈ Finset.Icc 1 n, ((i : ℝ)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Icc_subset_Icc_right hmn
      · intro i _ _
        positivity
    _ = ((harmonic n : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Both harmonic cutoff factors in the Type I families cost at most two
ambient logarithms on the source range. -/
theorem harmonic_vaughanSourceTailCutoff_le_two_log
    {B : ℕ} (hlog : 1 ≤ Real.log B) :
    ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ) ≤
      2 * Real.log B := by
  have hmono : ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ) ≤
      ((harmonic B : ℚ) : ℝ) := by
    exact harmonic_cast_mono_nat (vaughanSourceTailCutoff_le B)
  exact hmono.trans ((harmonic_le_one_add_log B).trans (by linarith))

theorem harmonic_vaughanSourceTailCutoff_sq_le_two_log
    {B : ℕ} (hlog : 1 ≤ Real.log B) :
    ((harmonic
      (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ) ≤
      2 * Real.log B := by
  have hsq : vaughanSourceTailCutoff B * vaughanSourceTailCutoff B ≤ B := by
    simpa only [pow_two] using vaughanSourceTailCutoff_sq_le B
  have hmono : ((harmonic
      (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ) ≤
      ((harmonic B : ℚ) : ℝ) := by
    exact harmonic_cast_mono_nat hsq
  exact hmono.trans ((harmonic_le_one_add_log B).trans (by linarith))

/-- Product geometry forces every active second-Type-I fiber to retain at
least half of the canonical cube-root cutoff after ceiling division. -/
theorem vaughanSourceTailCutoff_le_two_mul_ceilDiv_of_activePrime
    {P B U V m : ℕ} {sk : ℕ × ℕ}
    (hBP : B ≤ 2 * P) (hU : U = vaughanSourceTailCutoff B)
    (hV : V = vaughanSourceTailCutoff B)
    (hm : m ∈ vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ))) :
    vaughanSourceTailCutoff B ≤ 2 * (P ⌈/⌉ m) := by
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hm
  have hmUV : m ≤ U * V :=
    mem_vaughanTypeIActiveProductBlockSupport_typeIPrime_imp_le hm
  have hmCut : m ≤ (vaughanSourceTailCutoff B) ^ 2 := by
    simpa only [hU, hV, pow_two] using hmUV
  have hPceil : P ≤ m * (P ⌈/⌉ m) :=
    (ceilDiv_le_iff_le_mul hmpos).1 le_rfl
  have hcube := vaughanSourceTailCutoff_pow_three_le B
  let U₀ := vaughanSourceTailCutoff B
  have hchain : U₀ * U₀ ^ 2 ≤ U₀ ^ 2 * (2 * (P ⌈/⌉ m)) := by
    calc
      U₀ * U₀ ^ 2 = U₀ ^ 3 := by ring
      _ ≤ B := by simpa only [U₀] using hcube
      _ ≤ 2 * P := hBP
      _ ≤ 2 * (m * (P ⌈/⌉ m)) := Nat.mul_le_mul_left 2 hPceil
      _ ≤ 2 * (U₀ ^ 2 * (P ⌈/⌉ m)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (P ⌈/⌉ m) hmCut)
      _ = U₀ ^ 2 * (2 * (P ⌈/⌉ m)) := by ring
  by_cases hUzero : U₀ = 0
  · simp [U₀, hUzero]
  · change U₀ ≤ 2 * (P ⌈/⌉ m)
    have hcancel : U₀ * U₀ ^ 2 ≤ (2 * (P ⌈/⌉ m)) * U₀ ^ 2 := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hchain
    exact Nat.le_of_mul_le_mul_right hcancel (pow_pos (Nat.pos_of_ne_zero hUzero) 2)

/-- The first Type I active support enjoys the same half-cube-root inner-scale
lower bound. -/
theorem vaughanSourceTailCutoff_le_two_mul_ceilDiv_of_activeLog
    {P B U m : ℕ} {sk : ℕ × ℕ}
    (hBP : B ≤ 2 * P) (hU : U = vaughanSourceTailCutoff B)
    (hm : m ∈ vaughanTypeIActiveProductBlockSupport B sk
      (fun m => (vaughanTypeICoefficient U m : ℂ))) :
    vaughanSourceTailCutoff B ≤ 2 * (P ⌈/⌉ m) := by
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hm
  have hmU : m ≤ U :=
    mem_vaughanTypeIActiveProductBlockSupport_typeI_imp_le hm
  have hcutPos : 0 < vaughanSourceTailCutoff B := by
    rw [← hU]
    exact hmpos.trans_le hmU
  have hmCutSq : m ≤ (vaughanSourceTailCutoff B) ^ 2 := by
    have hCutOne : 1 ≤ vaughanSourceTailCutoff B := hcutPos
    calc
      m ≤ vaughanSourceTailCutoff B := by simpa only [hU] using hmU
      _ ≤ (vaughanSourceTailCutoff B) ^ 2 := by
        simpa only [pow_two, Nat.mul_one] using
          Nat.mul_le_mul_left (vaughanSourceTailCutoff B) hCutOne
  have hPceil : P ≤ m * (P ⌈/⌉ m) :=
    (ceilDiv_le_iff_le_mul hmpos).1 le_rfl
  have hcube := vaughanSourceTailCutoff_pow_three_le B
  let U₀ := vaughanSourceTailCutoff B
  have hchain : U₀ * U₀ ^ 2 ≤ U₀ ^ 2 * (2 * (P ⌈/⌉ m)) := by
    calc
      U₀ * U₀ ^ 2 = U₀ ^ 3 := by ring
      _ ≤ B := by simpa only [U₀] using hcube
      _ ≤ 2 * P := hBP
      _ ≤ 2 * (m * (P ⌈/⌉ m)) := Nat.mul_le_mul_left 2 hPceil
      _ ≤ 2 * (U₀ ^ 2 * (P ⌈/⌉ m)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (P ⌈/⌉ m) hmCutSq)
      _ = U₀ ^ 2 * (2 * (P ⌈/⌉ m)) := by ring
  change U₀ ≤ 2 * (P ⌈/⌉ m)
  have hcancel : U₀ * U₀ ^ 2 ≤ (2 * (P ⌈/⌉ m)) * U₀ ^ 2 := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hchain
  exact Nat.le_of_mul_le_mul_right hcancel (pow_pos hcutPos 2)

/-- Every active second-Type-I fiber eventually has rounded scale at least
`B^(1/4)`. -/
theorem eventually_quarter_rpow_le_ceilDiv_of_activePrime :
    ∀ᶠ B : ℕ in atTop, ∀ (P : ℕ) (sk : ℕ × ℕ) (m : ℕ),
      B ≤ 2 * P →
      m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient
          (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B) m : ℂ)) →
      (B : ℝ) ^ (1 / 4 : ℝ) ≤ ((P ⌈/⌉ m : ℕ) : ℝ) := by
  filter_upwards [eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff]
    with B hquarter
  intro P sk m hBP hm
  have hactive := vaughanSourceTailCutoff_le_two_mul_ceilDiv_of_activePrime
    hBP rfl rfl hm
  have hactiveReal : (vaughanSourceTailCutoff B : ℝ) ≤
      2 * ((P ⌈/⌉ m : ℕ) : ℝ) := by exact_mod_cast hactive
  linarith

/-- Every active logarithmic-Type-I fiber eventually has the same
quarter-power rounded-scale lower bound. -/
theorem eventually_quarter_rpow_le_ceilDiv_of_activeLog :
    ∀ᶠ B : ℕ in atTop, ∀ (P : ℕ) (sk : ℕ × ℕ) (m : ℕ),
      B ≤ 2 * P →
      m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient (vaughanSourceTailCutoff B) m : ℂ)) →
      (B : ℝ) ^ (1 / 4 : ℝ) ≤ ((P ⌈/⌉ m : ℕ) : ℝ) := by
  filter_upwards [eventually_two_mul_quarter_rpow_le_vaughanSourceTailCutoff]
    with B hquarter
  intro P sk m hBP hm
  have hactive := vaughanSourceTailCutoff_le_two_mul_ceilDiv_of_activeLog
    hBP rfl hm
  have hactiveReal : (vaughanSourceTailCutoff B : ℝ) ≤
      2 * ((P ⌈/⌉ m : ℕ) : ℝ) := by exact_mod_cast hactive
  linarith

/-- The quarter-power lower bound makes every active second-Type-I rounded
scale eventually exceed any fixed threshold. -/
theorem eventually_forall_activePrime_ceilDiv_ge (K : ℕ) :
    ∀ᶠ B : ℕ in atTop, ∀ (P : ℕ) (sk : ℕ × ℕ) (m : ℕ),
      B ≤ 2 * P →
      m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient
          (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B) m : ℂ)) →
      K ≤ P ⌈/⌉ m := by
  have hpower : ∀ᶠ B : ℕ in atTop,
      (K : ℝ) ≤ (B : ℝ) ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (K : ℝ))
  filter_upwards [eventually_quarter_rpow_le_ceilDiv_of_activePrime, hpower]
    with B hfiber hpowerB
  intro P sk m hBP hm
  exact_mod_cast hpowerB.trans (hfiber P sk m hBP hm)

/-- The corresponding fixed-threshold statement for the first Type I term.
-/
theorem eventually_forall_activeLog_ceilDiv_ge (K : ℕ) :
    ∀ᶠ B : ℕ in atTop, ∀ (P : ℕ) (sk : ℕ × ℕ) (m : ℕ),
      B ≤ 2 * P →
      m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient (vaughanSourceTailCutoff B) m : ℂ)) →
      K ≤ P ⌈/⌉ m := by
  have hpower : ∀ᶠ B : ℕ in atTop,
      (K : ℝ) ≤ (B : ℝ) ^ (1 / 4 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (K : ℝ))
  filter_upwards [eventually_quarter_rpow_le_ceilDiv_of_activeLog, hpower]
    with B hfiber hpowerB
  intro P sk m hBP hm
  exact_mod_cast hpowerB.trans (hfiber P sk m hBP hm)

/-- A ceiling quotient at least two forces its divisor below its numerator.
-/
theorem le_of_two_le_ceilDiv {P m : ℕ} (hm : 0 < m)
    (hD : 2 ≤ P ⌈/⌉ m) :
    m ≤ P := by
  by_contra hnot
  have hPm : P ≤ m := by omega
  have hceil : P ⌈/⌉ m ≤ 1 := by
    apply (ceilDiv_le_iff_le_mul hm).2
    simpa only [mul_one] using hPm
  omega

/-- A quarter-power lower bound converts exactly into the logarithmic lower
bound used by the high-scale Vinogradov parameter package. -/
theorem one_fourth_mul_log_le_log_of_quarter_rpow_le
    {B D : ℕ} (hB : 0 < B)
    (hscale : (B : ℝ) ^ (1 / 4 : ℝ) ≤ (D : ℝ)) :
    (1 / 4 : ℝ) * Real.log B ≤ Real.log D := by
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hpowpos : 0 < (B : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hBreal _
  calc
    (1 / 4 : ℝ) * Real.log B = Real.log ((B : ℝ) ^ (1 / 4 : ℝ)) := by
      rw [Real.log_rpow hBreal]
    _ ≤ Real.log D := Real.log_le_log hpowpos hscale

/-- For canonical second-Type-I active indices, the source frequency bounds
now imply the complete hybrid admissibility predicate with no fiberwise
analytic callback. -/
theorem eventually_forall_activePrime_typeIQuadraticHybridAdmissible
    {A C ε : ℝ} (hA : 1 / 4 ≤ A) (hC : 0 < C)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ B : ℕ in atTop, ∀ (P : ℕ) (N M : ℝ) (sk : ℕ × ℕ) (m : ℕ),
      0 < P → B ≤ 2 * P →
      64 ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale N M 2 P ≤
        C * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient
          (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B) m : ℂ)) →
      TypeIQuadraticHybridAdmissible (B : ℝ) A N M P m := by
  let K : ℕ := ⌈2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))⌉₊
  have hadmReal := eventually_typeIQuadraticHybridAdmissible_of_sourceBounds
    hA hC (by norm_num : (0 : ℝ) < 1 / 4) hε ha
  have hadmNat := tendsto_natCast_atTop_atTop.eventually hadmReal
  filter_upwards [hadmNat, eventually_forall_activePrime_ceilDiv_ge K,
    eventually_quarter_rpow_le_ceilDiv_of_activePrime,
    eventually_gt_atTop (0 : ℕ)] with B hadmB hlargeB hquarterB hB
  intro P N M sk m hP hBP hsource hupper hm
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hm
  have hD : K ≤ P ⌈/⌉ m := hlargeB P sk m hBP hm
  have htwoD : 2 ≤ P ⌈/⌉ m := by
    have hKtwo : 2 ≤ K := by
      norm_num [K]
    exact hKtwo.trans hD
  have hmP : m ≤ P := le_of_two_le_ceilDiv hmpos htwoD
  have hDreal : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) := by
    have hceil : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (K : ℝ) := by
      norm_num [K]
    exact hceil.trans (by exact_mod_cast hD)
  have hlocalUpper := reciprocalPhaseScale_typeI_rescale_ceilDiv_le
    N M 2 hP hmpos
  have hlower := one_fourth_mul_log_le_log_of_quarter_rpow_le hB
    (hquarterB P sk m hBP hm)
  exact hadmB N M P m hP hmpos hmP hDreal hsource
    (hlocalUpper.trans hupper) hlower

/-- Canonical first-Type-I active indices satisfy the same automatic hybrid
admissibility conclusion. -/
theorem eventually_forall_activeLog_typeIQuadraticHybridAdmissible
    {A C ε : ℝ} (hA : 1 / 4 ≤ A) (hC : 0 < C)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ B : ℕ in atTop, ∀ (P : ℕ) (N M : ℝ) (sk : ℕ × ℕ) (m : ℕ),
      0 < P → B ≤ 2 * P →
      64 ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale N M 2 P ≤
        C * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient (vaughanSourceTailCutoff B) m : ℂ)) →
      TypeIQuadraticHybridAdmissible (B : ℝ) A N M P m := by
  let K : ℕ := ⌈2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))⌉₊
  have hadmReal := eventually_typeIQuadraticHybridAdmissible_of_sourceBounds
    hA hC (by norm_num : (0 : ℝ) < 1 / 4) hε ha
  have hadmNat := tendsto_natCast_atTop_atTop.eventually hadmReal
  filter_upwards [hadmNat, eventually_forall_activeLog_ceilDiv_ge K,
    eventually_quarter_rpow_le_ceilDiv_of_activeLog,
    eventually_gt_atTop (0 : ℕ)] with B hadmB hlargeB hquarterB hB
  intro P N M sk m hP hBP hsource hupper hm
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hm
  have hD : K ≤ P ⌈/⌉ m := hlargeB P sk m hBP hm
  have htwoD : 2 ≤ P ⌈/⌉ m := by
    have hKtwo : 2 ≤ K := by
      norm_num [K]
    exact hKtwo.trans hD
  have hmP : m ≤ P := le_of_two_le_ceilDiv hmpos htwoD
  have hDreal : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) := by
    have hceil : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (K : ℝ) := by
      norm_num [K]
    exact hceil.trans (by exact_mod_cast hD)
  have hlocalUpper := reciprocalPhaseScale_typeI_rescale_ceilDiv_le
    N M 2 hP hmpos
  have hlower := one_fourth_mul_log_le_log_of_quarter_rpow_le hB
    (hquarterB P sk m hBP hm)
  exact hadmB N M P m hP hmpos hmP hDreal hsource
    (hlocalUpper.trans hupper) hlower

/-! ## Low-branch logarithmic envelope -/

/-- Explicit low-Weyl envelope after replacing both decay terms by the same
ambient logarithmic power. -/
noncomputable def typeIQuadraticLowLogEnvelope
    (B d : ℝ) (D : ℕ) : ℝ :=
  typeIQuadraticWeylConstant * D * (1 + Real.log B) *
    (17 * (Real.log B) ^ (-d)) ^ (1 / 1024 : ℝ)

theorem typeIQuadraticLowLogEnvelope_nonneg
    {B d : ℝ} {D : ℕ} (hlog : 0 ≤ Real.log B) :
    0 ≤ typeIQuadraticLowLogEnvelope B d D := by
  unfold typeIQuadraticLowLogEnvelope typeIQuadraticWeylConstant
  positivity

/-- The source logarithmic phase lower bound, active quarter-power geometry,
and the low-scale branch reduce the exact rescaled Weyl majorant to the
explicit ambient logarithmic envelope. -/
theorem typeIQuadraticRescaledWeylMajorant_le_lowLogEnvelope
    (N M : ℝ) {B P m : ℕ} {d : ℝ}
    (hB : 0 < B) (hP : 0 < P) (hm : 0 < m) (hmP : m ≤ P)
    (hPB : P ≤ B) (hlog : 0 < Real.log B)
    (hquarter : (B : ℝ) ^ (1 / 4 : ℝ) ≤ (P ⌈/⌉ m : ℕ))
    (hpower : (B : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      (Real.log B) ^ (-d))
    (hsource : (Real.log B) ^ d ≤ reciprocalPhaseScale N M 2 P)
    (hlow : reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
        ((P ⌈/⌉ m : ℕ) : ℝ) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4) :
    typeIQuadraticRescaledWeylMajorant N M P m ≤
      typeIQuadraticLowLogEnvelope B d (P ⌈/⌉ m) := by
  have hDposNat : 0 < P ⌈/⌉ m := typeI_ceilDiv_pos hP hm
  have hDpos : (0 : ℝ) < (P ⌈/⌉ m : ℕ) := by exact_mod_cast hDposNat
  have hDleP : P ⌈/⌉ m ≤ P := ceilDiv_le_self_of_pos P m hm
  have hDleB : P ⌈/⌉ m ≤ B := hDleP.trans hPB
  have hlogD : Real.log ((P ⌈/⌉ m : ℕ) : ℝ) ≤ Real.log B :=
    Real.log_le_log hDpos (by exact_mod_cast hDleB)
  have hlogpow : 0 < (Real.log B) ^ d := Real.rpow_pos_of_pos hlog _
  have hwidth := typeIQuadraticWeylSourceWidth_le_of_sourceLogScale
    N M B d hP hm hmP hlogpow hsource hlow
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hBquarter : 0 < (B : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos hBreal _
  have hinvD : 1 / ((P ⌈/⌉ m : ℕ) : ℝ) ≤
      (B : ℝ) ^ (-(1 / 4 : ℝ)) := by
    calc
      1 / ((P ⌈/⌉ m : ℕ) : ℝ) ≤
      1 / ((B : ℝ) ^ (1 / 4 : ℝ)) :=
        one_div_le_one_div_of_le hBquarter hquarter
      _ = (B : ℝ) ^ (-(1 / 4 : ℝ)) := by
        rw [Real.rpow_neg hBreal.le]
        rw [one_div]
  have hlogneg : 0 < (Real.log B) ^ (-d) := Real.rpow_pos_of_pos hlog _
  have hinverseLog : 16 / (Real.log B) ^ d =
      16 * (Real.log B) ^ (-d) := by
    rw [Real.rpow_neg hlog.le]
    ring
  have hinside :
      1 / ((P ⌈/⌉ m : ℕ) : ℝ) + 16 / (Real.log B) ^ d ≤
        17 * (Real.log B) ^ (-d) := by
    rw [hinverseLog]
    calc
      1 / ((P ⌈/⌉ m : ℕ) : ℝ) +
          16 * (Real.log B) ^ (-d) ≤
        (Real.log B) ^ (-d) + 16 * (Real.log B) ^ (-d) := by
          gcongr
          exact hinvD.trans hpower
      _ = 17 * (Real.log B) ^ (-d) := by ring
  have hwidth' : typeIQuadraticWeylSourceWidth
      (N / m) (M / (m : ℝ) ^ 2) (P ⌈/⌉ m) ≤
      (17 * (Real.log B) ^ (-d)) ^ (1 / 1024 : ℝ) :=
    hwidth.trans (Real.rpow_le_rpow (by positivity) hinside (by norm_num))
  rw [typeIQuadraticRescaledWeylMajorant_eq]
  unfold typeIQuadraticLowLogEnvelope
  have hC : 0 ≤ typeIQuadraticWeylConstant := by
    unfold typeIQuadraticWeylConstant
    positivity
  have hD : (0 : ℝ) ≤ (P ⌈/⌉ m : ℕ) := by positivity
  have hlogDnonneg : 0 ≤ 1 + Real.log ((P ⌈/⌉ m : ℕ) : ℝ) := by
    have : 0 ≤ Real.log ((P ⌈/⌉ m : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hDposNat)
    linarith
  have htarget : 0 ≤
      (17 * (Real.log B) ^ (-d)) ^ (1 / 1024 : ℝ) := by positivity
  calc
    typeIQuadraticWeylConstant * (P ⌈/⌉ m : ℕ) *
        (1 + Real.log ((P ⌈/⌉ m : ℕ) : ℝ)) *
        typeIQuadraticWeylSourceWidth
          (N / m) (M / (m : ℝ) ^ 2) (P ⌈/⌉ m) ≤
      typeIQuadraticWeylConstant * (P ⌈/⌉ m : ℕ) *
        (1 + Real.log ((P ⌈/⌉ m : ℕ) : ℝ)) *
        (17 * (Real.log B) ^ (-d)) ^ (1 / 1024 : ℝ) := by
          apply mul_le_mul_of_nonneg_left hwidth'
          positivity
    _ ≤ typeIQuadraticWeylConstant * (P ⌈/⌉ m : ℕ) *
        (1 + Real.log B) *
        (17 * (Real.log B) ^ (-d)) ^ (1 / 1024 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ htarget
      apply mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC hD)

/-- With one explicit exponent budget, the complete low-Weyl envelope has
arbitrary logarithmic saving proportional to the rounded fiber length. -/
theorem typeIQuadraticLowLogEnvelope_le_logSaving
    {B d T : ℝ} {D : ℕ}
    (hlog : 17 ≤ Real.log B)
    (hd : 1024 * (T + 1) + 1 ≤ d) :
    typeIQuadraticLowLogEnvelope B d D ≤
      2 * typeIQuadraticWeylConstant * D * (Real.log B) ^ (-T) := by
  have hlogpos : 0 < Real.log B := by linarith
  have hlogone : 1 ≤ Real.log B := by linarith
  have hnegpow : 0 ≤ (Real.log B) ^ (-d) :=
    Real.rpow_nonneg hlogpos.le _
  have hbase : 17 * (Real.log B) ^ (-d) ≤
      (Real.log B) ^ (1 - d) := by
    calc
      17 * (Real.log B) ^ (-d) ≤
          Real.log B * (Real.log B) ^ (-d) := by
        exact mul_le_mul_of_nonneg_right hlog hnegpow
      _ = (Real.log B) ^ (1 - d) := by
        calc
          Real.log B * (Real.log B) ^ (-d) =
              (Real.log B) ^ (1 : ℝ) * (Real.log B) ^ (-d) := by
                rw [Real.rpow_one]
          _ = (Real.log B) ^ ((1 : ℝ) + (-d)) :=
            (Real.rpow_add hlogpos 1 (-d)).symm
          _ = (Real.log B) ^ (1 - d) := by ring_nf
  have hroot :
      (17 * (Real.log B) ^ (-d)) ^ (1 / 1024 : ℝ) ≤
        (Real.log B) ^ ((1 - d) / 1024) := by
    calc
      (17 * (Real.log B) ^ (-d)) ^ (1 / 1024 : ℝ) ≤
          ((Real.log B) ^ (1 - d)) ^ (1 / 1024 : ℝ) := by
        exact Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      _ = (Real.log B) ^ ((1 - d) / 1024) := by
        rw [← Real.rpow_mul hlogpos.le]
        congr 1
        ring
  have hexp : 1 + (1 - d) / 1024 ≤ -T := by
    linarith
  have hpow : (Real.log B) ^ (1 + (1 - d) / 1024) ≤
      (Real.log B) ^ (-T) :=
    Real.rpow_le_rpow_of_exponent_le hlogone hexp
  have hC : 0 ≤ typeIQuadraticWeylConstant := by
    unfold typeIQuadraticWeylConstant
    positivity
  have hD : (0 : ℝ) ≤ D := by positivity
  have hfactor : 1 + Real.log B ≤ 2 * Real.log B := by linarith
  unfold typeIQuadraticLowLogEnvelope
  calc
    typeIQuadraticWeylConstant * (D : ℝ) * (1 + Real.log B) *
        (17 * (Real.log B) ^ (-d)) ^ (1 / 1024 : ℝ) ≤
      typeIQuadraticWeylConstant * (D : ℝ) * (2 * Real.log B) *
        (Real.log B) ^ ((1 - d) / 1024) := by
          gcongr
    _ = 2 * typeIQuadraticWeylConstant * (D : ℝ) *
        (Real.log B) ^ (1 + (1 - d) / 1024) := by
      have hmul : Real.log B * (Real.log B) ^ ((1 - d) / 1024) =
          (Real.log B) ^ (1 + (1 - d) / 1024) := by
        calc
          Real.log B * (Real.log B) ^ ((1 - d) / 1024) =
              (Real.log B) ^ (1 : ℝ) *
                (Real.log B) ^ ((1 - d) / 1024) := by rw [Real.rpow_one]
          _ = (Real.log B) ^ ((1 : ℝ) + (1 - d) / 1024) :=
            (Real.rpow_add hlogpos 1 ((1 - d) / 1024)).symm
      calc
        typeIQuadraticWeylConstant * (D : ℝ) * (2 * Real.log B) *
            (Real.log B) ^ ((1 - d) / 1024) =
          2 * typeIQuadraticWeylConstant * (D : ℝ) *
            (Real.log B * (Real.log B) ^ ((1 - d) / 1024)) := by ring
        _ = 2 * typeIQuadraticWeylConstant * (D : ℝ) *
            (Real.log B) ^ (1 + (1 - d) / 1024) := by rw [hmul]
    _ ≤ 2 * typeIQuadraticWeylConstant * (D : ℝ) *
        (Real.log B) ^ (-T) := by
      apply mul_le_mul_of_nonneg_left hpow
      positivity

/-- One absolute coefficient dominates the absorbed low-Weyl coefficient and
the high-Vinogradov coefficient. -/
noncomputable def typeIQuadraticBranchDecayConstant : ℝ :=
  2 * typeIQuadraticWeylConstant + 3

theorem typeIQuadraticBranchDecayConstant_pos :
    0 < typeIQuadraticBranchDecayConstant := by
  unfold typeIQuadraticBranchDecayConstant typeIQuadraticWeylConstant
  positivity

/-- Both analytic branches satisfy the same logarithmically saving envelope,
proportional to the rounded Type I fiber length.  The low branch uses the
explicit Weyl exponent budget; the high branch uses the source Vinogradov
envelope theorem. -/
theorem eventually_typeIQuadraticRescaledBranchMajorantAt_le_logSaving
    {C₀ C₁ ε A d T : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε)
    (hAT : T + 2 ≤ 3 * A)
    (hd : 1024 * (T + 1) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P m : ℕ) (N M : ℝ),
      0 < P → 0 < m → m ≤ P → P ≤ B →
      2 ≤ P ⌈/⌉ m →
      (B : ℝ) ^ (1 / 4 : ℝ) ≤ (P ⌈/⌉ m : ℕ) →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      typeIQuadraticRescaledBranchMajorantAt C₁ B A N M P m ≤
        typeIQuadraticBranchDecayConstant * (P ⌈/⌉ m : ℕ) *
          (Real.log B) ^ (-T) := by
  have hpowerReal := eventually_rpow_neg_le_log_rpow_neg
    (by norm_num : (0 : ℝ) < 1 / 4) d
  have hpowerNat := tendsto_natCast_atTop_atTop.eventually hpowerReal
  have hhighReal :=
    eventually_typeIQuadraticRescaledVinogradovMajorantAt_le
      hC₀ hC₁ (by norm_num : (0 : ℝ) < 1 / 4) hε ha hAT
  have hhighNat := tendsto_natCast_atTop_atTop.eventually hhighReal
  have hlogNat : ∀ᶠ B : ℕ in atTop, 17 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 17)
  filter_upwards [hpowerNat, hhighNat, hlogNat,
    eventually_gt_atTop (0 : ℕ)] with B hpowerB hhighB hlogB hB
  intro P m N M hP hm hmP hPB hD hquarter hsource hupper
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  let F := reciprocalPhaseScale N' M' 2 D
  have hlogpowNonneg : 0 ≤ (Real.log B) ^ (-T) :=
    Real.rpow_nonneg (by linarith : 0 ≤ Real.log B) _
  have hDnonneg : (0 : ℝ) ≤ D := by positivity
  have hCweyl : 0 ≤ typeIQuadraticWeylConstant := by
    unfold typeIQuadraticWeylConstant
    positivity
  by_cases hlow : F ≤ (D : ℝ) ^ 4
  · have hweyl := typeIQuadraticRescaledWeylMajorant_le_lowLogEnvelope
      N M hB hP hm hmP hPB (by linarith) hquarter hpowerB hsource
        (by simpa only [D, N', M', F] using hlow)
    have habsorb := typeIQuadraticLowLogEnvelope_le_logSaving hlogB hd
      (D := D)
    have hbound : typeIQuadraticRescaledWeylMajorant N M P m ≤
        typeIQuadraticBranchDecayConstant * (D : ℝ) *
          (Real.log B) ^ (-T) := by
      calc
        typeIQuadraticRescaledWeylMajorant N M P m ≤
            typeIQuadraticLowLogEnvelope B d D := hweyl
        _ ≤ 2 * typeIQuadraticWeylConstant * (D : ℝ) *
            (Real.log B) ^ (-T) := habsorb
        _ ≤ typeIQuadraticBranchDecayConstant * (D : ℝ) *
            (Real.log B) ^ (-T) := by
          unfold typeIQuadraticBranchDecayConstant
          gcongr
          linarith
    simpa only [typeIQuadraticRescaledBranchMajorantAt, D, N', M', F,
      if_pos hlow] using hbound
  · have hhigh : (D : ℝ) ^ 4 ≤ F := le_of_lt (lt_of_not_ge hlow)
    have hlower := one_fourth_mul_log_le_log_of_quarter_rpow_le hB hquarter
    have hvin := hhighB N M P m hD
      (by simpa only [D, N', M', F] using hhigh)
      (by simpa only [D, N', M', F] using hupper)
      (by simpa only [D] using hlower)
    have hbound :
        typeIQuadraticRescaledVinogradovMajorantAt C₁ B A N M P m ≤
          typeIQuadraticBranchDecayConstant * (D : ℝ) *
            (Real.log B) ^ (-T) := by
      calc
        typeIQuadraticRescaledVinogradovMajorantAt C₁ B A N M P m ≤
            3 * (D : ℝ) * (Real.log B) ^ (-T) := by
              simpa only [D] using hvin
        _ ≤ typeIQuadraticBranchDecayConstant * (D : ℝ) *
            (Real.log B) ^ (-T) := by
          unfold typeIQuadraticBranchDecayConstant
          gcongr
          linarith
    simpa only [typeIQuadraticRescaledBranchMajorantAt, D, N', M', F,
      if_neg hlow] using hbound

/-- Ceiling rounding converts a decay envelope proportional to
`ceil(P/m)` into the reciprocal-weighted form consumed by the family
aggregation theorems. -/
theorem typeIQuadraticBranchDecay_ceilDiv_le_invWeighted
    {P m : ℕ} {L : ℝ} (hm : 0 < m) (hmP : m ≤ P) (hL : 0 ≤ L) :
    typeIQuadraticBranchDecayConstant * (P ⌈/⌉ m : ℕ) * L ≤
      (P : ℝ) / m * (2 * typeIQuadraticBranchDecayConstant * L) := by
  have hceil := ceilDiv_cast_le_two_mul_div hm hmP
  have hC : 0 ≤ typeIQuadraticBranchDecayConstant :=
    typeIQuadraticBranchDecayConstant_pos.le
  calc
    typeIQuadraticBranchDecayConstant * (P ⌈/⌉ m : ℕ) * L ≤
        typeIQuadraticBranchDecayConstant * (2 * (P : ℝ) / m) * L := by
      gcongr
    _ = (P : ℝ) / m * (2 * typeIQuadraticBranchDecayConstant * L) := by
      ring

/-- Reciprocal-weighted form of the common branch envelope. -/
theorem eventually_typeIQuadraticRescaledBranchMajorantAt_le_invWeighted
    {C₀ C₁ ε A d T : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε)
    (hAT : T + 2 ≤ 3 * A)
    (hd : 1024 * (T + 1) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P m : ℕ) (N M : ℝ),
      0 < P → 0 < m → m ≤ P → P ≤ B →
      2 ≤ P ⌈/⌉ m →
      (B : ℝ) ^ (1 / 4 : ℝ) ≤ (P ⌈/⌉ m : ℕ) →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      typeIQuadraticRescaledBranchMajorantAt C₁ B A N M P m ≤
        (P : ℝ) / m *
          (2 * typeIQuadraticBranchDecayConstant * (Real.log B) ^ (-T)) := by
  have hbase := eventually_typeIQuadraticRescaledBranchMajorantAt_le_logSaving
    hC₀ hC₁ hε ha hAT hd
  filter_upwards [hbase] with B hbaseB
  intro P m N M hP hm hmP hPB hD hquarter hsource hupper
  have hBone : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hL : 0 ≤ (Real.log B) ^ (-T) :=
    Real.rpow_nonneg (Real.log_nonneg hBone) _
  exact (hbaseB P m N M hP hm hmP hPB hD hquarter hsource hupper).trans
    (typeIQuadraticBranchDecay_ceilDiv_le_invWeighted hm hmP hL)

/-! ## Reciprocal-weighted active-family summation -/

/-- The active first-Type-I support pays only a harmonic sum when a fiber
estimate retains its natural reciprocal outer-index factor. -/
theorem sum_inv_vaughanTypeIActiveLogSupport_le_harmonic
    (B U : ℕ) (sk : ℕ × ℕ) :
    ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)),
      ((m : ℝ)⁻¹) ≤ ((harmonic U : ℚ) : ℝ) := by
  have hsubset :
      vaughanTypeIActiveProductBlockSupport B sk
          (fun m => (vaughanTypeICoefficient U m : ℂ)) ⊆
        Finset.Icc 1 U := by
    intro m hm
    exact Finset.mem_Icc.mpr
      ⟨pos_of_mem_vaughanTypeIActiveProductBlockSupport hm,
        mem_vaughanTypeIActiveProductBlockSupport_typeI_imp_le hm⟩
  calc
    ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)), ((m : ℝ)⁻¹) ≤
        ∑ m ∈ Finset.Icc 1 U, ((m : ℝ)⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro m _ _
        positivity)
    _ = ((harmonic U : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- The active second-Type-I support has the analogous harmonic bound at its
literal convolution cutoff `U*V`. -/
theorem sum_inv_vaughanTypeIActivePrimeSupport_le_harmonic
    (B U V : ℕ) (sk : ℕ × ℕ) :
    ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
      ((m : ℝ)⁻¹) ≤ ((harmonic (U * V) : ℚ) : ℝ) := by
  have hsubset :
      vaughanTypeIActiveProductBlockSupport B sk
          (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)) ⊆
        Finset.Icc 1 (U * V) := by
    intro m hm
    exact Finset.mem_Icc.mpr
      ⟨pos_of_mem_vaughanTypeIActiveProductBlockSupport hm,
        mem_vaughanTypeIActiveProductBlockSupport_typeIPrime_imp_le hm⟩
  calc
    ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)), ((m : ℝ)⁻¹) ≤
        ∑ m ∈ Finset.Icc 1 (U * V), ((m : ℝ)⁻¹) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro m _ _
        positivity)
    _ = ((harmonic (U * V) : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- Complete first-Type-I aggregation for a fiber estimate proportional to
`P/m`. This replaces the former cardinality loss `U` by the exact harmonic
factor at the active cutoff. -/
theorem norm_weightedConvolutionProductVaughanTypeILogSum_le_invWeighted
    (I : Finset ℕ) (B U P : ℕ) (N M : ℝ) (j : ℕ)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hinner : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)),
        ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun n => (Real.log n : ℂ)) N M j m‖ ≤ (P : ℝ) / m * Q) :
    ‖weightedConvolutionProductSum I B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeICoefficient U) log‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        ((P : ℝ) * Q * ((harmonic U : ℚ) : ℝ)) := by
  refine (norm_weightedConvolutionProductVaughanTypeILogSum_le_active
    I B U N M j).trans ?_
  calc
    ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
            (fun m => (vaughanTypeICoefficient U m : ℂ)),
          ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
            (fun n => (Real.log n : ℂ)) N M j m‖ ≤
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
        ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
            (fun m => (vaughanTypeICoefficient U m : ℂ)),
          ((P : ℝ) / m * Q) := by
      apply Finset.sum_le_sum
      intro sk hsk
      apply Finset.sum_le_sum
      intro m hm
      exact hinner sk hsk m hm
    _ ≤ ∑ _sk ∈ vaughanShortIntervalIndexBox B,
        ((P : ℝ) * Q * ((harmonic U : ℚ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro sk _hsk
      calc
        ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
            (fun m => (vaughanTypeICoefficient U m : ℂ)),
            ((P : ℝ) / m * Q) =
            (P : ℝ) * Q *
              ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
                (fun m => (vaughanTypeICoefficient U m : ℂ)),
                ((m : ℝ)⁻¹) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro m _hm
          ring
        _ ≤ (P : ℝ) * Q * ((harmonic U : ℚ) : ℝ) := by
          apply mul_le_mul_of_nonneg_left
            (sum_inv_vaughanTypeIActiveLogSupport_le_harmonic B U sk)
          positivity
    _ = (Nat.log 2 B + 1 : ℕ) ^ 102 *
        ((P : ℝ) * Q * ((harmonic U : ℚ) : ℝ)) := by
      rw [Finset.sum_const, card_vaughanShortIntervalIndexBox]
      push_cast
      ring

/-- Complete second-Type-I aggregation with the same reciprocal weighting;
the only additional loss is the already exact source zeta envelope. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_invWeighted
    (I : Finset ℕ) (B U V P : ℕ) (hB : 0 < B)
    (N M : ℝ) (j : ℕ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hinner : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
        ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
          (fun _ => 1) N M j m‖ ≤ (P : ℝ) / m * Q) :
    ‖weightedConvolutionProductSum I B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M j n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        (Real.log (2 * B) *
          ((P : ℝ) * Q * ((harmonic (U * V) : ℚ) : ℝ))) := by
  refine (norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_active
    I B U V hB N M j).trans ?_
  have hlog : 0 ≤ Real.log (2 * B) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * B)
  have hsum :
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
              (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ ≤
        ∑ _sk ∈ vaughanShortIntervalIndexBox B,
          ((P : ℝ) * Q * ((harmonic (U * V) : ℚ) : ℝ)) := by
    calc
      ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
              (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ ≤
        ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
              (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
            ((P : ℝ) / m * Q) := by
        apply Finset.sum_le_sum
        intro sk hsk
        apply Finset.sum_le_sum
        intro m hm
        exact hinner sk hsk m hm
      _ ≤ ∑ _sk ∈ vaughanShortIntervalIndexBox B,
          ((P : ℝ) * Q * ((harmonic (U * V) : ℚ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro sk _hsk
        calc
          ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
              (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
              ((P : ℝ) / m * Q) =
              (P : ℝ) * Q *
                ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
                  (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
                  ((m : ℝ)⁻¹) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m _hm
            ring
          _ ≤ (P : ℝ) * Q * ((harmonic (U * V) : ℚ) : ℝ) := by
            apply mul_le_mul_of_nonneg_left
              (sum_inv_vaughanTypeIActivePrimeSupport_le_harmonic B U V sk)
            positivity
  calc
    Real.log (2 * B) *
        ∑ sk ∈ vaughanShortIntervalIndexBox B,
          ∑ m ∈ vaughanTypeIActiveProductBlockSupport B sk
              (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
            ‖typeIProductRestrictedWeightedInnerSum I (Finset.Ioc 0 B)
              (fun _ => 1) N M j m‖ ≤
      Real.log (2 * B) *
        ∑ _sk ∈ vaughanShortIntervalIndexBox B,
          ((P : ℝ) * Q * ((harmonic (U * V) : ℚ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hlog
    _ = (Nat.log 2 B + 1 : ℕ) ^ 102 *
        (Real.log (2 * B) *
          ((P : ℝ) * Q * ((harmonic (U * V) : ℚ) : ℝ))) := by
      rw [Finset.sum_const, card_vaughanShortIntervalIndexBox]
      push_cast
      ring

/-! ## Canonical source Type I family bounds -/

/-- The complete second Vaughan Type I family now has a logarithmically
saving bound under only the global source-frequency hypotheses.  All active
fiber admissibility, branch selection, ceiling losses, and outer summation are
discharged internally. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_source
    {C₀ C₁ ε A d T : ℝ}
    (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hVinogradov : VinogradovExponentialSumEstimateAt C₁)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε)
    (hAT : T + 2 ≤ 3 * A)
    (hd : 1024 * (T + 1) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a b : ℕ) (N M : ℝ),
      0 < P → P ≤ a → b ≤ 2 * P → 0 < a → b ≤ B →
      P ≤ B → B ≤ 2 * P → M ≠ 0 →
      64 ≤ reciprocalPhaseScale N M 2 P →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale N M 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖weightedConvolutionProductSum (Finset.Ico a b) B
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeIPrimeCoefficient
            (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B))
          (ζ : ArithmeticFunction ℝ)‖ ≤
        (Nat.log 2 B + 1 : ℕ) ^ 102 *
          (Real.log (2 * B) *
            ((P : ℝ) *
              (2 * typeIQuadraticBranchDecayConstant *
                (Real.log B) ^ (-T)) *
              ((harmonic
                (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ))) := by
  let K : ℕ := ⌈2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))⌉₊
  have hadm := eventually_forall_activePrime_typeIQuadraticHybridAdmissible
    hA hC₀ hε haexp
  have hlarge := eventually_forall_activePrime_ceilDiv_ge K
  have hquarter := eventually_quarter_rpow_le_ceilDiv_of_activePrime
  have hmajor := eventually_typeIQuadraticRescaledBranchMajorantAt_le_invWeighted
    hC₀ hC₁ hε haexp hAT hd
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hApos : 0 < A := by linarith
  have hten : ∀ᶠ B : ℕ in atTop, 10 ≤ (Real.log (B : ℝ)) ^ A :=
    ((tendsto_rpow_atTop hApos).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop 10)
  filter_upwards [hadm, hlarge, hquarter, hmajor, hlog, hten,
    eventually_gt_atTop (0 : ℕ)] with
      B hadmB hlargeB hquarterB hmajorB hlogB htenB hB
  intro P a b N M hP hPa hbP ha hbB hPB hBP hM hsource64 hsource hupper
  have hQ : 0 ≤
      2 * typeIQuadraticBranchDecayConstant * (Real.log B) ^ (-T) := by
    have hlogNonneg : 0 ≤ Real.log (B : ℝ) := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num)
      typeIQuadraticBranchDecayConstant_pos.le)
        (Real.rpow_nonneg hlogNonneg _)
  apply norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_invWeighted
    (Finset.Ico a b) B (vaughanSourceTailCutoff B)
      (vaughanSourceTailCutoff B) P hB N M 2 hQ
  intro sk hsk m hmActive
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hmActive
  have hD : K ≤ P ⌈/⌉ m := hlargeB P sk m hBP hmActive
  have htwoD : 2 ≤ P ⌈/⌉ m := by
    have hKtwo : 2 ≤ K := by norm_num [K]
    exact hKtwo.trans hD
  have hmP : m ≤ P := le_of_two_le_ceilDiv hmpos htwoD
  have hDreal : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) := by
    have hceil : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (K : ℝ) := by
      norm_num [K]
    exact hceil.trans (by exact_mod_cast hD)
  have hadmFiber := hadmB P N M sk m hP hBP hsource64 hupper hmActive
  have hbudget :
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4 →
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
              ((P ⌈/⌉ m : ℕ) : ℝ) /
            ((P ⌈/⌉ m : ℕ) : ℝ) ^ 5) +
        1 / 16 +
          4 / reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
            ((P ⌈/⌉ m : ℕ) : ℝ) ≤ 1 := by
    intro hlow
    exact typeIQuadraticWeylBudget_of_sourceScale
      N M hP hmpos hmP hDreal hsource64 hlow
  have hlocalUpper := reciprocalPhaseScale_typeI_rescale_ceilDiv_le
    N M 2 hP hmpos
  have hmajorFiber := hmajorB P m N M hP hmpos hmP hPB htwoD
    (hquarterB P sk m hBP hmActive) hsource (hlocalUpper.trans hupper)
  exact (norm_typeIProductRestrictedInnerSum_Ico_le_quadraticBranchAt
    C₁ hVinogradov B A N M hPa hbP ha hbB hmpos hM
      hlogB hA htenB hadmFiber hbudget).trans hmajorFiber

/-- The one Abel logarithm converts a reciprocal-weighted exponent `T` into
`T-1`, with an explicit factor two. -/
theorem two_mul_log_ceilDiv_mul_branchDecay_le_invWeighted
    {B P b m : ℕ} {T : ℝ}
    (hm : 0 < m) (hb : 0 < b) (hbB : b ≤ B)
    (hlogB : 0 < Real.log (B : ℝ)) :
    2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        ((P : ℝ) / m *
          (2 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-T))) ≤
      (P : ℝ) / m *
        (4 * typeIQuadraticBranchDecayConstant *
          (Real.log B) ^ (-(T - 1))) := by
  have hceilPos : 0 < b ⌈/⌉ m := typeI_ceilDiv_pos hb hm
  have hceilLe : b ⌈/⌉ m ≤ b := ceilDiv_le_self_of_pos b m hm
  have hceilB : b ⌈/⌉ m ≤ B := hceilLe.trans hbB
  have hlogCeil :
      Real.log ((b ⌈/⌉ m : ℕ) : ℝ) ≤ Real.log B :=
    Real.log_le_log (by exact_mod_cast hceilPos) (by exact_mod_cast hceilB)
  have hlogCeilNonneg :
      0 ≤ Real.log ((b ⌈/⌉ m : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hceilPos)
  have hpowNonneg : 0 ≤ (Real.log B) ^ (-T) :=
    Real.rpow_nonneg hlogB.le _
  have hinnerNonneg : 0 ≤
      (P : ℝ) / m *
        (2 * typeIQuadraticBranchDecayConstant * (Real.log B) ^ (-T)) := by
    exact mul_nonneg (div_nonneg (by positivity) (by positivity))
      (mul_nonneg (mul_nonneg (by norm_num)
        typeIQuadraticBranchDecayConstant_pos.le) hpowNonneg)
  have hmul : Real.log B * (Real.log B) ^ (-T) =
      (Real.log B) ^ (-(T - 1)) := by
    calc
      Real.log B * (Real.log B) ^ (-T) =
          (Real.log B) ^ (1 : ℝ) * (Real.log B) ^ (-T) := by
            rw [Real.rpow_one]
      _ = (Real.log B) ^ ((1 : ℝ) + (-T)) :=
        (Real.rpow_add hlogB 1 (-T)).symm
      _ = (Real.log B) ^ (-(T - 1)) := by ring_nf
  calc
    2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        ((P : ℝ) / m *
          (2 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-T))) ≤
      2 * Real.log B *
        ((P : ℝ) / m *
          (2 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-T))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogCeil (by norm_num)) hinnerNonneg
    _ = (P : ℝ) / m *
        (4 * typeIQuadraticBranchDecayConstant *
          (Real.log B * (Real.log B) ^ (-T))) := by ring
    _ = (P : ℝ) / m *
        (4 * typeIQuadraticBranchDecayConstant *
          (Real.log B) ^ (-(T - 1))) := by rw [hmul]

/-- The complete first Vaughan Type I family, including its finite Abel
summation, satisfies the corresponding source logarithmic bound. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeILogSum_le_source
    {C₀ C₁ ε A d T : ℝ}
    (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hVinogradov : VinogradovExponentialSumEstimateAt C₁)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε)
    (hAT : T + 2 ≤ 3 * A)
    (hd : 1024 * (T + 1) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a b : ℕ) (N M : ℝ),
      0 < P → P ≤ a → a ≤ b → b ≤ 2 * P → 0 < a → b ≤ B →
      P ≤ B → B ≤ 2 * P → M ≠ 0 →
      64 ≤ reciprocalPhaseScale N M 2 P →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale N M 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖weightedConvolutionProductSum (Finset.Ico a b) B
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeICoefficient (vaughanSourceTailCutoff B)) log‖ ≤
        (Nat.log 2 B + 1 : ℕ) ^ 102 *
          ((P : ℝ) *
            (4 * typeIQuadraticBranchDecayConstant *
              (Real.log B) ^ (-(T - 1))) *
            ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ)) := by
  let K : ℕ := ⌈2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)))⌉₊
  have hadm := eventually_forall_activeLog_typeIQuadraticHybridAdmissible
    hA hC₀ hε haexp
  have hlarge := eventually_forall_activeLog_ceilDiv_ge K
  have hquarter := eventually_quarter_rpow_le_ceilDiv_of_activeLog
  have hmajor := eventually_typeIQuadraticRescaledBranchMajorantAt_le_invWeighted
    hC₀ hC₁ hε haexp hAT hd
  have hlog : ∀ᶠ B : ℕ in atTop, 1 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hApos : 0 < A := by linarith
  have hten : ∀ᶠ B : ℕ in atTop, 10 ≤ (Real.log (B : ℝ)) ^ A :=
    ((tendsto_rpow_atTop hApos).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually
        (eventually_ge_atTop 10)
  filter_upwards [hadm, hlarge, hquarter, hmajor, hlog, hten,
    eventually_gt_atTop (0 : ℕ)] with
      B hadmB hlargeB hquarterB hmajorB hlogB htenB hB
  intro P a b N M hP hPa hab hbP ha hbB hPB hBP hM hsource64 hsource hupper
  have hQ : 0 ≤
      4 * typeIQuadraticBranchDecayConstant *
        (Real.log B) ^ (-(T - 1)) := by
    have hlogNonneg : 0 ≤ Real.log (B : ℝ) := by linarith
    exact mul_nonneg (mul_nonneg (by norm_num)
      typeIQuadraticBranchDecayConstant_pos.le)
        (Real.rpow_nonneg hlogNonneg _)
  apply norm_weightedConvolutionProductVaughanTypeILogSum_le_invWeighted
    (Finset.Ico a b) B (vaughanSourceTailCutoff B) P N M 2 hQ
  intro sk hsk m hmActive
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hmActive
  have hD : K ≤ P ⌈/⌉ m := hlargeB P sk m hBP hmActive
  have htwoD : 2 ≤ P ⌈/⌉ m := by
    have hKtwo : 2 ≤ K := by norm_num [K]
    exact hKtwo.trans hD
  have hmP : m ≤ P := le_of_two_le_ceilDiv hmpos htwoD
  have hDreal : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) := by
    have hceil : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (K : ℝ) := by
      norm_num [K]
    exact hceil.trans (by exact_mod_cast hD)
  have hadmFiber := hadmB P N M sk m hP hBP hsource64 hupper hmActive
  have hbudget :
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4 →
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
              ((P ⌈/⌉ m : ℕ) : ℝ) /
            ((P ⌈/⌉ m : ℕ) : ℝ) ^ 5) +
        1 / 16 +
          4 / reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
            ((P ⌈/⌉ m : ℕ) : ℝ) ≤ 1 := by
    intro hlow
    exact typeIQuadraticWeylBudget_of_sourceScale
      N M hP hmpos hmP hDreal hsource64 hlow
  have hlocalUpper := reciprocalPhaseScale_typeI_rescale_ceilDiv_le
    N M 2 hP hmpos
  have hmajorFiber := hmajorB P m N M hP hmpos hmP hPB htwoD
    (hquarterB P sk m hBP hmActive) hsource (hlocalUpper.trans hupper)
  have hinner := norm_typeIProductRestrictedLogInnerSum_Ico_le_quadraticBranchAt
    C₁ hVinogradov B A N M hPa hab hbP ha hbB hmpos hM hC₁.le
      hlogB hA htenB hadmFiber hbudget
  have hceilPos : 0 < b ⌈/⌉ m := typeI_ceilDiv_pos (ha.trans_le hab) hmpos
  have hlogCeil : 0 ≤ Real.log ((b ⌈/⌉ m : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hceilPos)
  calc
    ‖typeIProductRestrictedWeightedInnerSum (Finset.Ico a b)
        (Finset.Ioc 0 B) (fun n => (Real.log n : ℂ)) N M 2 m‖ ≤
      2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        typeIQuadraticRescaledBranchMajorantAt C₁ B A N M P m := hinner
    _ ≤ 2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        ((P : ℝ) / m *
          (2 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-T))) := by
      exact mul_le_mul_of_nonneg_left hmajorFiber
        (mul_nonneg (by norm_num) hlogCeil)
    _ ≤ (P : ℝ) / m *
        (4 * typeIQuadraticBranchDecayConstant *
          (Real.log B) ^ (-(T - 1))) :=
      two_mul_log_ceilDiv_mul_branchDecay_le_invWeighted
        hmpos (ha.trans_le hab) hbB (by linarith)

/-! ## Final Type I logarithmic compression -/

noncomputable def typeIQuadraticFamilyDecayConstant : ℝ :=
  8 * 3 ^ (102 : ℕ) * typeIQuadraticBranchDecayConstant

theorem typeIQuadraticFamilyDecayConstant_pos :
    0 < typeIQuadraticFamilyDecayConstant := by
  unfold typeIQuadraticFamilyDecayConstant
  exact mul_pos (mul_pos (by norm_num) (by positivity))
    typeIQuadraticBranchDecayConstant_pos

/-- Scalar compression of the complete second-Type-I family ledger. -/
theorem typeIPrimeFamilyEnvelope_le_logSaving
    {B P : ℕ} {T S : ℝ}
    (hB : 0 < B) (hlog : 2 ≤ Real.log B) (hT : T = S + 104) :
    (((Nat.log 2 B + 1 : ℕ) : ℝ) ^ 102) *
        (Real.log (2 * B) *
          ((P : ℝ) *
            (2 * typeIQuadraticBranchDecayConstant *
              (Real.log B) ^ (-T)) *
            ((harmonic
              (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ))) ≤
      typeIQuadraticFamilyDecayConstant * (P : ℝ) *
        (Real.log B) ^ (-S) := by
  have hlogpos : 0 < Real.log B := by linarith
  have hcount := source_natLogTwo_add_one_cast_le_three_mul_log hB hlog
  have hcountPow : (((Nat.log 2 B + 1 : ℕ) : ℝ) ^ 102) ≤
      (3 * Real.log B) ^ (102 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hcount 102
  have hlogTwo := realLog_two_mul_nat_le_two_mul_log hB hlog
  have hharm := harmonic_vaughanSourceTailCutoff_sq_le_two_log (by linarith :
    1 ≤ Real.log B)
  have hnatPow : (Real.log B) ^ (102 : ℕ) =
      (Real.log B) ^ (102 : ℝ) :=
    (Real.rpow_natCast (Real.log B) 102).symm
  have hlogs : (Real.log B) ^ (102 : ℕ) *
      (Real.log B * Real.log B * (Real.log B) ^ (-T)) =
        (Real.log B) ^ (-S) := by
    calc
      (Real.log B) ^ (102 : ℕ) *
          (Real.log B * Real.log B * (Real.log B) ^ (-T)) =
        (Real.log B) ^ (102 : ℝ) *
          (Real.log B) ^ (1 : ℝ) * (Real.log B) ^ (1 : ℝ) *
            (Real.log B) ^ (-T) := by
              rw [hnatPow, Real.rpow_one]
              ring
      _ = (Real.log B) ^ ((102 : ℝ) + 1 + 1 + (-T)) := by
        rw [← Real.rpow_add hlogpos, ← Real.rpow_add hlogpos,
          ← Real.rpow_add hlogpos]
      _ = (Real.log B) ^ (-S) := by
        rw [hT]
        congr 1
        ring
  have hbranch0 : 0 ≤ typeIQuadraticBranchDecayConstant :=
    typeIQuadraticBranchDecayConstant_pos.le
  have hpow0 : 0 ≤ (Real.log B) ^ (-T) :=
    Real.rpow_nonneg hlogpos.le _
  have hharm0 : 0 ≤ ((harmonic
      (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  have hlogTwo0 : 0 ≤ Real.log (2 * B) := by
    apply Real.log_nonneg
    exact_mod_cast (by omega : 1 ≤ 2 * B)
  calc
    (((Nat.log 2 B + 1 : ℕ) : ℝ) ^ 102) *
        (Real.log (2 * B) *
          ((P : ℝ) *
            (2 * typeIQuadraticBranchDecayConstant *
              (Real.log B) ^ (-T)) *
            ((harmonic
              (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ))) ≤
      (3 * Real.log B) ^ (102 : ℕ) *
        ((2 * Real.log B) *
          ((P : ℝ) *
            (2 * typeIQuadraticBranchDecayConstant *
              (Real.log B) ^ (-T)) * (2 * Real.log B))) := by
      gcongr
    _ = typeIQuadraticFamilyDecayConstant * (P : ℝ) *
        (Real.log B) ^ (-S) := by
      calc
        (3 * Real.log B) ^ (102 : ℕ) *
            ((2 * Real.log B) *
              ((P : ℝ) *
                (2 * typeIQuadraticBranchDecayConstant *
                  (Real.log B) ^ (-T)) * (2 * Real.log B))) =
          typeIQuadraticFamilyDecayConstant * (P : ℝ) *
            ((Real.log B) ^ (102 : ℕ) *
              (Real.log B * Real.log B * (Real.log B) ^ (-T))) := by
                rw [mul_pow]
                unfold typeIQuadraticFamilyDecayConstant
                ring
        _ = typeIQuadraticFamilyDecayConstant * (P : ℝ) *
            (Real.log B) ^ (-S) := by rw [hlogs]

/-- Scalar compression of the Abel-weighted first-Type-I family ledger. -/
theorem typeILogFamilyEnvelope_le_logSaving
    {B P : ℕ} {T S : ℝ}
    (hB : 0 < B) (hlog : 2 ≤ Real.log B) (hT : T = S + 104) :
    (((Nat.log 2 B + 1 : ℕ) : ℝ) ^ 102) *
        ((P : ℝ) *
          (4 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-(T - 1))) *
          ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ)) ≤
      typeIQuadraticFamilyDecayConstant * (P : ℝ) *
        (Real.log B) ^ (-S) := by
  have hlogpos : 0 < Real.log B := by linarith
  have hcount := source_natLogTwo_add_one_cast_le_three_mul_log hB hlog
  have hcountPow : (((Nat.log 2 B + 1 : ℕ) : ℝ) ^ 102) ≤
      (3 * Real.log B) ^ (102 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hcount 102
  have hharm := harmonic_vaughanSourceTailCutoff_le_two_log (by linarith :
    1 ≤ Real.log B)
  have hnatPow : (Real.log B) ^ (102 : ℕ) =
      (Real.log B) ^ (102 : ℝ) :=
    (Real.rpow_natCast (Real.log B) 102).symm
  have hlogs : (Real.log B) ^ (102 : ℕ) *
      (Real.log B * (Real.log B) ^ (-(T - 1))) =
        (Real.log B) ^ (-S) := by
    calc
      (Real.log B) ^ (102 : ℕ) *
          (Real.log B * (Real.log B) ^ (-(T - 1))) =
        (Real.log B) ^ (102 : ℝ) *
          (Real.log B) ^ (1 : ℝ) *
            (Real.log B) ^ (-(T - 1)) := by
              rw [hnatPow, Real.rpow_one]
              ring
      _ = (Real.log B) ^ ((102 : ℝ) + 1 + (-(T - 1))) := by
        rw [← Real.rpow_add hlogpos, ← Real.rpow_add hlogpos]
      _ = (Real.log B) ^ (-S) := by
        rw [hT]
        congr 1
        ring
  have hbranch0 : 0 ≤ typeIQuadraticBranchDecayConstant :=
    typeIQuadraticBranchDecayConstant_pos.le
  have hpow0 : 0 ≤ (Real.log B) ^ (-(T - 1)) :=
    Real.rpow_nonneg hlogpos.le _
  have hharm0 : 0 ≤
      ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    positivity
  calc
    (((Nat.log 2 B + 1 : ℕ) : ℝ) ^ 102) *
        ((P : ℝ) *
          (4 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-(T - 1))) *
          ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ)) ≤
      (3 * Real.log B) ^ (102 : ℕ) *
        ((P : ℝ) *
          (4 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-(T - 1))) * (2 * Real.log B)) := by
      gcongr
    _ = typeIQuadraticFamilyDecayConstant * (P : ℝ) *
        (Real.log B) ^ (-S) := by
      calc
        (3 * Real.log B) ^ (102 : ℕ) *
            ((P : ℝ) *
              (4 * typeIQuadraticBranchDecayConstant *
                (Real.log B) ^ (-(T - 1))) * (2 * Real.log B)) =
          typeIQuadraticFamilyDecayConstant * (P : ℝ) *
            ((Real.log B) ^ (102 : ℕ) *
              (Real.log B * (Real.log B) ^ (-(T - 1)))) := by
                rw [mul_pow]
                unfold typeIQuadraticFamilyDecayConstant
                ring
        _ = typeIQuadraticFamilyDecayConstant * (P : ℝ) *
            (Real.log B) ^ (-S) := by rw [hlogs]

/-- Final arbitrary-logarithmic-saving estimate for the complete second
Vaughan Type I family. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_logSaving
    {C₀ C₁ ε A d S : ℝ}
    (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hVinogradov : VinogradovExponentialSumEstimateAt C₁)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε)
    (hAS : S + 106 ≤ 3 * A)
    (hd : 1024 * (S + 105) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a b : ℕ) (N M : ℝ),
      0 < P → P ≤ a → b ≤ 2 * P → 0 < a → b ≤ B →
      P ≤ B → B ≤ 2 * P → M ≠ 0 →
      64 ≤ reciprocalPhaseScale N M 2 P →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale N M 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖weightedConvolutionProductSum (Finset.Ico a b) B
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeIPrimeCoefficient
            (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B))
          (ζ : ArithmeticFunction ℝ)‖ ≤
        typeIQuadraticFamilyDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
  have hAT : (S + 104) + 2 ≤ 3 * A := by linarith
  have hd' : 1024 * ((S + 104) + 1) + 1 ≤ d := by linarith
  have hsource :=
    eventually_norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_source
      hA hC₀ hC₁ hVinogradov hε haexp hAT hd'
  have hlog : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hsource, hlog] with B hsourceB hlogB
  intro P a b N M hP hPa hbP ha hbB hPB hBP hM hsource64 hlower hupper
  have hraw := hsourceB P a b N M hP hPa hbP ha hbB hPB hBP hM
    hsource64 hlower hupper
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeIPrimeCoefficient
          (vaughanSourceTailCutoff B) (vaughanSourceTailCutoff B))
        (ζ : ArithmeticFunction ℝ)‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        (Real.log (2 * B) *
          ((P : ℝ) *
            (2 * typeIQuadraticBranchDecayConstant *
              (Real.log B) ^ (-(S + 104))) *
            ((harmonic
              (vaughanSourceTailCutoff B * vaughanSourceTailCutoff B) : ℚ) : ℝ))) := hraw
    _ ≤ typeIQuadraticFamilyDecayConstant * (P : ℝ) *
        (Real.log B) ^ (-S) := by
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
        (typeIPrimeFamilyEnvelope_le_logSaving
          (hP.trans_le hPB) hlogB (T := S + 104) (S := S) rfl)

/-- Final arbitrary-logarithmic-saving estimate for the complete first
Vaughan Type I family, including finite Abel summation. -/
theorem eventually_norm_weightedConvolutionProductVaughanTypeILogSum_le_logSaving
    {C₀ C₁ ε A d S : ℝ}
    (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hVinogradov : VinogradovExponentialSumEstimateAt C₁)
    (hε : 0 < ε) (haexp : 0 ≤ 3 / 2 - ε)
    (hAS : S + 106 ≤ 3 * A)
    (hd : 1024 * (S + 105) + 1 ≤ d) :
    ∀ᶠ B : ℕ in atTop, ∀ (P a b : ℕ) (N M : ℝ),
      0 < P → P ≤ a → a ≤ b → b ≤ 2 * P → 0 < a → b ≤ B →
      P ≤ B → B ≤ 2 * P → M ≠ 0 →
      64 ≤ reciprocalPhaseScale N M 2 P →
      (Real.log B) ^ d ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale N M 2 P ≤
        C₀ * Real.exp ((Real.log B) ^ (3 / 2 - ε)) →
      ‖weightedConvolutionProductSum (Finset.Ico a b) B
          (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
          (vaughanTypeICoefficient (vaughanSourceTailCutoff B)) log‖ ≤
        typeIQuadraticFamilyDecayConstant * (P : ℝ) *
          (Real.log B) ^ (-S) := by
  have hAT : (S + 104) + 2 ≤ 3 * A := by linarith
  have hd' : 1024 * ((S + 104) + 1) + 1 ≤ d := by linarith
  have hsource :=
    eventually_norm_weightedConvolutionProductVaughanTypeILogSum_le_source
      hA hC₀ hC₁ hVinogradov hε haexp hAT hd'
  have hlog : ∀ᶠ B : ℕ in atTop, 2 ≤ Real.log (B : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 2)
  filter_upwards [hsource, hlog] with B hsourceB hlogB
  intro P a b N M hP hPa hab hbP ha hbB hPB hBP hM hsource64 hlower hupper
  have hraw := hsourceB P a b N M hP hPa hab hbP ha hbB hPB hBP hM
    hsource64 hlower hupper
  calc
    ‖weightedConvolutionProductSum (Finset.Ico a b) B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeICoefficient (vaughanSourceTailCutoff B)) log‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        ((P : ℝ) *
          (4 * typeIQuadraticBranchDecayConstant *
            (Real.log B) ^ (-((S + 104) - 1))) *
          ((harmonic (vaughanSourceTailCutoff B) : ℚ) : ℝ)) := hraw
    _ ≤ typeIQuadraticFamilyDecayConstant * (P : ℝ) *
        (Real.log B) ^ (-S) := by
      simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
        (typeILogFamilyEnvelope_le_logSaving
          (hP.trans_le hPB) hlogB (T := S + 104) (S := S) rfl)

end

end Tao2026
