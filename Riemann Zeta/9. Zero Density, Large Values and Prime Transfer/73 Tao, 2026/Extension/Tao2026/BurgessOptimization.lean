import Tao2026.BurgessAmplification
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Scalar preparation for Burgess parameter optimization

This file begins the post-amplification scalar layer. Its first task is a
quantitative lower bound for the number of positive multipliers up to `A`
that are coprime to the conductor. Exact Möbius inversion gives the expected
totient-density main term with an explicit divisor-count discrepancy.
-/

namespace Tao2026

open Finset
open Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

/-- The sum of the Möbius function over all divisors is the indicator of one. -/
theorem sum_moebius_divisors_int_eq_indicator (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) =
      if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simpa only [ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.one_apply] using h

/-- Divisors of a gcd are precisely the divisors of the first argument that
also divide the second. -/
theorem divisors_gcd_eq_filter_dvd (q a : ℕ) (hq : q ≠ 0) :
    (Nat.gcd q a).divisors = q.divisors.filter (fun d => d ∣ a) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hd, hg⟩
    exact ⟨⟨dvd_trans hd (Nat.gcd_dvd_left q a), hq⟩,
      dvd_trans hd (Nat.gcd_dvd_right q a)⟩
  · rintro ⟨⟨hdq, _⟩, hda⟩
    exact ⟨Nat.dvd_gcd hdq hda, Nat.gcd_ne_zero_left hq⟩

/-- Möbius inversion expresses the coprimality indicator through divisors of
the gcd. -/
theorem sum_moebius_gcd_eq_coprimeIndicator (q a : ℕ) :
    (∑ d ∈ (Nat.gcd q a).divisors, ArithmeticFunction.moebius d) =
      if Nat.Coprime a q then 1 else 0 := by
  rw [sum_moebius_divisors_int_eq_indicator]
  simp only [Nat.Coprime, Nat.gcd_comm]

/-- Exact integer Möbius formula for the positive coprime multiplier count. -/
theorem card_coprimeMultipliers_eq_sum_moebius_div
    (q A : ℕ) (hq : q ≠ 0) :
    (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℤ) =
      ∑ d ∈ q.divisors,
        ArithmeticFunction.moebius d * ((A / d : ℕ) : ℤ) := by
  calc
    (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℤ) =
        ∑ a ∈ Finset.Ioc 0 A, if Nat.Coprime a q then 1 else 0 := by
      rw [← Finset.sum_filter]
      simp
    _ = ∑ a ∈ Finset.Ioc 0 A,
          ∑ d ∈ (Nat.gcd q a).divisors,
            ArithmeticFunction.moebius d := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (sum_moebius_gcd_eq_coprimeIndicator q a).symm
    _ = ∑ a ∈ Finset.Ioc 0 A,
          ∑ d ∈ q.divisors,
            if d ∣ a then ArithmeticFunction.moebius d else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [divisors_gcd_eq_filter_dvd q a hq, Finset.sum_filter]
    _ = ∑ d ∈ q.divisors,
          ∑ a ∈ Finset.Ioc 0 A,
            if d ∣ a then ArithmeticFunction.moebius d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ q.divisors,
        ArithmeticFunction.moebius d * ((A / d : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [Nat.Ioc_filter_dvd_card_eq_div]
      push_cast
      ring

/-- A complete positive period contains exactly `φ(q)` coprime integers. -/
theorem card_coprimeMultipliers_full_period (q : ℕ) :
    ((Finset.Ioc 0 q).filter (fun a => Nat.Coprime a q)).card = q.totient := by
  rw [show Finset.Ioc 0 q = Finset.Ico 1 (1 + q) by ext x; simp; omega]
  simpa [Nat.coprime_comm] using Nat.filter_coprime_Ico_eq_totient q 1

/-- Dividing the complete-period Möbius formula by `q` gives the exact
totient density. -/
theorem sum_moebius_div_eq_totient_div (q : ℕ) (hq : q ≠ 0) :
    (∑ d ∈ q.divisors,
      (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) =
        (q.totient : ℝ) / (q : ℝ) := by
  have hcount := card_coprimeMultipliers_eq_sum_moebius_div q q hq
  rw [card_coprimeMultipliers_full_period] at hcount
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hcount
  simp only [Int.cast_natCast, Int.cast_mul, Int.cast_sum] at hcast
  rw [hcast]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d hd
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hd0 : d ≠ 0 := by
    intro hd0
    subst d
    simp at hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  field_simp
  rw [mul_assoc, ← Nat.cast_mul, Nat.mul_comm d (q / d),
    Nat.div_mul_cancel (Nat.mem_divisors.mp hd).1]

/-- Replacing `A/d` by natural division costs at most one after multiplication
by a Möbius coefficient. -/
theorem moebius_mul_div_le_floor_add_one (A d : ℕ) (hd : 0 < d) :
    (ArithmeticFunction.moebius d : ℝ) * ((A : ℝ) / (d : ℝ)) ≤
      (ArithmeticFunction.moebius d : ℝ) * ((A / d : ℕ) : ℝ) + 1 := by
  have hlower : ((A / d : ℕ) : ℝ) ≤ (A : ℝ) / (d : ℝ) :=
    Nat.cast_div_le
  have hupper : (A : ℝ) / (d : ℝ) < ((A / d : ℕ) : ℝ) + 1 := by
    apply (div_lt_iff₀ (by exact_mod_cast hd)).2
    have hnat := Nat.lt_mul_div_succ A hd
    exact_mod_cast (show A < (A / d + 1) * d by
      simpa [Nat.mul_comm] using hnat)
  rcases ArithmeticFunction.moebius_eq_or d with hzero | hone | hneg
  · simp [hzero]
  · simp only [hone, Int.cast_one, one_mul]
    exact hupper.le
  · simp only [hneg, Int.cast_neg, Int.cast_one, neg_mul]
    linarith

/-- Source-facing short-interval coprime count with an explicit, deliberately
coarse divisor-count discrepancy. -/
theorem card_coprimeMultipliers_cast_lower (q A : ℕ) (hq : q ≠ 0) :
    (A : ℝ) * (q.totient : ℝ) / (q : ℝ) - (q.divisors.card : ℝ) ≤
      (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℝ) := by
  have hcount := card_coprimeMultipliers_eq_sum_moebius_div q A hq
  have hcountR := congrArg (fun z : ℤ => (z : ℝ)) hcount
  simp only [Int.cast_natCast, Int.cast_mul, Int.cast_sum] at hcountR
  have hterm : ∀ d ∈ q.divisors,
      (ArithmeticFunction.moebius d : ℝ) * ((A : ℝ) / (d : ℝ)) ≤
        (ArithmeticFunction.moebius d : ℝ) * ((A / d : ℕ) : ℝ) + 1 := by
    intro d hd
    apply moebius_mul_div_le_floor_add_one
    exact Nat.pos_of_ne_zero (by
      intro hd0
      subst d
      simp at hd)
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  rw [← hcountR] at hsum
  have hdensity :
      (A : ℝ) * (q.totient : ℝ) / (q : ℝ) =
        ∑ d ∈ q.divisors,
          (ArithmeticFunction.moebius d : ℝ) * ((A : ℝ) / (d : ℝ)) := by
    calc
      (A : ℝ) * (q.totient : ℝ) / (q : ℝ) =
          (A : ℝ) * ((q.totient : ℝ) / (q : ℝ)) := by ring
      _ = (A : ℝ) * (∑ d ∈ q.divisors,
          (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)) := by
        rw [sum_moebius_div_eq_totient_div q hq]
      _ = ∑ d ∈ q.divisors,
          (ArithmeticFunction.moebius d : ℝ) * ((A : ℝ) / (d : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d hd
        ring
  rw [hdensity]
  linarith

/-- The same lower bound in the multiplier-pair notation used by the
amplification recurrence. -/
theorem card_burgessCoprimeMultiplierPairs_one_cast_lower
    (q A : ℕ) (hq : q ≠ 0) :
    (A : ℝ) * (q.totient : ℝ) / (q : ℝ) - (q.divisors.card : ℝ) ≤
      ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) := by
  simpa [burgessCoprimeMultiplierPairs] using
    card_coprimeMultipliers_cast_lower q A hq

/-- Once the divisor discrepancy is at most half the expected main term, the
coprime multiplier count retains at least half of its totient density. -/
theorem half_totientDensity_le_card_coprimeMultipliers
    (q A : ℕ) (hq : q ≠ 0)
    (hlarge : 2 * (q.divisors.card : ℝ) ≤
      (A : ℝ) * (q.totient : ℝ) / (q : ℝ)) :
    ((A : ℝ) * (q.totient : ℝ) / (q : ℝ)) / 2 ≤
      (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℝ) := by
  have h := card_coprimeMultipliers_cast_lower q A hq
  linarith

/-- The elementary identity `sum_{d|q} φ(d)=q` also gives the convenient
lower bound `φ(q) ≥ q/τ(q)`. -/
theorem self_le_card_divisors_mul_totient (q : ℕ) (hq : 0 < q) :
    q ≤ q.divisors.card * q.totient := by
  calc
    q = ∑ d ∈ q.divisors, d.totient := (Nat.sum_totient q).symm
    _ ≤ ∑ _d ∈ q.divisors, q.totient := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.le_of_dvd (Nat.totient_pos.mpr hq)
        (Nat.totient_dvd_of_dvd (Nat.mem_divisors.mp hd).1)
    _ = q.divisors.card * q.totient := by simp

/-- Real quotient form of the preceding elementary totient lower bound. -/
theorem conductor_div_totient_le_card_divisors (q : ℕ) (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤ (q.divisors.card : ℝ) := by
  apply (div_le_iff₀ (by exact_mod_cast (Nat.totient_pos.mpr hq))).2
  exact_mod_cast (show q ≤ q.divisors.card * q.totient from
    self_le_card_divisors_mul_totient q hq)

/-- A single natural inequality `2*τ(q)^2 ≤ A` dominates the discrepancy in
the short coprime count. -/
theorem two_mul_card_divisors_le_totientDensity_of_sq_le
    (q A : ℕ) (hq : 0 < q)
    (hA : 2 * q.divisors.card ^ 2 ≤ A) :
    2 * (q.divisors.card : ℝ) ≤
      (A : ℝ) * (q.totient : ℝ) / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  apply (le_div_iff₀ hqR).2
  have hqt := self_le_card_divisors_mul_totient q hq
  have hAreal : (2 : ℝ) * (q.divisors.card : ℝ) ^ 2 ≤ A := by
    exact_mod_cast hA
  have hphi0 : (0 : ℝ) ≤ q.totient := by positivity
  calc
    2 * (q.divisors.card : ℝ) * (q : ℝ) ≤
        2 * (q.divisors.card : ℝ) *
          ((q.divisors.card : ℝ) * (q.totient : ℝ)) := by
      gcongr
      exact_mod_cast hqt
    _ = (2 * (q.divisors.card : ℝ) ^ 2) * (q.totient : ℝ) := by ring
    _ ≤ (A : ℝ) * (q.totient : ℝ) :=
      mul_le_mul_of_nonneg_right hAreal hphi0

/-- Half of the expected coprime density follows from
`2*τ(q)^2 ≤ A`. -/
theorem half_totientDensity_le_card_coprimeMultipliers_of_sq_le
    (q A : ℕ) (hq : 0 < q)
    (hA : 2 * q.divisors.card ^ 2 ≤ A) :
    ((A : ℝ) * (q.totient : ℝ) / (q : ℝ)) / 2 ≤
      (((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card : ℝ) := by
  exact half_totientDensity_le_card_coprimeMultipliers q A hq.ne'
    (two_mul_card_divisors_le_totientDensity_of_sq_le q A hq hA)

/-- Source-facing affine-pair form of the half-density denominator bound. -/
theorem half_totientDensity_le_card_burgessCoprimeMultiplierPairs_one_of_sq_le
    (q A : ℕ) (hq : 0 < q)
    (hA : 2 * q.divisors.card ^ 2 ≤ A) :
    ((A : ℝ) * (q.totient : ℝ) / (q : ℝ)) / 2 ≤
      ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) := by
  simpa [burgessCoprimeMultiplierPairs] using
    half_totientDensity_le_card_coprimeMultipliers_of_sq_le q A hq hA

/-- The square of the divisor-count discrepancy is eventually dominated by
every fixed positive power of the conductor.  This is the asymptotic input
needed to make the elementary coprime-multiplier criterion automatic. -/
theorem eventually_two_mul_card_divisors_sq_cast_le_rpow
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop,
      (2 : ℝ) * (q.divisors.card : ℝ) ^ 2 ≤ (q : ℝ) ^ η := by
  let δ : ℝ := η / 4
  let a : ℝ := η / 2
  let D : ℝ := RiemannZeta.GuthMaynard.divisorEpsilonConstant δ
  let K : ℝ := 2 * D ^ 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have haη : a < η := by dsimp [a]; linarith
  have hD : 0 < D := by
    dsimp [D]
    exact RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos δ
  have hK : 0 < K := by dsimp [K]; positivity
  have hsmall :=
    (GafniTao.rpow_isLittleO_rpow haη).bound (inv_pos.mpr hK)
  have hnatTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  filter_upwards [hnatTop.eventually hsmall,
    eventually_ge_atTop (1 : ℕ)] with q hpow hq
  have hqPos : 0 < q := by omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqPos
  have hqa : 0 ≤ (q : ℝ) ^ a := Real.rpow_nonneg hqR.le _
  have hqη : 0 ≤ (q : ℝ) ^ η := Real.rpow_nonneg hqR.le _
  have hpow' : (q : ℝ) ^ a ≤ K⁻¹ * (q : ℝ) ^ η := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hqa, abs_of_nonneg hqη] using hpow
  have hdiv : (q.divisors.card : ℝ) ≤ D * (q : ℝ) ^ δ := by
    simpa only [D] using
      (RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow hδ hqPos.ne')
  have hdiv0 : (0 : ℝ) ≤ q.divisors.card := by positivity
  have hDpow0 : 0 ≤ D * (q : ℝ) ^ δ := by positivity
  calc
    (2 : ℝ) * (q.divisors.card : ℝ) ^ 2 ≤
        2 * (D * (q : ℝ) ^ δ) ^ 2 := by gcongr
    _ = K * (q : ℝ) ^ a := by
      dsimp [K, a, δ]
      rw [mul_pow]
      rw [show ((q : ℝ) ^ (η / 4)) ^ (2 : ℕ) =
          (q : ℝ) ^ (η / 2) by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hqR.le]
        congr 1
        ring]
      ring
    _ ≤ K * (K⁻¹ * (q : ℝ) ^ η) :=
      mul_le_mul_of_nonneg_left hpow' hK.le
    _ = (q : ℝ) ^ η := by field_simp [hK.ne']

/-- Natural-floor form of the eventual divisor-square absorption. -/
theorem eventually_two_mul_card_divisors_sq_le_floor_rpow
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop,
      2 * q.divisors.card ^ 2 ≤ ⌊(q : ℝ) ^ η⌋₊ := by
  filter_upwards [eventually_two_mul_card_divisors_sq_cast_le_rpow hη] with q hq
  exact Nat.le_floor (by exact_mod_cast hq)

/-- Any multiplier length above a floor-rounded positive power of the
conductor eventually satisfies the half-totient-density lower bound. -/
theorem eventually_half_totientDensity_le_card_burgessCoprimeMultiplierPairs_one
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ A : ℕ,
      ⌊(q : ℝ) ^ η⌋₊ ≤ A →
        ((A : ℝ) * (q.totient : ℝ) / (q : ℝ)) / 2 ≤
          ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) := by
  filter_upwards [eventually_two_mul_card_divisors_sq_le_floor_rpow hη,
    eventually_ge_atTop (1 : ℕ)] with q hdiv hq A hA
  exact half_totientDensity_le_card_burgessCoprimeMultiplierPairs_one_of_sq_le
    q A (by omega) (hdiv.trans hA)

/-- There are at most `A` positive coprime multipliers up to `A`. -/
theorem card_coprimeMultipliers_le (q A : ℕ) :
    ((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card ≤ A := by
  calc
    ((Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q)).card ≤
        (Finset.Ioc 0 A).card := Finset.card_filter_le _ _
    _ = A := by simp

/-- The multiplier-pair first moment is bounded by the enclosing rectangle. -/
theorem card_burgessCoprimeMultiplierPairs_cast_le_mul
    (q A H : ℕ) :
    ((burgessCoprimeMultiplierPairs q A H).card : ℝ) ≤
      (A : ℝ) * (H : ℝ) := by
  rw [card_burgessCoprimeMultiplierPairs]
  push_cast
  gcongr
  exact_mod_cast card_coprimeMultipliers_le q A

/-- The rooted `r = 7` Hölder estimate with both multiplier-cardinality
factors replaced by their scalar rectangle bounds. -/
theorem burgessResidueMultiplicity_holder_fourteenth_le_of_moment_scalar
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hAHq : 2 * A * H ≤ q) {V : ℝ}
    (hV : (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤ V) :
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) ≤
      ((((A : ℝ) * (H : ℝ)) ^ 12 *
        ((A : ℝ) ^ 2 +
          2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) * V) ^
            (14 : ℝ)⁻¹) := by
  have hmain := burgessResidueMultiplicity_holder_fourteenth_le_of_moment
    (N := N) χ hAHq hV
  have hpairAH := card_burgessCoprimeMultiplierPairs_cast_le_mul q A H
  have hpairAOne :
      ((burgessCoprimeMultiplierPairs q A 1).card : ℝ) ≤ (A : ℝ) := by
    simpa using card_burgessCoprimeMultiplierPairs_cast_le_mul q A 1
  have hV0 : 0 ≤ V := by
    exact (Finset.sum_nonneg fun _ _ => by positivity).trans hV
  have hharm0 : (0 : ℝ) ≤ ((harmonic A : ℚ) : ℝ) := by
    cases A with
    | zero => simp
    | succ K => exact_mod_cast (harmonic_pos (Nat.succ_ne_zero K)).le
  apply hmain.trans
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  gcongr

/-- Fully scalar normalized `r = 7` recurrence.  The divisor-square
criterion supplies the denominator, while the rectangle bounds remove both
remaining multiplier-set cardinalities from the Hölder numerator. -/
theorem norm_burgessIntervalCharacterSum_le_fourteenthScalar_add_rpowBoundary
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hAB : A * B ≤ H)
    (hAHq : 2 * A * H ≤ q)
    (hdiv : 2 * q.divisors.card ^ 2 ≤ A)
    {C Q α V : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hα : 0 ≤ α)
    (hleft : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q)
    (hright : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q)
    (hV : (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤ V) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤
      ((((A : ℝ) * (H : ℝ)) ^ 12 *
        ((A : ℝ) ^ 2 +
          2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) * V) ^
          (14 : ℝ)⁻¹) /
        (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) +
      2 * C * (A * B : ℝ) ^ α * Q := by
  let S : ℝ :=
    (((A : ℝ) * (H : ℝ)) ^ 12 *
      ((A : ℝ) ^ 2 +
        2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) * V) ^
          (14 : ℝ)⁻¹
  have hholder :
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
          ‖burgessShiftSum B χ x‖) ≤ S := by
    simpa only [S] using
      burgessResidueMultiplicity_holder_fourteenth_le_of_moment_scalar
        (N := N) χ hAHq hV
  have hrec :=
    norm_burgessIntervalCharacterSum_le_of_holderBound_add_rpowBoundary
      χ hA hB hAB hC hQ hα hleft hright hholder
  have hqPos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hP :=
    half_totientDensity_le_card_coprimeMultipliers_of_sq_le q A hqPos hdiv
  have hden :
      ((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ) ≤
        (((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) * (B : ℝ) :=
    mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg B)
  have hdenPos :
      (0 : ℝ) < ((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ) := by
    have htotient : 0 < q.totient := Nat.totient_pos.mpr hqPos
    positivity
  have hS0 : 0 ≤ S := by
    exact (Finset.sum_nonneg fun _ _ => by positivity).trans hholder
  calc
    ‖burgessIntervalCharacterSum χ N H‖ ≤
        S / ((((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) * (B : ℝ)) +
          2 * C * (A * B : ℝ) ^ α * Q := by
      simpa only [S] using hrec
    _ ≤ S /
          (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) +
          2 * C * (A * B : ℝ) ^ α * Q := by
      exact add_le_add
        (div_le_div_of_nonneg_left hS0 hdenPos hden) le_rfl

/-- Complete-Weil specialization of the fully scalar normalized recurrence.
This is the post-amplification statement to which the rounded Burgess
parameter choices are applied. -/
theorem exists_norm_burgessIntervalCharacterSum_le_fourteenthScalar_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₁ : ℝ, 0 < C₁ ∧
      ∀ {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        TaoCubefree q → DirichletCharacter.IsPrimitive χ →
        1 ≤ A → 1 ≤ B → A * B ≤ H → 2 * A * H ≤ q →
        2 * q.divisors.card ^ 2 ≤ A →
        ∀ {C₂ Q α : ℝ}, 0 ≤ C₂ → 0 ≤ Q → 0 ≤ α →
        (∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∀ b ∈ Finset.Ioc 0 B,
            ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
              C₂ * (a * b : ℝ) ^ α * Q) →
        (∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∀ b ∈ Finset.Ioc 0 B,
            ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
              C₂ * (a * b : ℝ) ^ α * Q) →
        ‖burgessIntervalCharacterSum χ N H‖ ≤
          ((((A : ℝ) * (H : ℝ)) ^ 12 *
            ((A : ℝ) ^ 2 +
              2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
            (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
              C₁ * (B : ℝ) ^ 14 *
                (q : ℝ) ^ ((1 / 2 : ℝ) + ε))) ^ (14 : ℝ)⁻¹) /
              (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) +
            2 * C₂ * (A * B : ℝ) ^ α * Q := by
  obtain ⟨C₁, hC₁, hmoment⟩ :=
    exists_burgess_shift_fourteenth_moment_le_of_completeWeil_rpow hweil hε
  refine ⟨C₁, hC₁, ?_⟩
  intro q N H A B _ χ hq hχ hA hB hAB hAHq hdiv C₂ Q α hC₂ hQ hα hleft hright
  exact norm_burgessIntervalCharacterSum_le_fourteenthScalar_add_rpowBoundary
    χ hA hB hAB hAHq hdiv hC₂ hQ hα hleft hright (hmoment χ hq hχ)

/-- A nonempty harmonic sum contains its first term. -/
theorem one_le_harmonic_cast_of_one_le {A : ℕ} (hA : 1 ≤ A) :
    (1 : ℝ) ≤ ((harmonic A : ℚ) : ℝ) := by
  have hq : (1 : ℚ) ≤ harmonic A := by
    rw [harmonic_eq_sum_Icc]
    calc
      (1 : ℚ) = ((1 : ℕ) : ℚ)⁻¹ := by norm_num
      _ ≤ ∑ i ∈ Finset.Icc 1 A, ((i : ℚ)⁻¹) := by
        apply Finset.single_le_sum
          (s := Finset.Icc 1 A) (f := fun i : ℕ => ((i : ℚ)⁻¹))
        · intro i hi
          positivity
        · simp [hA]
  exact_mod_cast hq

/-- In the Burgess range `A ≤ H`, the diagonal and harmonic collision terms
are together at most three copies of the harmonic term. -/
theorem burgessScalarCollisionFactor_le
    {A H : ℕ} (hA : 1 ≤ A) (hAH : A ≤ H) :
    (A : ℝ) ^ 2 +
        2 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ)) ≤
      3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ)) := by
  have hA0 : (0 : ℝ) ≤ A := by positivity
  have hHA0 : (0 : ℝ) ≤ (H : ℝ) * (A : ℝ) := by positivity
  have hharm := one_le_harmonic_cast_of_one_le hA
  have hsq : (A : ℝ) ^ 2 ≤ (H : ℝ) * (A : ℝ) := by
    have hAHreal : (A : ℝ) ≤ H := by exact_mod_cast hAH
    nlinarith
  have hprod :
      (H : ℝ) * (A : ℝ) ≤
        (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ)) := by
    calc
      (H : ℝ) * (A : ℝ) = (H : ℝ) * (A : ℝ) * 1 := by ring
      _ ≤ (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hharm hHA0
  nlinarith

/-- Rooted scalar Hölder bound with the collision factor compressed to
`3*H*A*harmonic A`. -/
theorem burgessResidueMultiplicity_holder_fourteenth_le_of_moment_scalar_compressed
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hA : 1 ≤ A) (hAH : A ≤ H) (hAHq : 2 * A * H ≤ q) {V : ℝ}
    (hV : (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤ V) :
    (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) ≤
      ((((A : ℝ) * (H : ℝ)) ^ 12 *
        (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) * V) ^
          (14 : ℝ)⁻¹) := by
  have hmain :=
    burgessResidueMultiplicity_holder_fourteenth_le_of_moment_scalar
      (N := N) χ hAHq hV
  have hV0 : 0 ≤ V :=
    (Finset.sum_nonneg fun _ _ => by positivity).trans hV
  have hharm0 : (0 : ℝ) ≤ ((harmonic A : ℚ) : ℝ) :=
    zero_le_one.trans (one_le_harmonic_cast_of_one_le hA)
  apply hmain.trans
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  gcongr
  exact burgessScalarCollisionFactor_le hA hAH

/-- Fully scalar recurrence with the collision bracket compressed.  This is
the form whose `A ≍ H/B` substitution produces the Burgess exponent
`H^(6/7)`. -/
theorem norm_burgessIntervalCharacterSum_le_fourteenthScalarCompressed_add_rpowBoundary
    {q N H A B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hAB : A * B ≤ H) (hAH : A ≤ H)
    (hAHq : 2 * A * H ≤ q)
    (hdiv : 2 * q.divisors.card ^ 2 ≤ A)
    {C Q α V : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q) (hα : 0 ≤ α)
    (hleft : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q)
    (hright : ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
      ∀ b ∈ Finset.Ioc 0 B,
        ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
          C * (a * b : ℝ) ^ α * Q)
    (hV : (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤ V) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤
      ((((A : ℝ) * (H : ℝ)) ^ 12 *
        (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) * V) ^
          (14 : ℝ)⁻¹) /
        (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) +
      2 * C * (A * B : ℝ) ^ α * Q := by
  let S : ℝ :=
    (((A : ℝ) * (H : ℝ)) ^ 12 *
      (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) * V) ^
        (14 : ℝ)⁻¹
  have hholder :
      (∑ x : ZMod q, (burgessResidueMultiplicity q N H A x : ℝ) *
        ‖burgessShiftSum B χ x‖) ≤ S := by
    simpa only [S] using
      burgessResidueMultiplicity_holder_fourteenth_le_of_moment_scalar_compressed
        (N := N) χ hA hAH hAHq hV
  have hrec :=
    norm_burgessIntervalCharacterSum_le_of_holderBound_add_rpowBoundary
      χ hA hB hAB hC hQ hα hleft hright hholder
  have hqPos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hP :=
    half_totientDensity_le_card_coprimeMultipliers_of_sq_le q A hqPos hdiv
  have hden :
      ((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ) ≤
        (((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) * (B : ℝ) :=
    mul_le_mul_of_nonneg_right hP (Nat.cast_nonneg B)
  have hdenPos :
      (0 : ℝ) < ((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ) := by
    have htotient : 0 < q.totient := Nat.totient_pos.mpr hqPos
    positivity
  have hS0 : 0 ≤ S :=
    (Finset.sum_nonneg fun _ _ => by positivity).trans hholder
  calc
    ‖burgessIntervalCharacterSum χ N H‖ ≤
        S / ((((Finset.Ioc 0 A).filter
          (fun a => Nat.Coprime a q)).card : ℝ) * (B : ℝ)) +
          2 * C * (A * B : ℝ) ^ α * Q := by
      simpa only [S] using hrec
    _ ≤ S /
          (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) +
          2 * C * (A * B : ℝ) ^ α * Q := by
      exact add_le_add
        (div_le_div_of_nonneg_left hS0 hdenPos hden) le_rfl

/-- Floor-rounded Burgess shift length for the fourteenth-moment (`r = 7`)
argument. -/
noncomputable def burgessFourteenthShiftLength (q : ℕ) : ℕ :=
  ⌊(q : ℝ) ^ (1 / 14 : ℝ)⌋₊

/-- The rounded shift length never exceeds its defining real power. -/
theorem burgessFourteenthShiftLength_cast_le (q : ℕ) :
    (burgessFourteenthShiftLength q : ℝ) ≤ (q : ℝ) ^ (1 / 14 : ℝ) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- Eventually the rounded shift length retains at least half of its defining
real scale and is nonzero. -/
theorem eventually_burgessFourteenthShiftLength_bounds :
    ∀ᶠ q : ℕ in atTop,
      1 ≤ burgessFourteenthShiftLength q ∧
        (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤
          (burgessFourteenthShiftLength q : ℝ) := by
  have hpow : Tendsto (fun q : ℕ => (q : ℝ) ^ (1 / 14 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 14)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually (eventually_ge_atTop (2 : ℝ))] with q hq
  have hnonneg : (0 : ℝ) ≤ (q : ℝ) ^ (1 / 14 : ℝ) := by positivity
  have hfloor :
      (q : ℝ) ^ (1 / 14 : ℝ) <
        (burgessFourteenthShiftLength q : ℝ) + 1 := by
    simpa only [burgessFourteenthShiftLength, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((q : ℝ) ^ (1 / 14 : ℝ))
  constructor
  · apply Nat.le_floor
    norm_num
    linarith
  · linarith

/-- The same rounded shift length eventually dominates the divisor-square
threshold used in the coprime multiplier count. -/
theorem eventually_two_mul_card_divisors_sq_le_burgessFourteenthShiftLength :
    ∀ᶠ q : ℕ in atTop,
      2 * q.divisors.card ^ 2 ≤ burgessFourteenthShiftLength q := by
  simpa only [burgessFourteenthShiftLength] using
    (eventually_two_mul_card_divisors_sq_le_floor_rpow
      (by norm_num : (0 : ℝ) < 1 / 14))

/-- Integer multiplier length associated to a positive safety factor `K` and
the floor-rounded fourteenth-moment shift length. -/
noncomputable def burgessFourteenthMultiplierLength
    (K H q : ℕ) : ℕ :=
  H / (K * burgessFourteenthShiftLength q)

/-- All scalar hypotheses needed to run one rounded `r=7` induction step. -/
def BurgessFourteenthRoundedInductionData (K H q : ℕ) : Prop :=
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  1 ≤ q ∧ 1 ≤ B ∧
    (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤ (B : ℝ) ∧
    2 * (K * B) ≤ H ∧ A ≤ q ∧ 1 ≤ A ∧ A * B ≤ H ∧ A ≤ H ∧
    2 * A * H ≤ q ∧ 2 * q.divisors.card ^ 2 ≤ A

/-- Any fixed constant is eventually absorbed by a strictly positive gap
between two conductor powers. -/
theorem eventually_const_mul_nat_rpow_le_nat_rpow
    {C a b : ℝ} (hab : a < b) :
    ∀ᶠ q : ℕ in atTop, C * (q : ℝ) ^ a ≤ (q : ℝ) ^ b := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have htend : Tendsto (fun q : ℕ => (q : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hgap).comp tendsto_natCast_atTop_atTop
  filter_upwards [htend.eventually (eventually_ge_atTop C),
    eventually_ge_atTop (1 : ℕ)] with q hC hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  calc
    C * (q : ℝ) ^ a ≤ (q : ℝ) ^ (b - a) * (q : ℝ) ^ a := by
      exact mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hqR.le _)
    _ = (q : ℝ) ^ b := by
      rw [mul_comm, ← Real.rpow_add hqR]
      congr 1
      ring

/-- Exact natural-number geometry of the rounded Burgess parameters.  The
quadratic range hypothesis is precisely what implies `2*A*H ≤ q`. -/
theorem burgessFourteenthParameter_geometry
    {K H q : ℕ} (hK : 1 ≤ K) (hB : 1 ≤ burgessFourteenthShiftLength q)
    (hquad : 2 * H * H ≤
      q * K * burgessFourteenthShiftLength q) :
    let A := burgessFourteenthMultiplierLength K H q
    let B := burgessFourteenthShiftLength q
    A * B ≤ H ∧ A ≤ H ∧ 2 * A * H ≤ q := by
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  have hKB : 0 < K * B := Nat.mul_pos (by omega) (by simpa only [B] using hB)
  have hfull : A * (K * B) ≤ H := by
    simpa only [A, B, burgessFourteenthMultiplierLength] using
      Nat.div_mul_le_self H (K * burgessFourteenthShiftLength q)
  have hBKB : B ≤ K * B := by
    calc
      B = 1 * B := by simp
      _ ≤ K * B := Nat.mul_le_mul_right B hK
  have hAB : A * B ≤ H :=
    (Nat.mul_le_mul_left A hBKB).trans hfull
  have hAH : A ≤ H := by
    have hAleAB : A ≤ A * B := by
      calc
        A = A * 1 := by simp
        _ ≤ A * B := Nat.mul_le_mul_left A (by simpa only [B] using hB)
    exact hAleAB.trans hAB
  have hmul : (2 * A * H) * (K * B) ≤ q * (K * B) := by
    calc
      (2 * A * H) * (K * B) = (2 * H) * (A * (K * B)) := by ring
      _ ≤ (2 * H) * H := Nat.mul_le_mul_left (2 * H) hfull
      _ = 2 * H * H := by ring
      _ ≤ q * K * burgessFourteenthShiftLength q := hquad
      _ = q * (K * B) := by simp only [B]; ring
  exact ⟨hAB, hAH,
    Nat.le_of_mul_le_mul_right (c := K * B) hmul hKB⟩

/-- The full rounded multiplier block, including the safety factor, fits
inside the original interval. -/
theorem burgessFourteenthFullMultiplierBlock_le
    (K H q : ℕ) :
    K * burgessFourteenthMultiplierLength K H q *
        burgessFourteenthShiftLength q ≤ H := by
  simpa only [burgessFourteenthMultiplierLength, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm] using
    Nat.div_mul_le_self H (K * burgessFourteenthShiftLength q)

/-- With a nontrivial safety factor and a positive ambient length, every
rounded multiplier product is strictly shorter than the ambient interval. -/
theorem burgessFourteenthMultiplierProduct_lt
    {K H q a b : ℕ} (hK : 2 ≤ K) (hH : 1 ≤ H)
    (ha : a ≤ burgessFourteenthMultiplierLength K H q)
    (hb : b ≤ burgessFourteenthShiftLength q) : a * b < H := by
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  have hab : a * b ≤ A * B := Nat.mul_le_mul ha hb
  have hfull : K * (A * B) ≤ H := by
    simpa only [A, B, Nat.mul_assoc] using
      burgessFourteenthFullMultiplierBlock_le K H q
  by_cases hAB : A * B = 0
  · have : a * b = 0 := Nat.eq_zero_of_le_zero (hAB ▸ hab)
    omega
  · have hdouble : 2 * (A * B) ≤ K * (A * B) :=
      Nat.mul_le_mul_right (A * B) hK
    have hstrict : A * B < 2 * (A * B) := by
      have : 0 < A * B := Nat.pos_of_ne_zero hAB
      omega
    exact hab.trans_lt (hstrict.trans_le (hdouble.trans hfull))

/-- The power boundary gains the safety factor to the induction exponent. -/
theorem burgessFourteenthMultiplierBlock_rpow_le
    {K H q : ℕ} (hK : 1 ≤ K) :
    ((burgessFourteenthMultiplierLength K H q *
        burgessFourteenthShiftLength q : ℕ) : ℝ) ^ (6 / 7 : ℝ) ≤
      (H : ℝ) ^ (6 / 7 : ℝ) / (K : ℝ) ^ (6 / 7 : ℝ) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hblockR :
      (K : ℝ) * ((burgessFourteenthMultiplierLength K H q *
        burgessFourteenthShiftLength q : ℕ) : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (show K * (burgessFourteenthMultiplierLength K H q *
      burgessFourteenthShiftLength q) ≤ H by
        simpa only [Nat.mul_assoc] using
          burgessFourteenthFullMultiplierBlock_le K H q)
  have hbase :
      ((burgessFourteenthMultiplierLength K H q *
        burgessFourteenthShiftLength q : ℕ) : ℝ) ≤ (H : ℝ) / (K : ℝ) := by
    apply (le_div_iff₀ hKpos).2
    simpa only [Nat.cast_mul, mul_comm] using hblockR
  calc
    ((burgessFourteenthMultiplierLength K H q *
        burgessFourteenthShiftLength q : ℕ) : ℝ) ^ (6 / 7 : ℝ) ≤
        ((H : ℝ) / (K : ℝ)) ^ (6 / 7 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hbase (by norm_num)
    _ = (H : ℝ) ^ (6 / 7 : ℝ) / (K : ℝ) ^ (6 / 7 : ℝ) := by
      rw [Real.div_rpow (by positivity) hKpos.le]

/-- A safety factor whose `6/7` power is at least four makes the normalized
affine boundary consume at most half of the induction majorant. -/
theorem burgessFourteenthBoundary_half_le
    {K H q : ℕ} (hK : 1 ≤ K)
    (hKpow : (4 : ℝ) ≤ (K : ℝ) ^ (6 / 7 : ℝ))
    {C Q : ℝ} (hC : 0 ≤ C) (hQ : 0 ≤ Q) :
    2 * C * ((burgessFourteenthMultiplierLength K H q *
        burgessFourteenthShiftLength q : ℕ) : ℝ) ^ (6 / 7 : ℝ) * Q ≤
      (C / 2) * (H : ℝ) ^ (6 / 7 : ℝ) * Q := by
  have hpow := burgessFourteenthMultiplierBlock_rpow_le (H := H) (q := q) hK
  have hHpow : 0 ≤ (H : ℝ) ^ (6 / 7 : ℝ) := by positivity
  have hdiv :
      (H : ℝ) ^ (6 / 7 : ℝ) / (K : ℝ) ^ (6 / 7 : ℝ) ≤
        (H : ℝ) ^ (6 / 7 : ℝ) / 4 := by
    exact div_le_div_of_nonneg_left hHpow (by norm_num) hKpow
  calc
    2 * C * ((burgessFourteenthMultiplierLength K H q *
        burgessFourteenthShiftLength q : ℕ) : ℝ) ^ (6 / 7 : ℝ) * Q ≤
        2 * C * ((H : ℝ) ^ (6 / 7 : ℝ) /
          (K : ℝ) ^ (6 / 7 : ℝ)) * Q := by gcongr
    _ ≤ 2 * C * ((H : ℝ) ^ (6 / 7 : ℝ) / 4) * Q := by gcongr
    _ = (C / 2) * (H : ℝ) ^ (6 / 7 : ℝ) * Q := by ring

/-- The concrete safety factor `128 = 2^7` has ample contraction margin. -/
theorem four_le_oneTwentyEight_rpow_six_sevenths :
    (4 : ℝ) ≤ (128 : ℝ) ^ (6 / 7 : ℝ) := by
  calc
    (4 : ℝ) ≤ (64 : ℝ) := by norm_num
    _ = ((2 : ℝ) ^ 7) ^ (6 / 7 : ℝ) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    _ = (128 : ℝ) ^ (6 / 7 : ℝ) := by norm_num

/-- A lower length range of size `K*q^(1/14+η)` makes the rounded multiplier
length large enough to absorb the divisor-square discrepancy. -/
theorem eventually_burgessFourteenthMultiplierLength_divisorCriterion
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ K H : ℕ,
      1 ≤ K →
      (K : ℝ) * (q : ℝ) ^ ((1 / 14 : ℝ) + η) ≤ (H : ℝ) →
      2 * q.divisors.card ^ 2 ≤
        burgessFourteenthMultiplierLength K H q := by
  filter_upwards [eventually_two_mul_card_divisors_sq_le_floor_rpow hη,
    eventually_burgessFourteenthShiftLength_bounds,
    eventually_ge_atTop (1 : ℕ)] with q hdiv hB hq K H hK hscale
  let T : ℕ := ⌊(q : ℝ) ^ η⌋₊
  let B : ℕ := burgessFourteenthShiftLength q
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hBpos : 0 < B := by simpa only [B] using (show 0 < burgessFourteenthShiftLength q by omega)
  have hKBpos : 0 < K * B := Nat.mul_pos (by omega) hBpos
  have hTupper : (T : ℝ) ≤ (q : ℝ) ^ η := by
    exact Nat.floor_le (Real.rpow_nonneg hqR.le _)
  have hBupper : (B : ℝ) ≤ (q : ℝ) ^ (1 / 14 : ℝ) := by
    simpa only [B] using burgessFourteenthShiftLength_cast_le q
  have hmulReal : (T * (K * B) : ℕ) ≤ H := by
    exact_mod_cast (show (T : ℝ) * ((K : ℝ) * (B : ℝ)) ≤ (H : ℝ) by
      calc
        (T : ℝ) * ((K : ℝ) * (B : ℝ)) =
            (K : ℝ) * (B : ℝ) * (T : ℝ) := by ring
        _ ≤ (K : ℝ) * (q : ℝ) ^ (1 / 14 : ℝ) * (q : ℝ) ^ η := by
          gcongr
        _ = (K : ℝ) * (q : ℝ) ^ ((1 / 14 : ℝ) + η) := by
          rw [Real.rpow_add hqR]
          ring
        _ ≤ (H : ℝ) := hscale)
  have hTA : T ≤ burgessFourteenthMultiplierLength K H q := by
    apply (Nat.le_div_iff_mul_le hKBpos).2
    simpa only [B, burgessFourteenthMultiplierLength] using hmulReal
  have hdivT : 2 * q.divisors.card ^ 2 ≤ T := by
    simpa only [T] using hdiv
  exact hdivT.trans hTA

/-- If the interval contains two full safety-factor blocks, natural division
retains at least half of the corresponding real quotient. -/
theorem burgessFourteenthMultiplierLength_cast_lower
    {K H q : ℕ} (hK : 1 ≤ K) (hB : 1 ≤ burgessFourteenthShiftLength q)
    (hH : 2 * (K * burgessFourteenthShiftLength q) ≤ H) :
    (H : ℝ) /
        (2 * ((K : ℝ) * (burgessFourteenthShiftLength q : ℝ))) ≤
      (burgessFourteenthMultiplierLength K H q : ℝ) := by
  let d : ℕ := K * burgessFourteenthShiftLength q
  let A : ℕ := burgessFourteenthMultiplierLength K H q
  have hd : 0 < d := Nat.mul_pos (by omega) (by omega)
  have hupperNat : H < (A + 1) * d := by
    simpa only [A, d, burgessFourteenthMultiplierLength, Nat.mul_comm] using
      Nat.lt_mul_div_succ H hd
  have hupper : (H : ℝ) < ((A : ℝ) + 1) * (d : ℝ) := by
    exact_mod_cast hupperNat
  have hlower : (2 : ℝ) * (d : ℝ) ≤ (H : ℝ) := by
    exact_mod_cast (by simpa only [d] using hH)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hcross : (H : ℝ) ≤ (A : ℝ) * (2 * (d : ℝ)) := by
    nlinarith
  apply (div_le_iff₀ (by positivity : (0 : ℝ) <
    2 * ((K : ℝ) * (burgessFourteenthShiftLength q : ℝ)))).2
  simpa only [A, d, Nat.cast_mul] using hcross

/-- Eventual admissibility package for the actual rounded `r = 7` Burgess
parameters.  The lower and upper interval ranges are exposed as two scalar
hypotheses. -/
theorem eventually_burgessFourteenthParameters_admissible
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ K H : ℕ,
      1 ≤ K →
      (K : ℝ) * (q : ℝ) ^ ((1 / 14 : ℝ) + η) ≤ (H : ℝ) →
      2 * H * H ≤ q * K * burgessFourteenthShiftLength q →
      let A := burgessFourteenthMultiplierLength K H q
      let B := burgessFourteenthShiftLength q
      1 ≤ A ∧ 1 ≤ B ∧ A * B ≤ H ∧ A ≤ H ∧
        2 * A * H ≤ q ∧ 2 * q.divisors.card ^ 2 ≤ A := by
  filter_upwards [eventually_burgessFourteenthShiftLength_bounds,
    eventually_burgessFourteenthMultiplierLength_divisorCriterion hη,
    eventually_ge_atTop (1 : ℕ)] with q hB hdiv hq K H hK hlower hupper
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  have hdivA : 2 * q.divisors.card ^ 2 ≤ A := by
    simpa only [A] using hdiv K H hK hlower
  have hcard : 1 ≤ q.divisors.card := by
    apply Finset.one_le_card.mpr
    exact ⟨1, by simp [show q ≠ 0 by omega]⟩
  have hA : 1 ≤ A := by
    have hpos : 0 < 2 * q.divisors.card ^ 2 := by positivity
    omega
  have hgeom := burgessFourteenthParameter_geometry hK hB.1 hupper
  dsimp only at hgeom
  exact ⟨hA, hB.1, hgeom.1, hgeom.2.1, hgeom.2.2, hdivA⟩

/-- In the genuine Burgess core range, the lower conductor power absorbs the
fixed safety factor.  Together with the quadratic upper range, this supplies
every rounded induction datum for `K=128`. -/
theorem eventually_burgessFourteenthRoundedInductionData_of_core
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q : ℕ in atTop, ∀ H : ℕ,
      H < q →
      (q : ℝ) ^ ((2 / 49 : ℝ) + η) < (H : ℝ) ^ (1 / 7 : ℝ) →
      2 * H * H ≤ q * 128 * burgessFourteenthShiftLength q →
      BurgessFourteenthRoundedInductionData 128 H q := by
  have hscale := eventually_const_mul_nat_rpow_le_nat_rpow
    (C := (128 : ℝ))
    (a := (1 / 14 : ℝ) + η) (b := (2 / 7 : ℝ) + 7 * η) (by linarith)
  have hblock := eventually_const_mul_nat_rpow_le_nat_rpow
    (C := (256 : ℝ))
    (a := (1 / 14 : ℝ)) (b := (2 / 7 : ℝ) + 7 * η) (by linarith)
  filter_upwards [eventually_burgessFourteenthShiftLength_bounds,
    eventually_burgessFourteenthParameters_admissible hη,
    hscale, hblock, eventually_ge_atTop (1 : ℕ)] with
      q hB hadm hscale hblock hq H hHq hcore hquad
  have hcore' :
      (q : ℝ) ^ ((2 / 7 : ℝ) + 7 * η) < (H : ℝ) :=
    (taoBurgess_core_lower_iff q H η).mp hcore
  have hlower :
      (128 : ℝ) * (q : ℝ) ^ ((1 / 14 : ℝ) + η) ≤ (H : ℝ) :=
    hscale.trans hcore'.le
  have htwoBlockR :
      (256 : ℝ) * (q : ℝ) ^ (1 / 14 : ℝ) ≤ (H : ℝ) :=
    hblock.trans hcore'.le
  have htwoBlock : 2 * (128 * burgessFourteenthShiftLength q) ≤ H := by
    exact_mod_cast (show
      (2 : ℝ) * ((128 : ℝ) * (burgessFourteenthShiftLength q : ℝ)) ≤
          (H : ℝ) by
        calc
          (2 : ℝ) * ((128 : ℝ) * (burgessFourteenthShiftLength q : ℝ)) =
              256 * (burgessFourteenthShiftLength q : ℝ) := by ring
          _ ≤ 256 * (q : ℝ) ^ (1 / 14 : ℝ) := by
            exact mul_le_mul_of_nonneg_left
              (burgessFourteenthShiftLength_cast_le q) (by norm_num)
          _ ≤ (H : ℝ) := htwoBlockR)
  have hparams := hadm 128 H (by norm_num) hlower hquad
  dsimp only at hparams
  let A := burgessFourteenthMultiplierLength 128 H q
  let B := burgessFourteenthShiftLength q
  have hAq : A ≤ q := by
    have hAH : A ≤ H := by simpa only [A] using hparams.2.2.2.1
    exact hAH.trans hHq.le
  dsimp only [BurgessFourteenthRoundedInductionData]
  exact ⟨hq, hB.1, hB.2, htwoBlock, hAq,
    hparams.1, hparams.2.2.1, hparams.2.2.2.1,
    hparams.2.2.2.2.1, hparams.2.2.2.2.2⟩

/-- The harmonic loss is bounded by the same positive power of any enclosing
conductor scale. -/
theorem harmonic_cast_le_const_mul_rpow_of_le
    {δ : ℝ} (hδ : 0 < δ) {A q : ℕ} (hAq : A ≤ q) (hq : 1 ≤ q) :
    ((harmonic A : ℚ) : ℝ) ≤
      (1 + δ⁻¹) * (q : ℝ) ^ δ := by
  have hharm :=
    RiemannZeta.GuthMaynard.harmonic_le_epsilon_rpow hδ A
  have hAqR : (A : ℝ) ≤ q := by exact_mod_cast hAq
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hpowA : (A : ℝ) ^ δ ≤ (q : ℝ) ^ δ := by
    exact Real.rpow_le_rpow (Nat.cast_nonneg A) hAqR hδ.le
  have hpowOne : (1 : ℝ) ≤ (q : ℝ) ^ δ := by
    simpa using Real.one_le_rpow hqOne hδ.le
  exact hharm.trans (mul_le_mul_of_nonneg_left
    (max_le hpowOne hpowA) (by positivity))

/-- The reciprocal totient density costs only the existing divisor-epsilon
factor times a prescribed positive conductor power. -/
theorem conductor_div_totient_le_const_mul_rpow
    {δ : ℝ} (hδ : 0 < δ) {q : ℕ} (hq : 0 < q) :
    (q : ℝ) / (q.totient : ℝ) ≤
      RiemannZeta.GuthMaynard.divisorEpsilonConstant δ * (q : ℝ) ^ δ := by
  exact (conductor_div_totient_le_card_divisors q hq).trans
    (RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow hδ hq.ne')

/-- Algebraic normalization of the half-totient-density denominator. -/
theorem div_halfTotientDensity_mul_eq
    {q A B : ℕ} (hq : 0 < q) (hA : 0 < A) (hB : 0 < B) (S : ℝ) :
    S / (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) =
      2 * S * ((q : ℝ) / (q.totient : ℝ)) /
        ((A : ℝ) * (B : ℝ)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hAR : (A : ℝ) ≠ 0 := by exact_mod_cast hA.ne'
  have hBR : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hphiR : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  field_simp

/-- At any shift length `B <= q^(1/14)`, the two complete-moment scalar
summands are bounded by one `q^(3/2+ε)` monomial. -/
theorem burgessFourteenthCompleteMomentScalar_le_monomial
    {q B : ℕ} (hq : 1 ≤ q)
    (hB : (B : ℝ) ≤ (q : ℝ) ^ (1 / 14 : ℝ))
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        C * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + ε)) ≤
      (((7 ^ 14 : ℕ) : ℝ) + C) *
        (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqOne : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hB0 : (0 : ℝ) ≤ B := by positivity
  have hB7 : (B : ℝ) ^ 7 ≤ (q : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      (B : ℝ) ^ 7 ≤ ((q : ℝ) ^ (1 / 14 : ℝ)) ^ (7 : ℕ) := by
        gcongr
      _ = (q : ℝ) ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hqR.le]
        congr 1
        norm_num
  have hB14 : (B : ℝ) ^ 14 ≤ (q : ℝ) := by
    calc
      (B : ℝ) ^ 14 ≤ ((q : ℝ) ^ (1 / 14 : ℝ)) ^ (14 : ℕ) := by
        gcongr
      _ = (q : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hqR.le]
        norm_num
  have hqGrow :
      (q : ℝ) ^ (3 / 2 : ℝ) ≤ (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
    exact Real.rpow_le_rpow_of_exponent_le hqOne (by linarith)
  have hmulHalf :
      (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) =
        (q : ℝ) ^ (3 / 2 : ℝ) := by
    calc
      (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) =
          (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 : ℝ) := by simp
      _ = (q : ℝ) ^ ((1 / 2 : ℝ) + 1) :=
        (Real.rpow_add hqR (1 / 2 : ℝ) 1).symm
      _ = (q : ℝ) ^ (3 / 2 : ℝ) := by norm_num
  have hmulEps :
      (q : ℝ) * (q : ℝ) ^ ((1 / 2 : ℝ) + ε) =
        (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
    calc
      (q : ℝ) * (q : ℝ) ^ ((1 / 2 : ℝ) + ε) =
          (q : ℝ) ^ (1 : ℝ) * (q : ℝ) ^ ((1 / 2 : ℝ) + ε) := by simp
      _ = (q : ℝ) ^ ((1 : ℝ) + ((1 / 2 : ℝ) + ε)) :=
        (Real.rpow_add hqR 1 ((1 / 2 : ℝ) + ε)).symm
      _ = (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
        congr 1
        ring
  have hfirst :
      (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q) ≤
        (((7 ^ 14 : ℕ) : ℝ) * (q : ℝ) ^ ((3 / 2 : ℝ) + ε)) := by
    push_cast
    calc
      (678223072849 : ℝ) * (B : ℝ) ^ 7 * (q : ℝ) ≤
          (678223072849 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) := by
        gcongr
      _ = (678223072849 : ℝ) *
          ((q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ)) := by ring
      _ = (678223072849 : ℝ) * (q : ℝ) ^ (3 / 2 : ℝ) := by
        rw [hmulHalf]
      _ ≤ (678223072849 : ℝ) * (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
        gcongr
  have hsecond :
      C * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + ε) ≤
        C * (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
    calc
      C * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + ε) ≤
          C * (q : ℝ) * (q : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
        gcongr
      _ = C * ((q : ℝ) * (q : ℝ) ^ ((1 / 2 : ℝ) + ε)) := by ring
      _ = C * (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := by
        rw [hmulEps]
  calc
    (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        C * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + ε)) ≤
        (((7 ^ 14 : ℕ) : ℝ) * (q : ℝ) ^ ((3 / 2 : ℝ) + ε)) +
          C * (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := add_le_add hfirst hsecond
    _ = (((7 ^ 14 : ℕ) : ℝ) + C) *
        (q : ℝ) ^ ((3 / 2 : ℝ) + ε) := by ring

/-- Fourteenth-root form of the complete-moment monomial bound. -/
theorem burgessFourteenthCompleteMomentScalar_rpow_le
    {q B : ℕ} (hq : 1 ≤ q)
    (hB : (B : ℝ) ≤ (q : ℝ) ^ (1 / 14 : ℝ))
    {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) :
    ((((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        C * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + ε)) ^
          (14 : ℝ)⁻¹) ≤
      ((((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        (q : ℝ) ^ ((3 / 28 : ℝ) + ε / 14) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hbase := burgessFourteenthCompleteMomentScalar_le_monomial
    hq hB hC hε
  calc
    ((((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        C * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + ε)) ^
          (14 : ℝ)⁻¹) ≤
        ((((7 ^ 14 : ℕ) : ℝ) + C) *
          (q : ℝ) ^ ((3 / 2 : ℝ) + ε)) ^ (14 : ℝ)⁻¹ := by
      exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = ((((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        (((q : ℝ) ^ ((3 / 2 : ℝ) + ε)) ^ (14 : ℝ)⁻¹) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = ((((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        (q : ℝ) ^ ((3 / 28 : ℝ) + ε / 14) := by
      rw [← Real.rpow_mul hqR.le]
      congr 2
      norm_num
      ring

/-- Exact fourteenth-root factorization of the compressed Burgess collision
monomial. -/
theorem burgessCompressedCollisionMoment_rpow_eq
    {A H h V : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hh : 0 ≤ h) (hV : 0 ≤ V) :
    (((A * H) ^ 12 * (3 * H * A * h) * V) ^ (14 : ℝ)⁻¹) =
      (3 : ℝ) ^ (14 : ℝ)⁻¹ *
        A ^ (13 / 14 : ℝ) * H ^ (13 / 14 : ℝ) *
          h ^ (14 : ℝ)⁻¹ * V ^ (14 : ℝ)⁻¹ := by
  have hbase :
      (A * H) ^ 12 * (3 * H * A * h) * V =
        (((3 * A ^ 13) * H ^ 13) * h) * V := by ring
  have hAroot :
      ((A ^ 13) ^ (14 : ℝ)⁻¹) = A ^ (13 / 14 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hA]
    congr 1
  have hHroot :
      ((H ^ 13) ^ (14 : ℝ)⁻¹) = H ^ (13 / 14 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hH]
    congr 1
  rw [hbase]
  rw [Real.mul_rpow (by positivity) hV]
  rw [Real.mul_rpow (by positivity) hh]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  rw [hAroot, hHroot]

/-- The compressed complete-Weil main term after harmonic and moment
epsilon-power normalization, but before substituting `A ≍ H/B`. -/
theorem burgessFourteenthCompressedMain_rpow_le
    {q A H B : ℕ} (hq : 1 ≤ q) (hAq : A ≤ q)
    (hB : (B : ℝ) ≤ (q : ℝ) ^ (1 / 14 : ℝ))
    {C ε δ : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hδ : 0 < δ) :
    ((((A : ℝ) * (H : ℝ)) ^ 12 *
        (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
        (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
          C * (B : ℝ) ^ 14 *
            (q : ℝ) ^ ((1 / 2 : ℝ) + ε))) ^ (14 : ℝ)⁻¹) ≤
      ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
        (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
        (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        (A : ℝ) ^ (13 / 14 : ℝ) *
        (H : ℝ) ^ (13 / 14 : ℝ) *
        (q : ℝ) ^ ((3 / 28 : ℝ) + ε / 14 + δ / 14) := by
  let h : ℝ := ((harmonic A : ℚ) : ℝ)
  let V : ℝ :=
    (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
      C * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + ε))
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hh0 : 0 ≤ h := by
    dsimp [h]
    cases A with
    | zero => simp
    | succ K => exact_mod_cast (harmonic_pos (Nat.succ_ne_zero K)).le
  have hV0 : 0 ≤ V := by dsimp [V]; positivity
  have hharm : h ≤ (1 + δ⁻¹) * (q : ℝ) ^ δ := by
    simpa only [h] using harmonic_cast_le_const_mul_rpow_of_le hδ hAq hq
  have hharmRoot :
      h ^ (14 : ℝ)⁻¹ ≤
        (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ * (q : ℝ) ^ (δ / 14) := by
    calc
      h ^ (14 : ℝ)⁻¹ ≤
          ((1 + δ⁻¹) * (q : ℝ) ^ δ) ^ (14 : ℝ)⁻¹ :=
        Real.rpow_le_rpow hh0 hharm (by positivity)
      _ = (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
          (((q : ℝ) ^ δ) ^ (14 : ℝ)⁻¹) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ * (q : ℝ) ^ (δ / 14) := by
        rw [← Real.rpow_mul hqR.le]
        congr 2
  have hmomentRoot :
      V ^ (14 : ℝ)⁻¹ ≤
        ((((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
          (q : ℝ) ^ ((3 / 28 : ℝ) + ε / 14) := by
    simpa only [V] using
      burgessFourteenthCompleteMomentScalar_rpow_le hq hB hC hε
  have hqmul :
      (q : ℝ) ^ (δ / 14) *
          (q : ℝ) ^ ((3 / 28 : ℝ) + ε / 14) =
        (q : ℝ) ^ ((3 / 28 : ℝ) + ε / 14 + δ / 14) := by
    rw [← Real.rpow_add hqR]
    congr 1
    ring
  change ((((A : ℝ) * (H : ℝ)) ^ 12 *
    (3 * (H : ℝ) * (A : ℝ) * h) * V) ^ (14 : ℝ)⁻¹) ≤ _
  rw [burgessCompressedCollisionMoment_rpow_eq
    (Nat.cast_nonneg A) (Nat.cast_nonneg H) hh0 hV0]
  calc
    (3 : ℝ) ^ (14 : ℝ)⁻¹ * (A : ℝ) ^ (13 / 14 : ℝ) *
          (H : ℝ) ^ (13 / 14 : ℝ) * h ^ (14 : ℝ)⁻¹ * V ^ (14 : ℝ)⁻¹ ≤
        (3 : ℝ) ^ (14 : ℝ)⁻¹ * (A : ℝ) ^ (13 / 14 : ℝ) *
          (H : ℝ) ^ (13 / 14 : ℝ) *
          ((1 + δ⁻¹) ^ (14 : ℝ)⁻¹ * (q : ℝ) ^ (δ / 14)) *
          (((((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
            (q : ℝ) ^ ((3 / 28 : ℝ) + ε / 14)) := by
      gcongr
    _ = ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
          (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
          (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
          (A : ℝ) ^ (13 / 14 : ℝ) *
          (H : ℝ) ^ (13 / 14 : ℝ) *
          (q : ℝ) ^ ((3 / 28 : ℝ) + ε / 14 + δ / 14) := by
      rw [← hqmul]
      ring

/-- Cross-multiplied core of the rounded `A,B` substitution.  Keeping the
fourteenth-power base avoids all negative-exponent bookkeeping. -/
theorem burgessRoundedFourteenthBase_le
    {A B H K q : ℝ} (hA : 0 < A) (hB : 0 < B) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hq : 0 < q)
    (hHA : H ≤ 2 * K * B * A)
    (hqB : q ^ (1 / 14 : ℝ) ≤ 2 * B) :
    H ^ 13 / (A * B ^ 14) ≤
      ((2 : ℝ) ^ 14 * K * H ^ 12) / q ^ (13 / 14 : ℝ) := by
  have hqroot0 : 0 ≤ q ^ (1 / 14 : ℝ) := Real.rpow_nonneg hq.le _
  have htwoB0 : 0 ≤ 2 * B := by positivity
  have hqpow :
      q ^ (13 / 14 : ℝ) ≤ (2 * B) ^ 13 := by
    calc
      q ^ (13 / 14 : ℝ) = (q ^ (1 / 14 : ℝ)) ^ (13 : ℕ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hq.le]
        congr 1
        ring
      _ ≤ (2 * B) ^ 13 := by gcongr
  have hHpow : H ^ 13 ≤ (2 * K * B * A) * H ^ 12 := by
    calc
      H ^ 13 = H * H ^ 12 := by ring
      _ ≤ (2 * K * B * A) * H ^ 12 :=
        mul_le_mul_of_nonneg_right hHA (pow_nonneg hH 12)
  have hcross :
      H ^ 13 * q ^ (13 / 14 : ℝ) ≤
        ((2 : ℝ) ^ 14 * K * H ^ 12) * (A * B ^ 14) := by
    calc
      H ^ 13 * q ^ (13 / 14 : ℝ) ≤
          ((2 * K * B * A) * H ^ 12) * (2 * B) ^ 13 := by
        exact mul_le_mul hHpow hqpow
          (Real.rpow_nonneg hq.le _) (by positivity)
      _ = ((2 : ℝ) ^ 14 * K * H ^ 12) * (A * B ^ 14) := by ring
  exact (div_le_div_iff₀ (mul_pos hA (pow_pos hB 14))
    (Real.rpow_pos_of_pos hq _)).2 hcross

/-- Exact identity relating the normalized rooted `A,H` factor to the
fourteenth-power base used by `burgessRoundedFourteenthBase_le`. -/
theorem burgessNormalizedAH_eq_fourteenthBase_rpow
    {A B H : ℝ} (hA : 0 < A) (hB : 0 < B) (hH : 0 ≤ H) :
    A ^ (13 / 14 : ℝ) * H ^ (13 / 14 : ℝ) / (A * B) =
      (H ^ 13 / (A * B ^ 14)) ^ (14 : ℝ)⁻¹ := by
  have hHroot :
      (H ^ 13) ^ (14 : ℝ)⁻¹ = H ^ (13 / 14 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hH]
    congr 1
  have hAprod :
    A ^ (13 / 14 : ℝ) * A ^ (1 / 14 : ℝ) = A := by
    rw [← Real.rpow_add hA]
    convert Real.rpow_one A using 1
    norm_num
  have hBroot :
      (B ^ 14) ^ (14 : ℝ)⁻¹ = B := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hB.le]
    norm_num
  rw [Real.div_rpow (pow_nonneg hH 13)
    (mul_nonneg hA.le (pow_nonneg hB.le 14))]
  rw [hHroot]
  rw [Real.mul_rpow hA.le (pow_nonneg hB.le 14)]
  rw [hBroot]
  have hArootPos : 0 < A ^ (1 / 14 : ℝ) := Real.rpow_pos_of_pos hA _
  field_simp
  calc
    A ^ (13 / 14 : ℝ) * H ^ (13 / 14 : ℝ) * A ^ (1 / 14 : ℝ) =
        H ^ (13 / 14 : ℝ) *
          (A ^ (13 / 14 : ℝ) * A ^ (1 / 14 : ℝ)) := by ring
    _ = H ^ (13 / 14 : ℝ) * A := by rw [hAprod]
    _ = H ^ (13 / 14 : ℝ) * A := rfl

/-- Fourteenth-root rounded substitution.  This is the precise step that
changes the normalized `A,H` factor to `H^(6/7)` and contributes
`q^(-13/196)` from the rounded shift length. -/
theorem burgessNormalizedAH_le_roundedPower
    {A B H K q : ℝ} (hA : 0 < A) (hB : 0 < B) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hq : 0 < q)
    (hHA : H ≤ 2 * K * B * A)
    (hqB : q ^ (1 / 14 : ℝ) ≤ 2 * B) :
    A ^ (13 / 14 : ℝ) * H ^ (13 / 14 : ℝ) / (A * B) ≤
      2 * K ^ (14 : ℝ)⁻¹ * H ^ (6 / 7 : ℝ) /
        q ^ (13 / 196 : ℝ) := by
  have hbase := burgessRoundedFourteenthBase_le
    hA hB hH hK hq hHA hqB
  rw [burgessNormalizedAH_eq_fourteenthBase_rpow hA hB hH]
  calc
    (H ^ 13 / (A * B ^ 14)) ^ (14 : ℝ)⁻¹ ≤
        (((2 : ℝ) ^ 14 * K * H ^ 12) /
          q ^ (13 / 14 : ℝ)) ^ (14 : ℝ)⁻¹ := by
      exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
    _ = 2 * K ^ (14 : ℝ)⁻¹ * H ^ (6 / 7 : ℝ) /
        q ^ (13 / 196 : ℝ) := by
      have hTwoRoot :
          (((2 : ℝ) ^ 14) ^ (14 : ℝ)⁻¹) = 2 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hHRoot :
          ((H ^ 12) ^ (14 : ℝ)⁻¹) = H ^ (6 / 7 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hH]
        congr 1
        norm_num
      have hqRoot :
          ((q ^ (13 / 14 : ℝ)) ^ (14 : ℝ)⁻¹) =
            q ^ (13 / 196 : ℝ) := by
        rw [← Real.rpow_mul hq.le]
        congr 1
        norm_num
      rw [Real.div_rpow (by positivity) (by positivity)]
      rw [Real.mul_rpow (by positivity) (pow_nonneg hH 12)]
      rw [Real.mul_rpow (pow_nonneg (by norm_num) 14) hK]
      rw [hTwoRoot, hHRoot, hqRoot]

/-- Natural-parameter specialization of the rounded root substitution. -/
theorem burgessFourteenthRounded_normalizedAH_le
    {K H q : ℕ} (hK : 1 ≤ K) (hq : 1 ≤ q)
    (hB : (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤
      (burgessFourteenthShiftLength q : ℝ))
    (hH : 2 * (K * burgessFourteenthShiftLength q) ≤ H) :
    let A := burgessFourteenthMultiplierLength K H q
    let B := burgessFourteenthShiftLength q
    (A : ℝ) ^ (13 / 14 : ℝ) * (H : ℝ) ^ (13 / 14 : ℝ) /
        ((A : ℝ) * (B : ℝ)) ≤
      2 * (K : ℝ) ^ (14 : ℝ)⁻¹ * (H : ℝ) ^ (6 / 7 : ℝ) /
        (q : ℝ) ^ (13 / 196 : ℝ) := by
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  have hBnat : 1 ≤ B := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hqroot : (1 : ℝ) ≤ (q : ℝ) ^ (1 / 14 : ℝ) :=
      Real.one_le_rpow hqR (by norm_num)
    have hBreal : (1 / 2 : ℝ) ≤ B := by
      have : (1 / 2 : ℝ) ≤ (q : ℝ) ^ (1 / 14 : ℝ) / 2 := by linarith
      exact this.trans (by simpa only [B] using hB)
    have hBpos : 0 < B := by
      by_contra hnot
      have hBzero : B = 0 := Nat.eq_zero_of_not_pos hnot
      norm_num [hBzero] at hBreal
    exact hBpos
  have hKBpos : 0 < K * B := Nat.mul_pos (by omega) (by omega)
  have hAone : 1 ≤ A := by
    have hKBle : K * B ≤ H := by
      have htwo : 2 * (K * B) ≤ H := by simpa only [B] using hH
      omega
    dsimp only [A, B, burgessFourteenthMultiplierLength]
    apply (Nat.le_div_iff_mul_le hKBpos).2
    simpa only [one_mul, B] using hKBle
  have hAlower := burgessFourteenthMultiplierLength_cast_lower
    hK (by simpa only [B] using hBnat) hH
  have hdenPos :
      (0 : ℝ) < 2 * ((K : ℝ) * (B : ℝ)) := by positivity
  have hHA : (H : ℝ) ≤ 2 * (K : ℝ) * (B : ℝ) * (A : ℝ) := by
    have := (div_le_iff₀ hdenPos).mp (by
      simpa only [A, B] using hAlower)
    nlinarith
  have hqB : (q : ℝ) ^ (1 / 14 : ℝ) ≤ 2 * (B : ℝ) := by
    have : (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤ (B : ℝ) := by
      simpa only [B] using hB
    linarith
  exact burgessNormalizedAH_le_roundedPower
    (by exact_mod_cast hAone) (by exact_mod_cast hBnat)
    (Nat.cast_nonneg H) (Nat.cast_nonneg K)
    (by exact_mod_cast (show 0 < q by omega)) hHA hqB

/-- The rounded `A,B` substitution applied to the complete compressed main
term.  The exponent difference `3/28 - 13/196` is normalized to `2/49`. -/
theorem burgessFourteenthRoundedCompressedMain_div_le
    {K H q : ℕ} (hK : 1 ≤ K) (hq : 1 ≤ q)
    (hBnat : 1 ≤ burgessFourteenthShiftLength q)
    (hBlower : (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤
      (burgessFourteenthShiftLength q : ℝ))
    (hH : 2 * (K * burgessFourteenthShiftLength q) ≤ H)
    (hAq : burgessFourteenthMultiplierLength K H q ≤ q)
    {C ε δ : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hδ : 0 < δ) :
    let A := burgessFourteenthMultiplierLength K H q
    let B := burgessFourteenthShiftLength q
    (((((A : ℝ) * (H : ℝ)) ^ 12 *
        (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
        (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
          C * (B : ℝ) ^ 14 *
            (q : ℝ) ^ ((1 / 2 : ℝ) + ε))) ^ (14 : ℝ)⁻¹) /
          ((A : ℝ) * (B : ℝ)) ≤
      2 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
        (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
        (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        (K : ℝ) ^ (14 : ℝ)⁻¹ *
        (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + ε / 14 + δ / 14)) := by
  dsimp only
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  let C₀ : ℝ :=
    (3 : ℝ) ^ (14 : ℝ)⁻¹ *
      (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
      (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹
  let e : ℝ := (3 / 28 : ℝ) + ε / 14 + δ / 14
  let S : ℝ :=
    ((((A : ℝ) * (H : ℝ)) ^ 12 *
      (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
      (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        C * (B : ℝ) ^ 14 *
          (q : ℝ) ^ ((1 / 2 : ℝ) + ε))) ^ (14 : ℝ)⁻¹)
  have hKBpos : 0 < K * B := Nat.mul_pos (by omega) (by simpa only [B] using hBnat)
  have hAone : 1 ≤ A := by
    have hKBle : K * B ≤ H := by
      have htwo : 2 * (K * B) ≤ H := by simpa only [B] using hH
      omega
    dsimp only [A, B, burgessFourteenthMultiplierLength]
    apply (Nat.le_div_iff_mul_le hKBpos).2
    simpa only [one_mul, B] using hKBle
  have hdenPos : (0 : ℝ) < (A : ℝ) * (B : ℝ) := by positivity
  have hmain :
      S ≤ C₀ * (A : ℝ) ^ (13 / 14 : ℝ) *
        (H : ℝ) ^ (13 / 14 : ℝ) * (q : ℝ) ^ e := by
    simpa only [S, C₀, e] using (burgessFourteenthCompressedMain_rpow_le
      (H := H) hq (by simpa only [A] using hAq)
      (by simpa only [B] using burgessFourteenthShiftLength_cast_le q)
      hC hε hδ)
  have hmainDiv :
      S / ((A : ℝ) * (B : ℝ)) ≤
        (C₀ * (A : ℝ) ^ (13 / 14 : ℝ) *
          (H : ℝ) ^ (13 / 14 : ℝ) * (q : ℝ) ^ e) /
          ((A : ℝ) * (B : ℝ)) := by
    exact div_le_div_of_nonneg_right hmain hdenPos.le
  have hrounded := burgessFourteenthRounded_normalizedAH_le
    hK hq hBlower hH
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hqexp :
      (q : ℝ) ^ e / (q : ℝ) ^ (13 / 196 : ℝ) =
        (q : ℝ) ^ ((2 / 49 : ℝ) + ε / 14 + δ / 14) := by
    rw [← Real.rpow_sub hqR]
    congr 1
    dsimp [e]
    ring
  change S / ((A : ℝ) * (B : ℝ)) ≤ _
  calc
    S / ((A : ℝ) * (B : ℝ)) ≤
        (C₀ * (A : ℝ) ^ (13 / 14 : ℝ) *
          (H : ℝ) ^ (13 / 14 : ℝ) * (q : ℝ) ^ e) /
            ((A : ℝ) * (B : ℝ)) := hmainDiv
    _ = C₀ *
        ((A : ℝ) ^ (13 / 14 : ℝ) * (H : ℝ) ^ (13 / 14 : ℝ) /
          ((A : ℝ) * (B : ℝ))) * (q : ℝ) ^ e := by ring
    _ ≤ C₀ *
        (2 * (K : ℝ) ^ (14 : ℝ)⁻¹ * (H : ℝ) ^ (6 / 7 : ℝ) /
          (q : ℝ) ^ (13 / 196 : ℝ)) * (q : ℝ) ^ e := by
      gcongr
    _ = 2 * C₀ * (K : ℝ) ^ (14 : ℝ)⁻¹ *
        (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + ε / 14 + δ / 14) := by
      rw [show
        C₀ * (2 * (K : ℝ) ^ (14 : ℝ)⁻¹ * (H : ℝ) ^ (6 / 7 : ℝ) /
          (q : ℝ) ^ (13 / 196 : ℝ)) * (q : ℝ) ^ e =
        2 * C₀ * (K : ℝ) ^ (14 : ℝ)⁻¹ * (H : ℝ) ^ (6 / 7 : ℝ) *
          ((q : ℝ) ^ e / (q : ℝ) ^ (13 / 196 : ℝ)) by ring]
      rw [hqexp]
    _ = 2 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
        (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
        (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        (K : ℝ) ^ (14 : ℝ)⁻¹ *
        (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + ε / 14 + δ / 14) := by
      rfl

/-- The rounded compressed main term after restoring the exact half-totient
density normalization.  The three conductor losses are displayed separately:
the complete moment contributes `ε / 14`, the harmonic bound contributes
`δ / 14`, and the reciprocal totient density contributes `δt`. -/
theorem burgessFourteenthRoundedCompressedMain_totient_le
    {K H q : ℕ} (hK : 1 ≤ K) (hq : 1 ≤ q)
    (hBnat : 1 ≤ burgessFourteenthShiftLength q)
    (hBlower : (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤
      (burgessFourteenthShiftLength q : ℝ))
    (hH : 2 * (K * burgessFourteenthShiftLength q) ≤ H)
    (hAq : burgessFourteenthMultiplierLength K H q ≤ q)
    {C ε δ δt : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hδ : 0 < δ) (hδt : 0 < δt) :
    let A := burgessFourteenthMultiplierLength K H q
    let B := burgessFourteenthShiftLength q
    let S : ℝ := (((A : ℝ) * (H : ℝ)) ^ 12 *
      (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
      (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        C * (B : ℝ) ^ 14 *
          (q : ℝ) ^ ((1 / 2 : ℝ) + ε))) ^ (14 : ℝ)⁻¹
    2 * S * ((q : ℝ) / (q.totient : ℝ)) /
          ((A : ℝ) * (B : ℝ)) ≤
      4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
        (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
        (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        RiemannZeta.GuthMaynard.divisorEpsilonConstant δt *
        (K : ℝ) ^ (14 : ℝ)⁻¹ *
        (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + ε / 14 + δ / 14 + δt) := by
  dsimp only
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  let S : ℝ :=
    (((A : ℝ) * (H : ℝ)) ^ 12 *
      (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
      (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        C * (B : ℝ) ^ 14 *
          (q : ℝ) ^ ((1 / 2 : ℝ) + ε))) ^ (14 : ℝ)⁻¹
  let M : ℝ :=
    2 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
      (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
      (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
      (K : ℝ) ^ (14 : ℝ)⁻¹ *
      (H : ℝ) ^ (6 / 7 : ℝ) *
      (q : ℝ) ^ ((2 / 49 : ℝ) + ε / 14 + δ / 14)
  have hmain : S / ((A : ℝ) * (B : ℝ)) ≤ M := by
    simpa only [S, M, A, B] using
      (burgessFourteenthRoundedCompressedMain_div_le
        hK hq hBnat hBlower hH hAq hC hε hδ)
  have htot :
      (q : ℝ) / (q.totient : ℝ) ≤
        RiemannZeta.GuthMaynard.divisorEpsilonConstant δt *
          (q : ℝ) ^ δt :=
    conductor_div_totient_le_const_mul_rpow hδt (by omega)
  have hprod :
      (S / ((A : ℝ) * (B : ℝ))) * ((q : ℝ) / (q.totient : ℝ)) ≤
        M * (RiemannZeta.GuthMaynard.divisorEpsilonConstant δt *
          (q : ℝ) ^ δt) := by
    exact mul_le_mul hmain htot (by positivity) (by positivity)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  change 2 * S * ((q : ℝ) / (q.totient : ℝ)) /
      ((A : ℝ) * (B : ℝ)) ≤ _
  calc
    2 * S * ((q : ℝ) / (q.totient : ℝ)) /
        ((A : ℝ) * (B : ℝ)) =
        2 * ((S / ((A : ℝ) * (B : ℝ))) *
          ((q : ℝ) / (q.totient : ℝ))) := by ring
    _ ≤ 2 * (M *
        (RiemannZeta.GuthMaynard.divisorEpsilonConstant δt *
          (q : ℝ) ^ δt)) := mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
        (1 + δ⁻¹) ^ (14 : ℝ)⁻¹ *
        (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        RiemannZeta.GuthMaynard.divisorEpsilonConstant δt *
        (K : ℝ) ^ (14 : ℝ)⁻¹ *
        (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + ε / 14 + δ / 14 + δt) := by
      rw [Real.rpow_add hqR]
      dsimp [M]
      ring

/-- A single-epsilon form of the rounded half-totient-density main term.
The allocation `6η / 14 + η / 14 + η / 2 = η` reserves respectively the
complete-moment, harmonic, and reciprocal-totient losses. -/
theorem burgessFourteenthRoundedCompressedMain_epsilon_le
    {K H q : ℕ} (hK : 1 ≤ K) (hq : 1 ≤ q)
    (hBnat : 1 ≤ burgessFourteenthShiftLength q)
    (hBlower : (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤
      (burgessFourteenthShiftLength q : ℝ))
    (hH : 2 * (K * burgessFourteenthShiftLength q) ≤ H)
    (hAq : burgessFourteenthMultiplierLength K H q ≤ q)
    {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η) :
    let A := burgessFourteenthMultiplierLength K H q
    let B := burgessFourteenthShiftLength q
    let S : ℝ := (((A : ℝ) * (H : ℝ)) ^ 12 *
      (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) *
      (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        C * (B : ℝ) ^ 14 *
          (q : ℝ) ^ ((1 / 2 : ℝ) + 6 * η))) ^ (14 : ℝ)⁻¹
    2 * S * ((q : ℝ) / (q.totient : ℝ)) /
          ((A : ℝ) * (B : ℝ)) ≤
      4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
        (1 + η⁻¹) ^ (14 : ℝ)⁻¹ *
        (((7 ^ 14 : ℕ) : ℝ) + C) ^ (14 : ℝ)⁻¹) *
        RiemannZeta.GuthMaynard.divisorEpsilonConstant (η / 2) *
        (K : ℝ) ^ (14 : ℝ)⁻¹ *
        (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
  have h6η : 0 ≤ 6 * η := by positivity
  have hηhalf : 0 < η / 2 := by positivity
  convert burgessFourteenthRoundedCompressedMain_totient_le
    hK hq hBnat hBlower hH hAq hC h6η hη hηhalf using 1
  ring_nf

/-- The rounded main estimate and the contractive affine boundary assembled
inside the complete-Weil scalar recurrence.  The moment constant is selected
once from the analytic input; the induction constant `C₂` remains explicit,
and exactly one half of it is consumed by the two translated intervals. -/
theorem exists_norm_burgessIntervalCharacterSum_le_rounded_epsilon_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {η : ℝ} (hη : 0 < η) :
    ∃ Cw : ℝ, 0 < Cw ∧
      ∀ {K H q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        1 ≤ q → TaoCubefree q → DirichletCharacter.IsPrimitive χ →
        1 ≤ K → (4 : ℝ) ≤ (K : ℝ) ^ (6 / 7 : ℝ) →
        1 ≤ burgessFourteenthShiftLength q →
        (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤
          (burgessFourteenthShiftLength q : ℝ) →
        2 * (K * burgessFourteenthShiftLength q) ≤ H →
        burgessFourteenthMultiplierLength K H q ≤ q →
        let A := burgessFourteenthMultiplierLength K H q
        let B := burgessFourteenthShiftLength q
        let Q := (q : ℝ) ^ ((2 / 49 : ℝ) + η)
        1 ≤ A → A * B ≤ H → A ≤ H → 2 * A * H ≤ q →
        2 * q.divisors.card ^ 2 ≤ A →
        ∀ {C₂ : ℝ}, 0 ≤ C₂ →
        (∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∀ b ∈ Finset.Ioc 0 B,
            ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
              C₂ * (a * b : ℝ) ^ (6 / 7 : ℝ) * Q) →
        (∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
          ∀ b ∈ Finset.Ioc 0 B,
            ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
              C₂ * (a * b : ℝ) ^ (6 / 7 : ℝ) * Q) →
        ‖burgessIntervalCharacterSum χ N H‖ ≤
          (4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
              (1 + η⁻¹) ^ (14 : ℝ)⁻¹ *
              (((7 ^ 14 : ℕ) : ℝ) + Cw) ^ (14 : ℝ)⁻¹) *
              RiemannZeta.GuthMaynard.divisorEpsilonConstant (η / 2) *
              (K : ℝ) ^ (14 : ℝ)⁻¹ + C₂ / 2) *
            (H : ℝ) ^ (6 / 7 : ℝ) * Q := by
  obtain ⟨Cw, hCw, hmoment⟩ :=
    exists_burgess_shift_fourteenth_moment_le_of_completeWeil_rpow hweil
      (show 0 < 6 * η by positivity)
  refine ⟨Cw, hCw, ?_⟩
  intro K H q N _ χ hq hcube hχ hK hKpow hB hBlower hH hAq
  dsimp only
  intro hA hAB hAH hAHq hdiv C₂ hC₂ hleft hright
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  let Q : ℝ := (q : ℝ) ^ ((2 / 49 : ℝ) + η)
  let V : ℝ :=
    (((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
      Cw * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + 6 * η))
  let S : ℝ :=
    (((A : ℝ) * (H : ℝ)) ^ 12 *
      (3 * (H : ℝ) * (A : ℝ) * (((harmonic A : ℚ) : ℝ))) * V) ^
        (14 : ℝ)⁻¹
  have hQ : 0 ≤ Q := by positivity
  have hV :
      (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤ V := by
    simpa only [V, B] using hmoment χ hcube hχ
  have hrec :
      ‖burgessIntervalCharacterSum χ N H‖ ≤
        S / (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) +
          2 * C₂ * (A * B : ℝ) ^ (6 / 7 : ℝ) * Q := by
    simpa only [S, A, B, Q, V] using
      (norm_burgessIntervalCharacterSum_le_fourteenthScalarCompressed_add_rpowBoundary
        χ hA hB hAB hAH hAHq hdiv hC₂ hQ (by norm_num) hleft hright hV)
  have hmainNorm :
      2 * S * ((q : ℝ) / (q.totient : ℝ)) /
          ((A : ℝ) * (B : ℝ)) ≤
        4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
          (1 + η⁻¹) ^ (14 : ℝ)⁻¹ *
          (((7 ^ 14 : ℕ) : ℝ) + Cw) ^ (14 : ℝ)⁻¹) *
          RiemannZeta.GuthMaynard.divisorEpsilonConstant (η / 2) *
          (K : ℝ) ^ (14 : ℝ)⁻¹ *
          (H : ℝ) ^ (6 / 7 : ℝ) * Q := by
    simpa only [S, V, A, B, Q] using
      (burgessFourteenthRoundedCompressedMain_epsilon_le
        hK hq hB hBlower hH hAq hCw.le hη)
  have hmain :
      S / (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) ≤
        4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
          (1 + η⁻¹) ^ (14 : ℝ)⁻¹ *
          (((7 ^ 14 : ℕ) : ℝ) + Cw) ^ (14 : ℝ)⁻¹) *
          RiemannZeta.GuthMaynard.divisorEpsilonConstant (η / 2) *
          (K : ℝ) ^ (14 : ℝ)⁻¹ *
          (H : ℝ) ^ (6 / 7 : ℝ) * Q := by
    rw [div_halfTotientDensity_mul_eq (by omega) (by omega) (by omega)]
    exact hmainNorm
  have hboundary :
      2 * C₂ * (A * B : ℝ) ^ (6 / 7 : ℝ) * Q ≤
        (C₂ / 2) * (H : ℝ) ^ (6 / 7 : ℝ) * Q := by
    simpa only [A, B, Nat.cast_mul] using
      (burgessFourteenthBoundary_half_le (H := H) (q := q)
        hK hKpow hC₂ hQ)
  calc
    ‖burgessIntervalCharacterSum χ N H‖ ≤
        S / (((A : ℝ) * (q.totient : ℝ) / (q : ℝ) / 2) * (B : ℝ)) +
          2 * C₂ * (A * B : ℝ) ^ (6 / 7 : ℝ) * Q := hrec
    _ ≤ 4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
          (1 + η⁻¹) ^ (14 : ℝ)⁻¹ *
          (((7 ^ 14 : ℕ) : ℝ) + Cw) ^ (14 : ℝ)⁻¹) *
          RiemannZeta.GuthMaynard.divisorEpsilonConstant (η / 2) *
          (K : ℝ) ^ (14 : ℝ)⁻¹ *
          (H : ℝ) ^ (6 / 7 : ℝ) * Q +
        (C₂ / 2) * (H : ℝ) ^ (6 / 7 : ℝ) * Q :=
      add_le_add hmain hboundary
    _ = (4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
              (1 + η⁻¹) ^ (14 : ℝ)⁻¹ *
              (((7 ^ 14 : ℕ) : ℝ) + Cw) ^ (14 : ℝ)⁻¹) *
              RiemannZeta.GuthMaynard.divisorEpsilonConstant (η / 2) *
              (K : ℝ) ^ (14 : ℝ)⁻¹ + C₂ / 2) *
            (H : ℝ) ^ (6 / 7 : ℝ) * Q := by ring

/-- Quantitative induction step for the rounded Burgess recurrence.  Doubling
the main-term coefficient leaves exactly one copy for the main term and one
copy for the half-sized affine boundary. -/
theorem exists_burgessRoundedInductionStep_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {η : ℝ} (hη : 0 < η) {K : ℕ} (hK : 2 ≤ K)
    (hKpow : (4 : ℝ) ≤ (K : ℝ) ^ (6 / 7 : ℝ)) :
    ∃ Cb : ℝ, 1 ≤ Cb ∧
      ∀ {H q N : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        1 ≤ q → TaoCubefree q → DirichletCharacter.IsPrimitive χ →
        1 ≤ burgessFourteenthShiftLength q →
        (q : ℝ) ^ (1 / 14 : ℝ) / 2 ≤
          (burgessFourteenthShiftLength q : ℝ) →
        2 * (K * burgessFourteenthShiftLength q) ≤ H →
        burgessFourteenthMultiplierLength K H q ≤ q →
        let A := burgessFourteenthMultiplierLength K H q
        let B := burgessFourteenthShiftLength q
        1 ≤ A → A * B ≤ H → A ≤ H → 2 * A * H ≤ q →
        2 * q.divisors.card ^ 2 ≤ A →
        (∀ L < H, ∀ M : ℕ,
          ‖burgessIntervalCharacterSum χ M L‖ ≤
            Cb * (L : ℝ) ^ (6 / 7 : ℝ) *
              (q : ℝ) ^ ((2 / 49 : ℝ) + η)) →
        ‖burgessIntervalCharacterSum χ N H‖ ≤
          Cb * (H : ℝ) ^ (6 / 7 : ℝ) *
            (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
  obtain ⟨Cw, hCw, hassemble⟩ :=
    exists_norm_burgessIntervalCharacterSum_le_rounded_epsilon_of_completeWeil
      hweil hη
  let Mmain : ℝ :=
    4 * ((3 : ℝ) ^ (14 : ℝ)⁻¹ *
      (1 + η⁻¹) ^ (14 : ℝ)⁻¹ *
      (((7 ^ 14 : ℕ) : ℝ) + Cw) ^ (14 : ℝ)⁻¹) *
      RiemannZeta.GuthMaynard.divisorEpsilonConstant (η / 2) *
      (K : ℝ) ^ (14 : ℝ)⁻¹
  let Cb : ℝ := max (2 * Mmain) 1
  have hMmain : 0 < Mmain := by
    have hOneEta : 0 < 1 + η⁻¹ := by positivity
    have hCterm : 0 < (((7 ^ 14 : ℕ) : ℝ) + Cw) := by positivity
    have hD : 0 < RiemannZeta.GuthMaynard.divisorEpsilonConstant (η / 2) :=
      RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos (η / 2)
    dsimp [Mmain]
    positivity
  have hCbOne : 1 ≤ Cb := by exact le_max_right _ _
  have hCbMain : 2 * Mmain ≤ Cb := by exact le_max_left _ _
  refine ⟨Cb, hCbOne, ?_⟩
  intro H q N _ χ hq hcube hχ hB hBlower hH hAq
  dsimp only
  intro hA hAB hAH hAHq hdiv hind
  let A := burgessFourteenthMultiplierLength K H q
  let B := burgessFourteenthShiftLength q
  let Q : ℝ := (q : ℝ) ^ ((2 / 49 : ℝ) + η)
  have hHpos : 1 ≤ H := by
    have hKBpos : 0 < K * burgessFourteenthShiftLength q :=
      Nat.mul_pos (by omega) (by omega)
    omega
  have hleft :
      ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ∀ b ∈ Finset.Ioc 0 B,
          ‖burgessIntervalCharacterSum χ N (a * b)‖ ≤
            Cb * (a * b : ℝ) ^ (6 / 7 : ℝ) * Q := by
    intro a ha b hb
    have haA : a ≤ A := (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).2
    have hbB : b ≤ B := (Finset.mem_Ioc.mp hb).2
    have hablt := burgessFourteenthMultiplierProduct_lt hK hHpos
      (by simpa only [A] using haA) (by simpa only [B] using hbB)
    simpa only [Q, Nat.cast_mul] using (hind (a * b) hablt N)
  have hright :
      ∀ a ∈ (Finset.Ioc 0 A).filter (fun a => Nat.Coprime a q),
        ∀ b ∈ Finset.Ioc 0 B,
          ‖burgessIntervalCharacterSum χ (N + H) (a * b)‖ ≤
            Cb * (a * b : ℝ) ^ (6 / 7 : ℝ) * Q := by
    intro a ha b hb
    have haA : a ≤ A := (Finset.mem_Ioc.mp (Finset.mem_filter.mp ha).1).2
    have hbB : b ≤ B := (Finset.mem_Ioc.mp hb).2
    have hablt := burgessFourteenthMultiplierProduct_lt hK hHpos
      (by simpa only [A] using haA) (by simpa only [B] using hbB)
    simpa only [Q, Nat.cast_mul] using (hind (a * b) hablt (N + H))
  have hout := hassemble χ hq hcube hχ (by omega) hKpow hB hBlower hH hAq
    hA hAB hAH hAHq hdiv (C₂ := Cb) (by positivity) hleft hright
  have hcoefficient : Mmain + Cb / 2 ≤ Cb := by linarith
  change ‖burgessIntervalCharacterSum χ N H‖ ≤
    Cb * (H : ℝ) ^ (6 / 7 : ℝ) * Q
  calc
    ‖burgessIntervalCharacterSum χ N H‖ ≤
        (Mmain + Cb / 2) * (H : ℝ) ^ (6 / 7 : ℝ) * Q := by
      simpa only [Mmain, Q] using hout
    _ ≤ Cb * (H : ℝ) ^ (6 / 7 : ℝ) * Q := by gcongr

/-- Below the nontrivial Burgess core threshold, the trivial interval bound
already has the desired two-factor shape for every coefficient at least one. -/
theorem norm_burgessIntervalCharacterSum_le_of_not_burgessCore
    {q N H : ℕ} (χ : DirichletCharacter ℂ q) {C η : ℝ} (hC : 1 ≤ C)
    (hsmall : ¬(q : ℝ) ^ ((2 / 49 : ℝ) + η) <
      (H : ℝ) ^ (1 / 7 : ℝ)) :
    ‖burgessIntervalCharacterSum χ N H‖ ≤
      C * (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
  by_cases hH : H = 0
  · subst H
    simp [burgessIntervalCharacterSum]
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hthreshold :
      (H : ℝ) ^ (1 / 7 : ℝ) ≤
        (q : ℝ) ^ ((2 / 49 : ℝ) + η) := le_of_not_gt hsmall
  have hsplit :
      (H : ℝ) = (H : ℝ) ^ (6 / 7 : ℝ) *
        (H : ℝ) ^ (1 / 7 : ℝ) := by
    rw [← Real.rpow_add hHpos]
    norm_num
  calc
    ‖burgessIntervalCharacterSum χ N H‖ ≤ (H : ℝ) :=
      norm_burgessIntervalCharacterSum_le χ
    _ = (H : ℝ) ^ (6 / 7 : ℝ) * (H : ℝ) ^ (1 / 7 : ℝ) := hsplit
    _ ≤ (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by gcongr
    _ ≤ C * (H : ℝ) ^ (6 / 7 : ℝ) *
        (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
      have hfactor :
          (H : ℝ) ^ (6 / 7 : ℝ) ≤
            C * (H : ℝ) ^ (6 / 7 : ℝ) := by
        calc
          (H : ℝ) ^ (6 / 7 : ℝ) =
              1 * (H : ℝ) ^ (6 / 7 : ℝ) := by ring
          _ ≤ C * (H : ℝ) ^ (6 / 7 : ℝ) :=
            mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hHpos.le _)
      exact mul_le_mul_of_nonneg_right
        hfactor
        (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- The complete-Weil hypothesis implies the primitive Burgess estimate on
the entire eventual medium range where the no-wrap quadratic inequality
holds.  Strong induction supplies both translated shorter intervals; below
the core threshold those intervals are closed by the trivial estimate. -/
theorem exists_eventually_norm_burgessIntervalCharacterSum_le_medium_of_completeWeil
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {η : ℝ} (hη : 0 < η) :
    ∃ Cb : ℝ, 0 < Cb ∧
      ∀ᶠ q : ℕ in atTop, ∀ (χ : DirichletCharacter ℂ q),
        TaoCubefree q → DirichletCharacter.IsPrimitive χ →
        ∀ H N : ℕ, H < q →
          (q : ℝ) ^ ((2 / 49 : ℝ) + η) <
            (H : ℝ) ^ (1 / 7 : ℝ) →
          2 * H * H ≤ q * 128 * burgessFourteenthShiftLength q →
          ‖burgessIntervalCharacterSum χ N H‖ ≤
            Cb * (H : ℝ) ^ (6 / 7 : ℝ) *
              (q : ℝ) ^ ((2 / 49 : ℝ) + η) := by
  obtain ⟨Cb, hCbOne, hstep⟩ :=
    exists_burgessRoundedInductionStep_of_completeWeil hweil hη
      (K := 128) (by norm_num) four_le_oneTwentyEight_rpow_six_sevenths
  refine ⟨Cb, zero_lt_one.trans_le hCbOne, ?_⟩
  filter_upwards [eventually_burgessFourteenthRoundedInductionData_of_core hη]
    with q hdata
  intro χ hcube hχ
  have hq0 : q ≠ 0 := hcube.ne_zero
  letI : NeZero q := ⟨hq0⟩
  intro H
  induction H using Nat.strong_induction_on with
  | h H ih =>
      intro N hHq hcore hquad
      have hd := hdata H hHq hcore hquad
      dsimp only [BurgessFourteenthRoundedInductionData] at hd
      rcases hd with ⟨hq, hB, hBlower, hblock, hAq, hA, hAB, hAH, hAHq, hdiv⟩
      apply hstep χ hq hcube hχ hB hBlower hblock hAq hA hAB hAH hAHq hdiv
      intro L hLH M
      by_cases hLcore :
          (q : ℝ) ^ ((2 / 49 : ℝ) + η) < (L : ℝ) ^ (1 / 7 : ℝ)
      · apply ih L hLH M (hLH.trans hHq) hLcore
        have hLL : L * L ≤ H * H :=
          Nat.mul_le_mul (Nat.le_of_lt hLH) (Nat.le_of_lt hLH)
        simpa only [Nat.mul_assoc] using
          ((Nat.mul_le_mul_left 2 hLL).trans (by
            simpa only [Nat.mul_assoc] using hquad))
      · exact norm_burgessIntervalCharacterSum_le_of_not_burgessCore
          χ hCbOne hLcore

end


end Tao2026
