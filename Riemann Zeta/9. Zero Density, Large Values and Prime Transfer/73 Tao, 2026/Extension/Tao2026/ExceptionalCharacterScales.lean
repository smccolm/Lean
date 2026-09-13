import Tao2026.ExceptionalCharacterBurgess
import GafniTao.Asymptotics
import Mathlib.NumberTheory.Bertrand

/-!
# Canonical scales in Tao's proof of Lemma 5.1

This file rounds the source choice `R = Z^0.0001` and verifies the elementary
large-prefix and Burgess-range conditions required by
`ExceptionalCharacterBurgess`.
-/

namespace Tao2026

open Filter Asymptotics

noncomputable section

/-- The literal floor-rounded version of Tao's sieve level `Z^0.0001`. -/
def taoExceptionalSieveLevel (Z : ℕ) : ℕ :=
  Nat.floor ((Z : ℝ) ^ taoExceptionalSieveLevelExponent)

/-- The complementary exponent `0.9999` for the shortest sieve prefix. -/
def taoExceptionalPrefixExponent : ℝ :=
  1 - taoExceptionalSieveLevelExponent

/-- A floor-rounded lower comparison for all sieve prefixes. -/
def taoExceptionalPrefixFloor (Z : ℕ) : ℕ :=
  Nat.floor ((Z : ℝ) ^ taoExceptionalPrefixExponent)

theorem taoExceptionalSieveLevel_cast_le (Z : ℕ) :
    (taoExceptionalSieveLevel Z : ℝ) ≤
      (Z : ℝ) ^ taoExceptionalSieveLevelExponent := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg Z) _)

theorem taoExceptionalPrefixFloor_cast_le (Z : ℕ) :
    (taoExceptionalPrefixFloor Z : ℝ) ≤
      (Z : ℝ) ^ taoExceptionalPrefixExponent := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg Z) _)

theorem taoExceptional_exponents_add :
    taoExceptionalPrefixExponent + taoExceptionalSieveLevelExponent = 1 := by
  simp [taoExceptionalPrefixExponent]

/-- The two rounded complementary scales have product at most `Z`. -/
theorem taoExceptionalPrefixFloor_mul_sieveLevel_le
    (Z : ℕ) (hZ : 0 < Z) :
    taoExceptionalPrefixFloor Z * taoExceptionalSieveLevel Z ≤ Z := by
  have hZReal : 0 < (Z : ℝ) := by exact_mod_cast hZ
  have hmulReal :
      (taoExceptionalPrefixFloor Z : ℝ) *
          (taoExceptionalSieveLevel Z : ℝ) ≤ (Z : ℝ) := by
    calc
      (taoExceptionalPrefixFloor Z : ℝ) *
          (taoExceptionalSieveLevel Z : ℝ) ≤
          (Z : ℝ) ^ taoExceptionalPrefixExponent *
            (Z : ℝ) ^ taoExceptionalSieveLevelExponent :=
        mul_le_mul (taoExceptionalPrefixFloor_cast_le Z)
          (taoExceptionalSieveLevel_cast_le Z)
          (Nat.cast_nonneg _) (Real.rpow_nonneg hZReal.le _)
      _ = (Z : ℝ) ^
          (taoExceptionalPrefixExponent +
            taoExceptionalSieveLevelExponent) := by
        rw [Real.rpow_add hZReal]
      _ = (Z : ℝ) := by
        rw [taoExceptional_exponents_add, Real.rpow_one]
  exact_mod_cast hmulReal

theorem taoExceptionalPrefixFloor_le_sievePrefix
    {R Z d : ℕ} (hZ : 0 < Z)
    (hR : R ≤ taoExceptionalSieveLevel Z)
    (hdPos : 0 < d) (hdR : d ≤ R) :
    taoExceptionalPrefixFloor Z ≤ (2 * Z - 1) / d := by
  apply (Nat.le_div_iff_mul_le hdPos).2
  calc
    taoExceptionalPrefixFloor Z * d ≤
        taoExceptionalPrefixFloor Z * taoExceptionalSieveLevel Z :=
      Nat.mul_le_mul_left _ (hdR.trans hR)
    _ ≤ Z := taoExceptionalPrefixFloor_mul_sieveLevel_le Z hZ
    _ ≤ 2 * Z - 1 := by omega

/-- The canonical sieve level eventually lies strictly between `1` and `Z`. -/
theorem eventually_one_lt_taoExceptionalSieveLevel :
    ∀ᶠ Z : ℕ in atTop, 1 < taoExceptionalSieveLevel Z := by
  have hpow : Tendsto
      (fun Z : ℕ => (Z : ℝ) ^ taoExceptionalSieveLevelExponent)
      atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num [taoExceptionalSieveLevelExponent])).comp
        tendsto_natCast_atTop_atTop
  filter_upwards [hpow.eventually (eventually_gt_atTop (3 : ℝ))] with Z hZ
  have hfloor := Nat.lt_floor_add_one
    ((Z : ℝ) ^ taoExceptionalSieveLevelExponent)
  unfold taoExceptionalSieveLevel
  have htwo : 2 < Nat.floor
      ((Z : ℝ) ^ taoExceptionalSieveLevelExponent) := by
    exact_mod_cast (show (2 : ℝ) <
      Nat.floor ((Z : ℝ) ^ taoExceptionalSieveLevelExponent) by linarith)
  omega

theorem eventually_taoExceptionalSieveLevel_lt :
    ∀ᶠ Z : ℕ in atTop, taoExceptionalSieveLevel Z < Z := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Z hZ
  have hZReal : (1 : ℝ) < Z := by exact_mod_cast hZ
  have hpow : (Z : ℝ) ^ taoExceptionalSieveLevelExponent < (Z : ℝ) := by
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt hZReal
        (by norm_num [taoExceptionalSieveLevelExponent] :
          taoExceptionalSieveLevelExponent < (1 : ℝ))
  have hcast : (taoExceptionalSieveLevel Z : ℝ) < Z :=
    (taoExceptionalSieveLevel_cast_le Z).trans_lt hpow
  exact_mod_cast hcast

/-- Every divisor in the canonical sieve support produces a prefix beyond
any fixed Burgess cutoff, once `Z` is large. -/
theorem eventually_taoExceptional_sievePrefixes_large (H₀ : ℕ) :
    ∀ᶠ Z : ℕ in atTop,
      ∀ d ∈ (primorial (taoExceptionalSieveLevel Z)).divisors,
        (d : ℝ) ≤ taoExceptionalSieveLevel Z →
        H₀ ≤ (2 * Z - 1) / d := by
  have hprefix : Tendsto
      (fun Z : ℕ => (Z : ℝ) ^ taoExceptionalPrefixExponent)
      atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num [taoExceptionalPrefixExponent,
        taoExceptionalSieveLevelExponent])).comp
        tendsto_natCast_atTop_atTop
  filter_upwards [hprefix.eventually
      (eventually_gt_atTop ((H₀ : ℝ) + 1)),
    eventually_ge_atTop (1 : ℕ)] with Z hpow hZ d hd hdR
  have hfloor := Nat.lt_floor_add_one
    ((Z : ℝ) ^ taoExceptionalPrefixExponent)
  have hH₀Floor : H₀ ≤ taoExceptionalPrefixFloor Z := by
    have hreal : (H₀ : ℝ) + 1 <
        (taoExceptionalPrefixFloor Z : ℝ) + 1 := by
      exact hpow.trans (by
        simpa [taoExceptionalPrefixFloor] using hfloor)
    have hnat : H₀ < taoExceptionalPrefixFloor Z := by
      exact_mod_cast (show (H₀ : ℝ) <
        (taoExceptionalPrefixFloor Z : ℝ) by linarith)
    omega
  exact hH₀Floor.trans
    (taoExceptionalPrefixFloor_le_sievePrefix hZ
      le_rfl (Nat.pos_of_mem_divisors hd) (by exact_mod_cast hdR))

/-- The floor-rounded complementary scale is eventually large enough that
its `3.1` power contains the entire `Z^3.09` period envelope. -/
theorem eventually_taoExceptional_periodRange_prefixFloor :
    ∀ᶠ Z : ℕ in atTop,
      (Z : ℝ) ^ taoBurgessPeriodExponent ≤
        (taoExceptionalPrefixFloor Z : ℝ) ^ (31 / 10 : ℝ) := by
  let a : ℝ := taoBurgessPeriodExponent
  let b : ℝ := (31 / 10 : ℝ) * taoExceptionalPrefixExponent
  let K : ℝ := (1 / 2 : ℝ) ^ (31 / 10 : ℝ)
  have hab : a < b := by
    simpa [a, b, taoExceptionalPrefixExponent] using
      taoExceptionalPeriodExponent_lt_burgessRange
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hsmallNat :
      (fun Z : ℕ => (Z : ℝ) ^ a) =o[atTop]
        (fun Z : ℕ => (Z : ℝ) ^ b) :=
    (GafniTao.rpow_isLittleO_rpow hab).comp_tendsto
      tendsto_natCast_atTop_atTop
  have hbound := hsmallNat.bound hK
  have hprefix : Tendsto
      (fun Z : ℕ => (Z : ℝ) ^ taoExceptionalPrefixExponent)
      atTop atTop :=
    (tendsto_rpow_atTop
      (by norm_num [taoExceptionalPrefixExponent,
        taoExceptionalSieveLevelExponent])).comp
        tendsto_natCast_atTop_atTop
  filter_upwards [hbound,
    hprefix.eventually (eventually_ge_atTop (2 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with Z hZbound hpowTwo hZ
  have hZReal : 0 < (Z : ℝ) := by exact_mod_cast hZ
  have hfloor := Nat.lt_floor_add_one
    ((Z : ℝ) ^ taoExceptionalPrefixExponent)
  have hfloorLower :
      (1 / 2 : ℝ) * (Z : ℝ) ^ taoExceptionalPrefixExponent ≤
        (taoExceptionalPrefixFloor Z : ℝ) := by
    have hfloor' : (Z : ℝ) ^ taoExceptionalPrefixExponent <
        (taoExceptionalPrefixFloor Z : ℝ) + 1 := by
      simpa [taoExceptionalPrefixFloor] using hfloor
    nlinarith
  have hbound' : (Z : ℝ) ^ a ≤ K * (Z : ℝ) ^ b := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZReal.le a),
      abs_of_nonneg (Real.rpow_nonneg hZReal.le b)] using hZbound
  have hmono :
      ((1 / 2 : ℝ) * (Z : ℝ) ^ taoExceptionalPrefixExponent) ^
          (31 / 10 : ℝ) ≤
        (taoExceptionalPrefixFloor Z : ℝ) ^ (31 / 10 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hfloorLower (by norm_num)
  calc
    (Z : ℝ) ^ taoBurgessPeriodExponent = (Z : ℝ) ^ a := rfl
    _ ≤ K * (Z : ℝ) ^ b := hbound'
    _ = ((1 / 2 : ℝ) *
          (Z : ℝ) ^ taoExceptionalPrefixExponent) ^ (31 / 10 : ℝ) := by
      dsimp [K, b]
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hZReal.le _),
        ← Real.rpow_mul hZReal.le]
      congr 2
      ring
    _ ≤ (taoExceptionalPrefixFloor Z : ℝ) ^ (31 / 10 : ℝ) := hmono

/-- Hence every divisor in the canonical sieve support satisfies the exact
period-range side condition required by the explicit Burgess theorem. -/
theorem eventually_taoExceptional_sievePrefixes_periodRange :
    ∀ᶠ Z : ℕ in atTop,
      ∀ d ∈ (primorial (taoExceptionalSieveLevel Z)).divisors,
        (d : ℝ) ≤ taoExceptionalSieveLevel Z →
        (Z : ℝ) ^ taoBurgessPeriodExponent ≤
          (((2 * Z - 1) / d : ℕ) : ℝ) ^ (31 / 10 : ℝ) := by
  filter_upwards [eventually_taoExceptional_periodRange_prefixFloor,
    eventually_ge_atTop (1 : ℕ)] with Z hrange hZ d hd hdR
  refine hrange.trans ?_
  apply Real.rpow_le_rpow
  · exact_mod_cast Nat.zero_le (taoExceptionalPrefixFloor Z)
  · exact_mod_cast taoExceptionalPrefixFloor_le_sievePrefix hZ le_rfl
      (Nat.pos_of_mem_divisors hd) (by exact_mod_cast hdR)
  · norm_num

/-- Bertrand's postulate makes every sufficiently large half-open dyadic
prime band nonempty. -/
theorem eventually_taoDyadicPrimeBand_nonempty :
    ∀ᶠ Z : ℕ in atTop, (taoDyadicPrimeBand Z).Nonempty := by
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with Z hZ
  obtain ⟨p, hpPrime, hZp, hpTwo⟩ :=
    Nat.exists_prime_lt_and_le_two_mul Z (by omega)
  refine ⟨p, mem_taoDyadicPrimeBand.mpr ⟨hpPrime, hZp.le, ?_⟩⟩
  by_contra hnot
  have hpEq : p = 2 * Z := by omega
  have hpDvd : p ∣ 2 * Z := hpEq ▸ dvd_rfl
  rcases hpPrime.dvd_mul.mp hpDvd with hpTwo | hpZ
  · have : p ≤ 2 := Nat.le_of_dvd (by omega) hpTwo
    omega
  · have : p ≤ Z := Nat.le_of_dvd (by omega) hpZ
    omega

/-- With the canonical source sieve level, a source-shaped explicit Burgess
theorem supplies the full finite Selberg/BHM estimate eventually; no further
prefix-size or conductor-range assumptions remain. -/
theorem eventually_sum_finiteNormalizedPrimeBandSum_sq_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q₁ : ℕ → ℕ)
    (W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z))
    (hq₁ : ∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z))
    (hsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (W Z)) :
    ∀ᶠ Z : ℕ in atTop,
      ∑ a ∈ W Z,
          ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤
        ((((2 * Z : ℕ) : ℝ) *
              (2 / Real.log (taoExceptionalSieveLevel Z)) +
            (taoExceptionalSieveLevel Z : ℝ) *
              (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) +
          ((((W Z).card - 1 : ℕ) : ℝ) *
            (((taoExceptionalSieveLevel Z : ℝ) *
                (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
              (C * (2 * Z : ℝ) ^
                (1 - taoBurgessSavingExponent))))) /
          (taoDyadicPrimeBand Z).card := by
  filter_upwards [eventually_one_lt_taoExceptionalSieveLevel,
    eventually_taoExceptionalSieveLevel_lt,
    eventually_taoExceptional_sievePrefixes_large H₀,
    eventually_taoExceptional_sievePrefixes_periodRange,
    hq₁, eventually_taoDyadicPrimeBand_nonempty, hsep] with
      Z hR hRZ hlarge hrange hq₁Z hbandZ hsepZ
  exact
    sum_finiteNormalizedPrimeBandSum_sq_le_exceptionalFamily_of_explicitBurgess
      hC hR hRZ hq₁Z (W Z) hbandZ hsepZ hburgess hlarge hrange

end

end Tao2026
