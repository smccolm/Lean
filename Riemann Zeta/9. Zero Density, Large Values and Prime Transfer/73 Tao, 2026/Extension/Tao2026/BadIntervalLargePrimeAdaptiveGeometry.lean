import Tao2026.BadIntervalLargePrimeAdaptiveSource

/-!
# Automatic conductor geometry for adaptive large-prime blocks

The source dyadic range has upper endpoint `z^(1+o(1))`.  We record a fixed
`z^1.01` margin and prove that the common ambient interval from `R` through
`2S` lies in every Burgess conductor range.  The same calculation supplies
the stronger square-root cofactor range needed for mixed exceptional pairs.
-/

namespace Tao2026

open Filter Topology
open scoped Classical

noncomputable section

set_option maxRecDepth 10000

/-- A source large-prime selector with the fixed upper margin used for the
literal Burgess conductor geometry. -/
structure TaoLargePrimeDyadicBandSelector (R : ℕ → ℕ) : Prop
    extends TaoLargePrimeSourceBandSelector R where
  upper_source : ∀ᶠ x : ℕ in atTop,
    (R x : ℝ) ≤ (taoZ x) ^ (101 / 100 : ℝ)

/-- A fixed positive power of `z` eventually absorbs any fixed constant. -/
private theorem eventually_const_mul_taoZ_rpow_le_rpow
    {c α β : ℝ} (hαβ : α < β) :
    ∀ᶠ x : ℕ in atTop,
      c * (taoZ x) ^ α ≤ (taoZ x) ^ β := by
  have hpow : Tendsto (fun z : ℝ => z ^ (β - α)) atTop atTop :=
    tendsto_rpow_atTop (sub_pos.mpr hαβ)
  filter_upwards [
    (hpow.comp tendsto_taoZ_atTop).eventually (eventually_ge_atTop c)] with
      x hx
  calc
    c * (taoZ x) ^ α ≤
        (taoZ x) ^ (β - α) * (taoZ x) ^ α :=
      mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg (taoZ_pos x).le _)
    _ = (taoZ x) ^ β := by
      rw [← Real.rpow_add (taoZ_pos x)]
      congr 1
      ring

private theorem taoLargePrimeDyadicBand_subset_commonRange
    {R S p : ℕ} (hRS : R ≤ S) (hp : p ∈ taoDyadicPrimeBand R) :
    p ∈ taoLargeAntiSievePrimeRange (R - 1) (2 * S - 1) := by
  rw [mem_taoLargeAntiSievePrimeRange]
  have hpData := mem_taoDyadicPrimeBand.mp hp
  exact ⟨hpData.1, by omega, by omega⟩

private theorem taoLargePrimeUpperDyadicBand_subset_commonRange
    {R S q : ℕ} (hRS : R ≤ S) (hq : q ∈ taoDyadicPrimeBand S) :
    q ∈ taoLargeAntiSievePrimeRange (R - 1) (2 * S - 1) := by
  rw [mem_taoLargeAntiSievePrimeRange]
  have hqData := mem_taoDyadicPrimeBand.mp hq
  exact ⟨hqData.1, by omega, by omega⟩

/-- For ordered source dyadic bands, the interval `(R-1,2S-1]` is an
admissible Burgess conductor set at every tuple scale, contains both bands,
and has the square-root cofactor room required after fixing a prime in the
lower band. -/
theorem eventually_taoLargePrimeAdaptive_commonRange_geometry
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeDyadicBandSelector R)
    (hS : TaoLargePrimeDyadicBandSelector S)
    (hRS : ∀ᶠ x : ℕ in atTop, R x ≤ S x) :
    ∀ᶠ x : ℕ in atTop,
      (∀ j : Fin 1001,
        IsAdmissibleTaoExceptionalConductorSet
          (taoLargeAntiSievePrimeRange (R x - 1) (2 * S x - 1))
          (P x j)) ∧
      taoDyadicPrimeBand (R x) ⊆
        taoLargeAntiSievePrimeRange (R x - 1) (2 * S x - 1) ∧
      taoDyadicPrimeBand (S x) ⊆
        taoLargeAntiSievePrimeRange (R x - 1) (2 * S x - 1) ∧
      (∀ p ∈ taoDyadicPrimeBand (R x), ∀ j : Fin 1001,
        (2 * S x - 1 : ℕ) ≤
          Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent / (p : ℝ))) := by
  have hP := eventually_taoPrimeTupleSourceScale_lower_rpow hscale
    (β := (999 / 1000 : ℝ)) (by norm_num)
  have hfour : ∀ᶠ x : ℕ in atTop,
      4 * (taoZ x) ^ (202 / 100 : ℝ) ≤
        (taoZ x) ^ (41 / 20 : ℝ) :=
    eventually_const_mul_taoZ_rpow_le_rpow (by norm_num)
  have height : ∀ᶠ x : ℕ in atTop,
      8 * (taoZ x) ^ (303 / 100 : ℝ) ≤
        (taoZ x) ^ (153 / 50 : ℝ) :=
    eventually_const_mul_taoZ_rpow_le_rpow (by norm_num)
  filter_upwards [hP, hR.eventually_two_le, hS.upper_source, hRS, hfour, height,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hPX hRtwo hSupper hRSX hfourX heightX hz
  have hzpos : 0 < taoZ x := taoZ_pos x
  have htwoS : (0 : ℝ) ≤ 2 * (S x : ℝ) := by
    exact_mod_cast (show 0 ≤ 2 * S x by omega)
  have hupper : ((2 * S x - 1 : ℕ) : ℝ) ≤ 2 * (S x : ℝ) := by
    exact_mod_cast Nat.sub_le (2 * S x) 1
  have hScube : (S x : ℝ) ^ (3 : ℕ) ≤
      ((taoZ x) ^ (101 / 100 : ℝ)) ^ (3 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hSupper 3
  have hSsq : (S x : ℝ) ^ (2 : ℕ) ≤
      ((taoZ x) ^ (101 / 100 : ℝ)) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hSupper 2
  have hPpower : ∀ j : Fin 1001,
      (taoZ x) ^ (308691 / 100000 : ℝ) ≤
        (P x j : ℝ) ^ taoBurgessPeriodExponent := by
    intro j
    calc
      (taoZ x) ^ (308691 / 100000 : ℝ) =
          ((taoZ x) ^ (999 / 1000 : ℝ)) ^
            taoBurgessPeriodExponent := by
        rw [← Real.rpow_mul hzpos.le]
        congr 1
        norm_num [taoBurgessPeriodExponent]
      _ ≤ (P x j : ℝ) ^ taoBurgessPeriodExponent :=
        Real.rpow_le_rpow (Real.rpow_nonneg hzpos.le _) (hPX j)
          (by norm_num [taoBurgessPeriodExponent])
  have hEndpoint : ∀ j : Fin 1001,
      ((2 * S x - 1 : ℕ) : ℝ) ≤
        Real.sqrt ((P x j : ℝ) ^ taoBurgessPeriodExponent) := by
    intro j
    apply (Real.le_sqrt (by positivity) (Real.rpow_nonneg (by positivity) _)).2
    calc
      ((2 * S x - 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤
          (2 * (S x : ℝ)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (by positivity) hupper 2
      _ = 4 * (S x : ℝ) ^ (2 : ℕ) := by ring
      _ ≤ 4 * (((taoZ x) ^ (101 / 100 : ℝ)) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hSsq (by norm_num)
      _ = 4 * (taoZ x) ^ (202 / 100 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
        norm_num
      _ ≤ (taoZ x) ^ (41 / 20 : ℝ) := hfourX
      _ ≤ (taoZ x) ^ (308691 / 100000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
      _ ≤ (P x j : ℝ) ^ taoBurgessPeriodExponent := hPpower j
  refine ⟨fun j => isAdmissible_taoLargeAntiSievePrimeRange (hEndpoint j),
    ?_, ?_, ?_⟩
  · intro p hp
    exact taoLargePrimeDyadicBand_subset_commonRange hRSX hp
  · intro q hq
    exact taoLargePrimeUpperDyadicBand_subset_commonRange hRSX hq
  · intro p hp j
    have hpData := mem_taoDyadicPrimeBand.mp hp
    have hpPos : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
    have hpUpper : (p : ℝ) ≤ 2 * (S x : ℝ) := by
      exact_mod_cast (hpData.2.2.le.trans (Nat.mul_le_mul_left 2 hRSX))
    apply (Real.le_sqrt (by positivity)
      (div_nonneg (Real.rpow_nonneg (by positivity) _) hpPos.le)).2
    apply (le_div_iff₀ hpPos).2
    calc
      ((2 * S x - 1 : ℕ) : ℝ) ^ (2 : ℕ) * (p : ℝ) ≤
          (2 * (S x : ℝ)) ^ (2 : ℕ) * (2 * (S x : ℝ)) :=
        mul_le_mul
          (pow_le_pow_left₀ (by positivity) hupper 2) hpUpper hpPos.le
          (sq_nonneg _)
      _ = 8 * (S x : ℝ) ^ (3 : ℕ) := by ring
      _ ≤ 8 * (((taoZ x) ^ (101 / 100 : ℝ)) ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_left hScube (by norm_num)
      _ = 8 * (taoZ x) ^ (303 / 100 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
        norm_num
      _ ≤ (taoZ x) ^ (153 / 50 : ℝ) := heightX
      _ ≤ (taoZ x) ^ (308691 / 100000 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
      _ ≤ (P x j : ℝ) ^ taoBurgessPeriodExponent := hPpower j

/-! ## Uniform crude bounds on complete dyadic bands -/

/-- The crude one-prime estimate holds simultaneously for every shift and
every prime in a source dyadic band.  In particular, no selector sequence for
the individual prime is needed. -/
theorem eventually_taoLargePrimeProbability_le_crude_dyadicBand
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R : ℕ → ℕ} (hR : TaoLargePrimeDyadicBandSelector R)
    (m' : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ a : ℕ × ℕ, a.2 ∈ taoDyadicPrimeBand (R x) → ¬a.2 ∣ a.1 →
        taoLargePrimeProbability (P x) hP (m' x) a ≤
          256 * Real.log (taoZ x) ^ 2 / (R x : ℝ) := by
  filter_upwards [eventually_taoPrimeTupleSourceScale_band_normalization hscale,
    eventually_taoPrimeTupleSourceScale_lower_nine_tenths hscale,
    hR.upper_source, hR.eventually_two_le,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hband hPlower hRupper hRtwo hz
  intro hP a ha hpa
  have haData := mem_taoDyadicPrimeBand.mp ha
  have hzpos : 0 < taoZ x := taoZ_pos x
  have hzpow : (taoZ x) ^ (101 / 100 : ℝ) ≤
      (taoZ x) ^ (9 / 5 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
  have hprodLower :
      (taoZ x) ^ (9 / 10 : ℝ) * (taoZ x) ^ (9 / 10 : ℝ) ≤
        (P x (1 : Fin 1001) : ℝ) * (P x (2 : Fin 1001) : ℝ) :=
    mul_le_mul (hPlower 1) (hPlower 2) (Real.rpow_nonneg hzpos.le _)
      (by positivity)
  have hqUreal : (a.2 : ℝ) ≤
      (((2 * P x (1 : Fin 1001)) * (2 * P x (2 : Fin 1001)) : ℕ) : ℝ) := by
    calc
      (a.2 : ℝ) ≤ 2 * (R x : ℝ) := by
        exact_mod_cast haData.2.2.le
      _ ≤ 2 * (taoZ x) ^ (101 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hRupper (by norm_num)
      _ ≤ 4 * (taoZ x) ^ (9 / 5 : ℝ) := by
        nlinarith [Real.rpow_nonneg hzpos.le (9 / 5 : ℝ)]
      _ = 4 * ((taoZ x) ^ (9 / 10 : ℝ) *
          (taoZ x) ^ (9 / 10 : ℝ)) := by
        rw [← Real.rpow_add hzpos]
        norm_num
      _ ≤ 4 * ((P x (1 : Fin 1001) : ℝ) *
          (P x (2 : Fin 1001) : ℝ)) :=
        mul_le_mul_of_nonneg_left hprodLower (by norm_num)
      _ = (((2 * P x (1 : Fin 1001)) *
          (2 * P x (2 : Fin 1001)) : ℕ) : ℝ) := by
        push_cast
        ring
  have hqU : a.2 ≤
      (2 * P x (1 : Fin 1001)) * (2 * P x (2 : Fin 1001)) := by
    exact_mod_cast hqUreal
  have hraw := taoLargePrimeProbability_le_crude_logScale_pair
    (P x) hP (m' x) a (1 : Fin 1001) (2 : Fin 1001)
      (by decide) (by decide) (by decide) haData.1 hpa
      (4 * Real.log (taoZ x))
      (mul_nonneg (by norm_num) (Real.log_nonneg hz))
      (hband 1) (hband 2) hqU
  have hraw' : taoLargePrimeProbability (P x) hP (m' x) a ≤
      256 * Real.log (taoZ x) ^ 2 / (a.2 : ℝ) := by
    convert hraw using 1
    ring
  calc
    taoLargePrimeProbability (P x) hP (m' x) a ≤
        256 * Real.log (taoZ x) ^ 2 / (a.2 : ℝ) := hraw'
    _ ≤ 256 * Real.log (taoZ x) ^ 2 / (R x : ℝ) := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (sq_nonneg _))
      · exact_mod_cast (show 0 < R x by omega)
      · exact_mod_cast haData.2.1

/-- The crude joint estimate holds simultaneously for every ordered pair of
distinct primes in two source dyadic bands. -/
theorem eventually_taoLargePrimeJointProbability_le_crude_twoBand
    {P : ℕ → Fin 1001 → ℕ} (hscale : TaoPrimeTupleSourceScaleFamily P)
    {R S : ℕ → ℕ} (hR : TaoLargePrimeDyadicBandSelector R)
    (hS : TaoLargePrimeDyadicBandSelector S) (m' : ℕ → ℕ) :
    ∀ᶠ x : ℕ in atTop,
      ∀ hP : ∀ j, (taoDyadicPrimeBand (P x j)).Nonempty,
      ∀ a b : ℕ × ℕ,
        a.2 ∈ taoDyadicPrimeBand (R x) →
        b.2 ∈ taoDyadicPrimeBand (S x) → a.2 ≠ b.2 →
        ¬a.2 ∣ a.1 → ¬b.2 ∣ b.1 →
        taoLargePrimeJointProbability (P x) hP (m' x) a b ≤
          6144 * Real.log (taoZ x) ^ 3 /
            ((R x : ℝ) * (S x : ℝ)) := by
  filter_upwards [eventually_taoPrimeTupleSourceScale_band_normalization hscale,
    eventually_taoPrimeTupleSourceScale_lower_nine_tenths hscale,
    hR.upper_source, hS.upper_source, hR.eventually_two_le,
    hS.eventually_two_le,
    tendsto_taoZ_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with
      x hband hPlower hRupper hSupper hRtwo hStwo hz
  intro hP a b ha hb hab hpa hpb
  have haData := mem_taoDyadicPrimeBand.mp ha
  have hbData := mem_taoDyadicPrimeBand.mp hb
  have hzpos : 0 < taoZ x := taoZ_pos x
  have hzpow : (taoZ x) ^ (202 / 100 : ℝ) ≤
      (taoZ x) ^ (27 / 10 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hz (by norm_num)
  have hpairUpper : (R x : ℝ) * (S x : ℝ) ≤
      (taoZ x) ^ (101 / 100 : ℝ) *
        (taoZ x) ^ (101 / 100 : ℝ) :=
    mul_le_mul hRupper hSupper (by positivity) (by positivity)
  have htripleLower :
      (taoZ x) ^ (9 / 10 : ℝ) * (taoZ x) ^ (9 / 10 : ℝ) *
          (taoZ x) ^ (9 / 10 : ℝ) ≤
        (P x (1 : Fin 1001) : ℝ) * (P x (2 : Fin 1001) : ℝ) *
          (P x (3 : Fin 1001) : ℝ) := by
    have hp12 := mul_le_mul (hPlower 1) (hPlower 2)
      (Real.rpow_nonneg hzpos.le _) (by positivity)
    exact mul_le_mul hp12 (hPlower 3) (Real.rpow_nonneg (by positivity) _)
      (by positivity)
  have hqUreal : ((a.2 * b.2 : ℕ) : ℝ) ≤
      (((2 * P x (1 : Fin 1001)) * (2 * P x (2 : Fin 1001))) *
        (2 * P x (3 : Fin 1001)) : ℕ) := by
    have haUpper : (a.2 : ℝ) ≤ 2 * (R x : ℝ) := by
      exact_mod_cast haData.2.2.le
    have hbUpper : (b.2 : ℝ) ≤ 2 * (S x : ℝ) := by
      exact_mod_cast hbData.2.2.le
    calc
      ((a.2 * b.2 : ℕ) : ℝ) ≤
          (2 * (R x : ℝ)) * (2 * (S x : ℝ)) := by
        push_cast
        exact mul_le_mul haUpper hbUpper (by positivity)
          (by positivity)
      _ = 4 * ((R x : ℝ) * (S x : ℝ)) := by ring
      _ ≤ 4 * ((taoZ x) ^ (101 / 100 : ℝ) *
          (taoZ x) ^ (101 / 100 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpairUpper (by norm_num)
      _ = 4 * (taoZ x) ^ (202 / 100 : ℝ) := by
        rw [← Real.rpow_add hzpos]
        norm_num
      _ ≤ 8 * (taoZ x) ^ (27 / 10 : ℝ) := by
        nlinarith [Real.rpow_nonneg hzpos.le (27 / 10 : ℝ)]
      _ = 8 * ((taoZ x) ^ (9 / 10 : ℝ) *
          (taoZ x) ^ (9 / 10 : ℝ) *
          (taoZ x) ^ (9 / 10 : ℝ)) := by
        rw [← Real.rpow_add hzpos, ← Real.rpow_add hzpos]
        norm_num
      _ ≤ 8 * ((P x (1 : Fin 1001) : ℝ) *
          (P x (2 : Fin 1001) : ℝ) *
          (P x (3 : Fin 1001) : ℝ)) :=
        mul_le_mul_of_nonneg_left htripleLower (by norm_num)
      _ = (((2 * P x (1 : Fin 1001)) * (2 * P x (2 : Fin 1001))) *
          (2 * P x (3 : Fin 1001)) : ℕ) := by
        push_cast
        ring
  have hqU : a.2 * b.2 ≤
      ((2 * P x (1 : Fin 1001)) * (2 * P x (2 : Fin 1001))) *
        (2 * P x (3 : Fin 1001)) := by
    exact_mod_cast hqUreal
  have hraw := taoLargePrimeJointProbability_le_crude_logScale_triple
    (P x) hP (m' x) a b (1 : Fin 1001) (2 : Fin 1001) (3 : Fin 1001)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      haData.1 hbData.1 hab hpa hpb
      (4 * Real.log (taoZ x))
      (mul_nonneg (by norm_num) (Real.log_nonneg hz))
      (hband 1) (hband 2) (hband 3) hqU
  have hraw' : taoLargePrimeJointProbability (P x) hP (m' x) a b ≤
      6144 * Real.log (taoZ x) ^ 3 /
        ((a.2 : ℝ) * (b.2 : ℝ)) := by
    convert hraw using 1
    ring
  calc
    taoLargePrimeJointProbability (P x) hP (m' x) a b ≤
        6144 * Real.log (taoZ x) ^ 3 /
          ((a.2 : ℝ) * (b.2 : ℝ)) := hraw'
    _ ≤ 6144 * Real.log (taoZ x) ^ 3 /
          ((R x : ℝ) * (S x : ℝ)) := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg (by norm_num) (pow_nonneg (Real.log_nonneg hz) 3))
      · positivity
      · have haLower : (R x : ℝ) ≤ (a.2 : ℝ) := by
          exact_mod_cast haData.2.1
        have hbLower : (S x : ℝ) ≤ (b.2 : ℝ) := by
          exact_mod_cast hbData.2.1
        exact mul_le_mul haLower hbLower (by positivity) (by positivity)

end

end Tao2026
