import Tao2026.ExceptionalCharacterNormalization
import PrimeNumberTheoremAnd.BrunTitchmarsh

/-!
# Asymptotic absorption for the exceptional-character BHM estimate

This module performs the non-Burgess asymptotic work in Tao's Lemma 5.1.  It
controls both Selberg diagonal terms, combines the family exponent `2/125`
with the sieve level and Burgess saving to obtain the strict exponent
`1-1/5000`, normalizes by the exact dyadic-prime cardinality, and proves Tao's
self-improving truncation argument.  Conditional only on the explicit Burgess
input, the final theorem gives both `#W ≪ Z^(2/125)` and a bounded exceptional
second moment, with no preliminary cardinality hypothesis.
-/

namespace Tao2026

open Filter Asymptotics

theorem taoExceptionalSelbergFloorError_isBigO :
    (fun Z : ℕ =>
      (taoExceptionalSieveLevel Z : ℝ) *
        (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) =O[atTop]
      (fun Z : ℕ => (Z : ℝ) / Real.log Z) := by
  have hmodel :=
    (BrunTitchmarsh.rpow_mul_rpow_log_isBigO_id_div_log
      (r := taoExceptionalSieveLevelExponent) 3
      (by norm_num [taoExceptionalSieveLevelExponent])).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (IsBigO.of_bound 8 ?_).trans hmodel
  filter_upwards [eventually_one_lt_taoExceptionalSieveLevel,
    eventually_taoExceptionalSieveLevel_lt,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with Z hR hRZ hlogZ
  have hRpos : (0 : ℝ) < taoExceptionalSieveLevel Z := by positivity
  have hZpos : (0 : ℝ) < Z := by
    exact_mod_cast (show 0 < Z by omega)
  change 1 ≤ Real.log (Z : ℝ) at hlogZ
  have hlogRpos : 0 < Real.log (taoExceptionalSieveLevel Z) :=
    Real.log_pos (by exact_mod_cast hR)
  have hlogRle : Real.log (taoExceptionalSieveLevel Z) ≤ Real.log Z :=
    Real.log_le_log hRpos (by exact_mod_cast hRZ.le)
  have hOneLog : 1 + Real.log (taoExceptionalSieveLevel Z) ≤ 2 * Real.log Z := by
    linarith
  have hfnonneg : 0 ≤ (taoExceptionalSieveLevel Z : ℝ) *
      (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3 := by positivity
  have hgnonneg : 0 ≤ (Z : ℝ) ^ taoExceptionalSieveLevelExponent *
      Real.log Z ^ (3 : ℝ) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hfnonneg, Real.norm_eq_abs]
  change (taoExceptionalSieveLevel Z : ℝ) *
      (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3 ≤
    8 * |(Z : ℝ) ^ taoExceptionalSieveLevelExponent * Real.log Z ^ (3 : ℝ)|
  rw [abs_of_nonneg hgnonneg]
  calc
    (taoExceptionalSieveLevel Z : ℝ) *
        (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3 ≤
      (Z : ℝ) ^ taoExceptionalSieveLevelExponent *
        (2 * Real.log Z) ^ 3 := by
          gcongr
          exact taoExceptionalSieveLevel_cast_le Z
    _ = 8 * ((Z : ℝ) ^ taoExceptionalSieveLevelExponent *
        Real.log Z ^ (3 : ℝ)) := by
          have hthree : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
          rw [hthree, Real.rpow_natCast]
          ring

theorem eventually_half_sieveExponent_mul_log_le_log_sieveLevel :
    ∀ᶠ Z : ℕ in atTop,
      (taoExceptionalSieveLevelExponent / 2) * Real.log Z ≤
        Real.log (taoExceptionalSieveLevel Z) := by
  have hePos : 0 < taoExceptionalSieveLevelExponent := by
    norm_num [taoExceptionalSieveLevelExponent]
  have hlogLarge :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop
        (2 * Real.log 2 / taoExceptionalSieveLevelExponent))
  filter_upwards [hlogLarge, eventually_ge_atTop (1 : ℕ)] with Z hlarge hZ
  change 2 * Real.log 2 / taoExceptionalSieveLevelExponent ≤
    Real.log (Z : ℝ) at hlarge
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hxpos : 0 < (Z : ℝ) ^ taoExceptionalSieveLevelExponent :=
    Real.rpow_pos_of_pos hZpos _
  have hxOne : 1 ≤ (Z : ℝ) ^ taoExceptionalSieveLevelExponent :=
    Real.one_le_rpow (by exact_mod_cast hZ) hePos.le
  have hfloor := Nat.div_two_lt_floor hxOne
  change (Z : ℝ) ^ taoExceptionalSieveLevelExponent / 2 <
    (taoExceptionalSieveLevel Z : ℝ) at hfloor
  have hlogFloor :
      Real.log ((Z : ℝ) ^ taoExceptionalSieveLevelExponent / 2) ≤
        Real.log (taoExceptionalSieveLevel Z) :=
    (Real.strictMonoOn_log.monotoneOn (div_pos hxpos (by norm_num))
      ((div_pos hxpos (by norm_num)).trans hfloor) hfloor.le)
  rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_rpow hZpos] at hlogFloor
  have hsmall : Real.log 2 ≤
      (taoExceptionalSieveLevelExponent / 2) * Real.log Z := by
    calc
      Real.log 2 = (taoExceptionalSieveLevelExponent / 2) *
          (2 * Real.log 2 / taoExceptionalSieveLevelExponent) := by field_simp
      _ ≤ (taoExceptionalSieveLevelExponent / 2) * Real.log Z := by gcongr
  linarith

theorem taoExceptionalSelbergMain_isBigO :
    (fun Z : ℕ => ((2 * Z : ℕ) : ℝ) *
      (2 / Real.log (taoExceptionalSieveLevel Z))) =O[atTop]
      (fun Z : ℕ => (Z : ℝ) / Real.log Z) := by
  apply IsBigO.of_bound 80000
  filter_upwards [eventually_half_sieveExponent_mul_log_le_log_sieveLevel,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with Z hlogR hlogZ
  change 1 ≤ Real.log (Z : ℝ) at hlogZ
  have hZnonneg : (0 : ℝ) ≤ Z := by positivity
  have hlogZpos : 0 < Real.log (Z : ℝ) := lt_of_lt_of_le zero_lt_one hlogZ
  have heHalfPos : 0 < taoExceptionalSieveLevelExponent / 2 := by
    norm_num [taoExceptionalSieveLevelExponent]
  have hlogRpos : 0 < Real.log (taoExceptionalSieveLevel Z) :=
    (mul_pos heHalfPos hlogZpos).trans_le hlogR
  have hfnonneg : 0 ≤ ((2 * Z : ℕ) : ℝ) *
      (2 / Real.log (taoExceptionalSieveLevel Z)) := by positivity
  have hgnonneg : 0 ≤ (Z : ℝ) / Real.log Z := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hfnonneg, Real.norm_eq_abs,
    abs_of_nonneg hgnonneg]
  calc
    ((2 * Z : ℕ) : ℝ) *
        (2 / Real.log (taoExceptionalSieveLevel Z)) =
      (4 * (Z : ℝ)) / Real.log (taoExceptionalSieveLevel Z) := by
        norm_num
        ring
    _ ≤ (80000 * (Z : ℝ)) / Real.log Z := by
      apply (div_le_div_iff₀ hlogRpos hlogZpos).2
      have hscaled := mul_le_mul_of_nonneg_left hlogR
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 80000) hZnonneg)
      calc
        4 * (Z : ℝ) * Real.log Z =
            (80000 * (Z : ℝ)) *
              ((taoExceptionalSieveLevelExponent / 2) * Real.log Z) := by
                norm_num [taoExceptionalSieveLevelExponent]
                ring
        _ ≤ (80000 * (Z : ℝ)) *
              Real.log (taoExceptionalSieveLevel Z) := hscaled
    _ = 80000 * ((Z : ℝ) / Real.log Z) := by ring

theorem eventually_taoExceptionalSelbergFloorError_le :
    ∀ᶠ Z : ℕ in atTop,
      (taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3 ≤
        8 * ((Z : ℝ) ^ taoExceptionalSieveLevelExponent *
          Real.log Z ^ (3 : ℕ)) := by
  filter_upwards [eventually_one_lt_taoExceptionalSieveLevel,
    eventually_taoExceptionalSieveLevel_lt,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with Z hR hRZ hlogZ
  change 1 ≤ Real.log (Z : ℝ) at hlogZ
  have hRpos : (0 : ℝ) < taoExceptionalSieveLevel Z := by positivity
  have hlogRle : Real.log (taoExceptionalSieveLevel Z) ≤ Real.log Z :=
    Real.log_le_log hRpos (by exact_mod_cast hRZ.le)
  have hOneLog : 1 + Real.log (taoExceptionalSieveLevel Z) ≤ 2 * Real.log Z := by
    linarith
  calc
    (taoExceptionalSieveLevel Z : ℝ) *
        (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3 ≤
      (Z : ℝ) ^ taoExceptionalSieveLevelExponent *
        (2 * Real.log Z) ^ 3 := by
          gcongr
          exact taoExceptionalSieveLevel_cast_le Z
    _ = 8 * ((Z : ℝ) ^ taoExceptionalSieveLevelExponent *
        Real.log Z ^ (3 : ℕ)) := by ring

/-- A strict power saving absorbs every fixed logarithmic power even after
normalization by the prime scale `x / log x`. -/
theorem rpow_mul_rpow_log_isLittleO_id_div_log (k : ℝ) {r : ℝ} (hr : r < 1) :
    (fun x : ℝ => x ^ r * Real.log x ^ k) =o[atTop]
      (fun x : ℝ => x / Real.log x) := by
  let d : ℝ := (1 - r) / 2
  have hd : 0 < d := by dsimp [d]; linarith
  have hlogk : (fun x : ℝ => Real.log x ^ k) =o[atTop]
      (fun x : ℝ => x ^ d) :=
    isLittleO_log_rpow_rpow_atTop k hd
  have hfirst : (fun x : ℝ => x ^ r * Real.log x ^ k) =o[atTop]
      (fun x : ℝ => x ^ r * x ^ d) :=
    (isBigO_refl (fun x : ℝ => x ^ r) atTop).mul_isLittleO hlogk
  have hlog : Real.log =o[atTop] (fun x : ℝ => x ^ d) :=
    isLittleO_log_rpow_atTop hd
  have hzero : ∀ᶠ x : ℝ in atTop, Real.log x = 0 → x ^ d = 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx hlogZero
    exact False.elim ((Real.log_pos hx).ne' hlogZero)
  have hinv : (fun x : ℝ => (x ^ d)⁻¹) =o[atTop]
      (fun x : ℝ => (Real.log x)⁻¹) := hlog.inv_rev hzero
  have hsecond : (fun x : ℝ => x * (x ^ d)⁻¹) =o[atTop]
      (fun x : ℝ => x * (Real.log x)⁻¹) :=
    (isBigO_refl (fun x : ℝ => x) atTop).mul_isLittleO hinv
  calc
    (fun x : ℝ => x ^ r * Real.log x ^ k) =o[atTop]
        (fun x : ℝ => x ^ r * x ^ d) := hfirst
    _ =ᶠ[atTop] (fun x : ℝ => x * (x ^ d)⁻¹) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      calc
        x ^ r * x ^ d = x ^ (r + d) := (Real.rpow_add hx r d).symm
        _ = x ^ (1 - d) := by
          congr 1
          dsimp [d]
          ring
        _ = x ^ (1 : ℝ) * x ^ (-d) := Real.rpow_add hx 1 (-d)
        _ = x * (x ^ d)⁻¹ := by rw [Real.rpow_one, Real.rpow_neg hx.le]
    _ =o[atTop] (fun x : ℝ => x * (Real.log x)⁻¹) := hsecond
    _ =ᶠ[atTop] (fun x : ℝ => x / Real.log x) := by
      filter_upwards [] with x
      rw [div_eq_mul_inv]

theorem taoExceptionalOffDiagonalEnvelope_isBigO :
    (fun Z : ℕ =>
      (Z : ℝ) ^ (2 / 125 : ℝ) *
        ((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent)) =O[atTop]
      (fun Z : ℕ => (Z : ℝ) / Real.log Z) := by
  let r : ℝ := 1 - (1 / 5000 : ℝ)
  let c : ℝ := 8 * (2 : ℝ) ^ (1 - taoBurgessSavingExponent)
  have hr : r < 1 := by norm_num [r]
  have hmodel :=
    (BrunTitchmarsh.rpow_mul_rpow_log_isBigO_id_div_log
      (r := r) 3 hr).comp_tendsto
        (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (IsBigO.of_bound c ?_).trans hmodel
  filter_upwards [eventually_taoExceptionalSelbergFloorError_le,
    eventually_ge_atTop (1 : ℕ)] with Z hfloor hZ
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hlogNonneg : 0 ≤ Real.log (Z : ℝ) := Real.log_nonneg (by exact_mod_cast hZ)
  have hleftNonneg : 0 ≤
      (Z : ℝ) ^ (2 / 125 : ℝ) *
        ((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent) := by positivity
  have hmodelNonneg : 0 ≤ (Z : ℝ) ^ r * Real.log Z ^ (3 : ℝ) := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleftNonneg, Real.norm_eq_abs]
  change _ ≤ c * |(Z : ℝ) ^ r * Real.log Z ^ (3 : ℝ)|
  rw [abs_of_nonneg hmodelNonneg]
  calc
    (Z : ℝ) ^ (2 / 125 : ℝ) *
          ((taoExceptionalSieveLevel Z : ℝ) *
            (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
          (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent) ≤
        (Z : ℝ) ^ (2 / 125 : ℝ) *
          (8 * ((Z : ℝ) ^ taoExceptionalSieveLevelExponent *
            Real.log Z ^ (3 : ℕ))) *
          (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent) := by gcongr
    _ = c * ((Z : ℝ) ^ r * Real.log Z ^ (3 : ℝ)) := by
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      have hZnonneg : (0 : ℝ) ≤ Z := hZpos.le
      rw [Real.mul_rpow htwo hZnonneg]
      have hexp : (2 / 125 : ℝ) + taoExceptionalSieveLevelExponent +
          (1 - taoBurgessSavingExponent) = r := by
        rw [taoExceptionalOffDiagonalExponentLedger]
      have hpows :
          ((Z : ℝ) ^ (2 / 125 : ℝ) *
              (Z : ℝ) ^ taoExceptionalSieveLevelExponent) *
            (Z : ℝ) ^ (1 - taoBurgessSavingExponent) =
          (Z : ℝ) ^ r := by
        rw [← Real.rpow_add hZpos, ← Real.rpow_add hZpos, hexp]
      have hthree : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
      rw [hthree, Real.rpow_natCast]
      rw [← hpows]
      dsimp [c]
      ring

theorem taoExceptionalOffDiagonalEnvelope_isLittleO :
    (fun Z : ℕ =>
      (Z : ℝ) ^ (2 / 125 : ℝ) *
        ((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent)) =o[atTop]
      (fun Z : ℕ => (Z : ℝ) / Real.log Z) := by
  let r : ℝ := 1 - (1 / 5000 : ℝ)
  let c : ℝ := 8 * (2 : ℝ) ^ (1 - taoBurgessSavingExponent)
  have hr : r < 1 := by norm_num [r]
  have hmodel :=
    (rpow_mul_rpow_log_isLittleO_id_div_log 3 hr).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (IsBigO.of_bound c ?_).trans_isLittleO hmodel
  filter_upwards [eventually_taoExceptionalSelbergFloorError_le,
    eventually_ge_atTop (1 : ℕ)] with Z hfloor hZ
  have hZpos : (0 : ℝ) < Z := by exact_mod_cast hZ
  have hleftNonneg : 0 ≤
      (Z : ℝ) ^ (2 / 125 : ℝ) *
        ((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent) := by positivity
  have hmodelNonneg : 0 ≤ (Z : ℝ) ^ r * Real.log Z ^ (3 : ℝ) := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleftNonneg, Real.norm_eq_abs]
  change _ ≤ c * |(Z : ℝ) ^ r * Real.log Z ^ (3 : ℝ)|
  rw [abs_of_nonneg hmodelNonneg]
  calc
    (Z : ℝ) ^ (2 / 125 : ℝ) *
          ((taoExceptionalSieveLevel Z : ℝ) *
            (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
          (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent) ≤
        (Z : ℝ) ^ (2 / 125 : ℝ) *
          (8 * ((Z : ℝ) ^ taoExceptionalSieveLevelExponent *
            Real.log Z ^ (3 : ℕ))) *
          (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent) := by gcongr
    _ = c * ((Z : ℝ) ^ r * Real.log Z ^ (3 : ℝ)) := by
      have htwo : (0 : ℝ) ≤ 2 := by norm_num
      have hZnonneg : (0 : ℝ) ≤ Z := hZpos.le
      rw [Real.mul_rpow htwo hZnonneg]
      have hexp : (2 / 125 : ℝ) + taoExceptionalSieveLevelExponent +
          (1 - taoBurgessSavingExponent) = r := by
        rw [taoExceptionalOffDiagonalExponentLedger]
      have hpows :
          ((Z : ℝ) ^ (2 / 125 : ℝ) *
              (Z : ℝ) ^ taoExceptionalSieveLevelExponent) *
            (Z : ℝ) ^ (1 - taoBurgessSavingExponent) =
          (Z : ℝ) ^ r := by
        rw [← Real.rpow_add hZpos, ← Real.rpow_add hZpos, hexp]
      have hthree : (3 : ℝ) = ((3 : ℕ) : ℝ) := by norm_num
      rw [hthree, Real.rpow_natCast]
      rw [← hpows]
      dsimp [c]
      ring

noncomputable def taoExceptionalBHMNumerator (C : ℝ) (J Z : ℕ) : ℝ :=
  ((((2 * Z : ℕ) : ℝ) *
          (2 / Real.log (taoExceptionalSieveLevel Z)) +
        (taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) +
      (((J - 1 : ℕ) : ℝ) *
        (((taoExceptionalSieveLevel Z : ℝ) *
            (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
          (C * (2 * Z : ℝ) ^
            (1 - taoBurgessSavingExponent)))))

theorem taoExceptionalFamilyOffDiagonal_isBigO
    {J : ℕ → ℕ} {A C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ᶠ Z : ℕ in atTop,
      (J Z : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ)) :
    (fun Z : ℕ => (((J Z - 1 : ℕ) : ℝ) *
      (((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (C * (2 * Z : ℝ) ^
          (1 - taoBurgessSavingExponent))))) =O[atTop]
      (fun Z : ℕ => (Z : ℝ) / Real.log Z) := by
  let envelope : ℕ → ℝ := fun Z =>
    (Z : ℝ) ^ (2 / 125 : ℝ) *
      ((taoExceptionalSieveLevel Z : ℝ) *
        (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
      (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent)
  apply (IsBigO.of_bound (A * C) ?_).trans
    (by simpa [envelope] using taoExceptionalOffDiagonalEnvelope_isBigO)
  filter_upwards [hJ] with Z hJZ
  have hJsub : (((J Z - 1 : ℕ) : ℝ)) ≤ J Z := by
    exact_mod_cast Nat.sub_le (J Z) 1
  have hleftNonneg : 0 ≤ (((J Z - 1 : ℕ) : ℝ) *
      (((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (C * (2 * Z : ℝ) ^
          (1 - taoBurgessSavingExponent)))) := by positivity
  have henvNonneg : 0 ≤ envelope Z := by
    dsimp [envelope]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleftNonneg, Real.norm_eq_abs,
    abs_of_nonneg henvNonneg]
  calc
    (((J Z - 1 : ℕ) : ℝ) *
        (((taoExceptionalSieveLevel Z : ℝ) *
            (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
          (C * (2 * Z : ℝ) ^
            (1 - taoBurgessSavingExponent)))) ≤
      (A * (Z : ℝ) ^ (2 / 125 : ℝ)) *
        (((taoExceptionalSieveLevel Z : ℝ) *
            (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
          (C * (2 * Z : ℝ) ^
            (1 - taoBurgessSavingExponent))) := by
              gcongr
              exact hJsub.trans hJZ
    _ = (A * C) * envelope Z := by
      dsimp [envelope]
      ring

theorem taoExceptionalFamilyOffDiagonal_isLittleO
    {J : ℕ → ℕ} {A C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ᶠ Z : ℕ in atTop,
      (J Z : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ)) :
    (fun Z : ℕ => (((J Z - 1 : ℕ) : ℝ) *
      (((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (C * (2 * Z : ℝ) ^
          (1 - taoBurgessSavingExponent))))) =o[atTop]
      (fun Z : ℕ => (Z : ℝ) / Real.log Z) := by
  let envelope : ℕ → ℝ := fun Z =>
    (Z : ℝ) ^ (2 / 125 : ℝ) *
      ((taoExceptionalSieveLevel Z : ℝ) *
        (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
      (2 * Z : ℝ) ^ (1 - taoBurgessSavingExponent)
  apply (IsBigO.of_bound (A * C) ?_).trans_isLittleO
    (by simpa [envelope] using taoExceptionalOffDiagonalEnvelope_isLittleO)
  filter_upwards [hJ] with Z hJZ
  have hJsub : (((J Z - 1 : ℕ) : ℝ)) ≤ J Z := by
    exact_mod_cast Nat.sub_le (J Z) 1
  have hleftNonneg : 0 ≤ (((J Z - 1 : ℕ) : ℝ) *
      (((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (C * (2 * Z : ℝ) ^
          (1 - taoBurgessSavingExponent)))) := by positivity
  have henvNonneg : 0 ≤ envelope Z := by
    dsimp [envelope]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleftNonneg, Real.norm_eq_abs,
    abs_of_nonneg henvNonneg]
  calc
    (((J Z - 1 : ℕ) : ℝ) *
        (((taoExceptionalSieveLevel Z : ℝ) *
            (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
          (C * (2 * Z : ℝ) ^
            (1 - taoBurgessSavingExponent)))) ≤
      (A * (Z : ℝ) ^ (2 / 125 : ℝ)) *
        (((taoExceptionalSieveLevel Z : ℝ) *
            (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
          (C * (2 * Z : ℝ) ^
            (1 - taoBurgessSavingExponent))) := by
              gcongr
              exact hJsub.trans hJZ
    _ = (A * C) * envelope Z := by
      dsimp [envelope]
      ring

theorem taoExceptionalBHMNumerator_isBigO
    {J : ℕ → ℕ} {A C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ᶠ Z : ℕ in atTop,
      (J Z : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ)) :
    (fun Z : ℕ => taoExceptionalBHMNumerator C (J Z) Z) =O[atTop]
      (fun Z : ℕ => (Z : ℝ) / Real.log Z) := by
  have hdiag := taoExceptionalSelbergMain_isBigO.add
    taoExceptionalSelbergFloorError_isBigO
  have hoff := taoExceptionalFamilyOffDiagonal_isBigO hC hJ
  simpa only [taoExceptionalBHMNumerator] using hdiag.add hoff

theorem exists_eventually_taoExceptionalBHMNumerator_div_card_le
    {J : ℕ → ℕ} {A C : ℝ} (hC : 0 ≤ C)
    (hJ : ∀ᶠ Z : ℕ in atTop,
      (J Z : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℕ in atTop,
      taoExceptionalBHMNumerator C (J Z) Z /
        (taoDyadicPrimeBand Z).card ≤ K := by
  obtain ⟨K, hKpos, hK⟩ :=
    (taoExceptionalBHMNumerator_isBigO hC hJ).exists_pos
  refine ⟨2 * K, by positivity, ?_⟩
  filter_upwards [hK.bound,
    eventually_nat_div_two_log_le_card_taoDyadicPrimeBand,
    eventually_one_lt_taoExceptionalSieveLevel,
    eventually_taoExceptionalSieveLevel_lt,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with Z hnum hband hR hRZ hlogZ
  change 1 ≤ Real.log (Z : ℝ) at hlogZ
  have hZpos : (0 : ℝ) < Z := by
    exact_mod_cast (show 0 < Z by
      have : 1 < Z := hR.trans hRZ
      omega)
  have hlogZpos : 0 < Real.log (Z : ℝ) := lt_of_lt_of_le zero_lt_one hlogZ
  have hgpos : 0 < (Z : ℝ) / Real.log Z := div_pos hZpos hlogZpos
  have hlogRpos : 0 < Real.log (taoExceptionalSieveLevel Z) :=
    Real.log_pos (by exact_mod_cast hR)
  have hnumNonneg : 0 ≤ taoExceptionalBHMNumerator C (J Z) Z := by
    unfold taoExceptionalBHMNumerator
    positivity
  have hgNonneg : 0 ≤ (Z : ℝ) / Real.log Z := hgpos.le
  have hnumLe : taoExceptionalBHMNumerator C (J Z) Z ≤
      K * ((Z : ℝ) / Real.log Z) := by
    change |taoExceptionalBHMNumerator C (J Z) Z| ≤
      K * |(Z : ℝ) / Real.log Z| at hnum
    rw [abs_of_nonneg hnumNonneg, abs_of_nonneg hgNonneg] at hnum
    exact hnum
  have hgLe : (Z : ℝ) / Real.log Z ≤
      2 * ((taoDyadicPrimeBand Z).card : ℝ) := by
    calc
      (Z : ℝ) / Real.log Z = 2 * ((Z : ℝ) / (2 * Real.log Z)) := by ring
      _ ≤ 2 * ((taoDyadicPrimeBand Z).card : ℝ) := by gcongr
  have hbandPos : (0 : ℝ) < (taoDyadicPrimeBand Z).card := by
    have : 0 < (Z : ℝ) / (2 * Real.log Z) := by positivity
    exact this.trans_le hband
  apply (div_le_iff₀ hbandPos).2
  calc
    taoExceptionalBHMNumerator C (J Z) Z ≤
        K * ((Z : ℝ) / Real.log Z) := hnumLe
    _ ≤ K * (2 * ((taoDyadicPrimeBand Z).card : ℝ)) := by
      gcongr
    _ = (2 * K) * ((taoDyadicPrimeBand Z).card : ℝ) := by ring

/-- The provisional cardinality constant only changes how large `Z` must be:
the eventual normalized BHM bound itself is absolute. -/
theorem exists_uniform_eventually_taoExceptionalBHMNumerator_div_card_le :
    ∃ K : ℝ, 0 < K ∧ ∀ {J : ℕ → ℕ} {A C : ℝ}, 0 ≤ C →
      (∀ᶠ Z : ℕ in atTop,
        (J Z : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ)) →
      ∀ᶠ Z : ℕ in atTop,
        taoExceptionalBHMNumerator C (J Z) Z /
          (taoDyadicPrimeBand Z).card ≤ K := by
  have hdiag := taoExceptionalSelbergMain_isBigO.add
    taoExceptionalSelbergFloorError_isBigO
  obtain ⟨D, hDpos, hD⟩ := hdiag.exists_pos
  refine ⟨2 * (D + 1), by positivity, ?_⟩
  intro J A C hC hJ
  have hoff := taoExceptionalFamilyOffDiagonal_isLittleO hC hJ
  filter_upwards [hD.bound, hoff.bound zero_lt_one,
    eventually_nat_div_two_log_le_card_taoDyadicPrimeBand,
    eventually_one_lt_taoExceptionalSieveLevel,
    eventually_taoExceptionalSieveLevel_lt,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))] with Z hdiagZ hoffZ hband hR hRZ hlogZ
  change 1 ≤ Real.log (Z : ℝ) at hlogZ
  have hZpos : (0 : ℝ) < Z := by
    exact_mod_cast (show 0 < Z by
      have : 1 < Z := hR.trans hRZ
      omega)
  have hlogZpos : 0 < Real.log (Z : ℝ) := lt_of_lt_of_le zero_lt_one hlogZ
  have hgpos : 0 < (Z : ℝ) / Real.log Z := div_pos hZpos hlogZpos
  have hlogRpos : 0 < Real.log (taoExceptionalSieveLevel Z) :=
    Real.log_pos (by exact_mod_cast hR)
  have hdiagNonneg : 0 ≤
      (((2 * Z : ℕ) : ℝ) *
          (2 / Real.log (taoExceptionalSieveLevel Z)) +
        (taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) := by positivity
  have hoffNonneg : 0 ≤ (((J Z - 1 : ℕ) : ℝ) *
      (((taoExceptionalSieveLevel Z : ℝ) *
          (1 + Real.log (taoExceptionalSieveLevel Z)) ^ 3) *
        (C * (2 * Z : ℝ) ^
          (1 - taoBurgessSavingExponent)))) := by positivity
  have hgNonneg : 0 ≤ (Z : ℝ) / Real.log Z := hgpos.le
  rw [Real.norm_eq_abs, abs_of_nonneg hdiagNonneg,
    Real.norm_eq_abs, abs_of_nonneg hgNonneg] at hdiagZ
  rw [Real.norm_eq_abs, abs_of_nonneg hoffNonneg,
    Real.norm_eq_abs, abs_of_nonneg hgNonneg] at hoffZ
  have hnumLe : taoExceptionalBHMNumerator C (J Z) Z ≤
      (D + 1) * ((Z : ℝ) / Real.log Z) := by
    unfold taoExceptionalBHMNumerator
    calc
      _ ≤ D * ((Z : ℝ) / Real.log Z) +
          1 * ((Z : ℝ) / Real.log Z) := add_le_add hdiagZ hoffZ
      _ = (D + 1) * ((Z : ℝ) / Real.log Z) := by ring
  have hgLe : (Z : ℝ) / Real.log Z ≤
      2 * ((taoDyadicPrimeBand Z).card : ℝ) := by
    calc
      (Z : ℝ) / Real.log Z = 2 * ((Z : ℝ) / (2 * Real.log Z)) := by ring
      _ ≤ 2 * ((taoDyadicPrimeBand Z).card : ℝ) := by gcongr
  have hbandPos : (0 : ℝ) < (taoDyadicPrimeBand Z).card := by
    have : 0 < (Z : ℝ) / (2 * Real.log Z) := by positivity
    exact this.trans_le hband
  apply (div_le_iff₀ hbandPos).2
  calc
    taoExceptionalBHMNumerator C (J Z) Z ≤
        (D + 1) * ((Z : ℝ) / Real.log Z) := hnumLe
    _ ≤ (D + 1) * (2 * ((taoDyadicPrimeBand Z).card : ℝ)) := by
      gcongr
    _ = (2 * (D + 1)) * ((taoDyadicPrimeBand Z).card : ℝ) := by ring

theorem exists_eventually_exceptionalFamily_secondMoment_le_of_explicitBurgess
    {C A : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q₁ : ℕ → ℕ)
    (W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z))
    (hq₁ : ∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z))
    (hsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (W Z))
    (hcard : ∀ᶠ Z : ℕ in atTop,
      ((W Z).card : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ Z : ℕ in atTop,
      ∑ a ∈ W Z, ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤ K := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_eventually_taoExceptionalBHMNumerator_div_card_le hC hcard
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [
    eventually_sum_finiteNormalizedPrimeBandSum_sq_le_of_explicitBurgess
      hC hburgess q₁ W hq₁ hsep,
    hK] with Z hsum hbound
  exact hsum.trans (by simpa only [taoExceptionalBHMNumerator] using hbound)

/-- Uniform form of the conditional moment estimate.  The output constant is
independent of the provisional coefficient in `#W ≤ A Z^(2/125)`. -/
theorem exists_uniform_eventually_exceptionalFamily_secondMoment_le_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀) :
    ∃ K : ℝ, 0 < K ∧
      ∀ {A : ℝ} (q₁ : ℕ → ℕ)
        (W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z)),
        (∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z)) →
        (∀ᶠ Z : ℕ in atTop, IsSeparatedTaoExceptionalFamily (W Z)) →
        (∀ᶠ Z : ℕ in atTop,
          ((W Z).card : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ)) →
        ∀ᶠ Z : ℕ in atTop,
          ∑ a ∈ W Z, ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤ K := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_uniform_eventually_taoExceptionalBHMNumerator_div_card_le
  refine ⟨K, hKpos, ?_⟩
  intro A q₁ W hq₁ hsep hcard
  have hnum := hK hC hcard
  filter_upwards [
    eventually_sum_finiteNormalizedPrimeBandSum_sq_le_of_explicitBurgess
      hC hburgess q₁ W hq₁ hsep,
    hnum] with Z hsum hbound
  exact hsum.trans (by simpa only [taoExceptionalBHMNumerator] using hbound)

/-- An arbitrary truncation of a finite set to the smaller of a requested
cardinality and its actual cardinality. -/
noncomputable def taoTruncateFinset {α : Type*} [DecidableEq α]
    (n : ℕ) (s : Finset α) : Finset α :=
  Classical.choose (Finset.exists_subset_card_eq (Nat.min_le_right n s.card))

theorem taoTruncateFinset_subset {α : Type*} [DecidableEq α]
    (n : ℕ) (s : Finset α) :
    taoTruncateFinset n s ⊆ s :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (Nat.min_le_right n s.card))).1

theorem card_taoTruncateFinset {α : Type*} [DecidableEq α]
    (n : ℕ) (s : Finset α) :
    (taoTruncateFinset n s).card = min n s.card :=
  (Classical.choose_spec
    (Finset.exists_subset_card_eq (Nat.min_le_right n s.card))).2

/-- Tao's self-improving truncation argument.  A provisional
`#W ≤ A Z^(2/125)` bound is imposed only on a truncation of `W`; the strict
off-diagonal saving makes the resulting moment constant independent of `A`,
which forces the same power bound for the original family. -/
theorem exists_eventually_exceptionalFamily_card_le_and_secondMoment_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q₁ : ℕ → ℕ)
    (W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z))
    (hq₁ : ∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z))
    (hsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (W Z))
    (hexceptional : ∀ᶠ Z : ℕ in atTop,
      ∀ a ∈ W Z, taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖) :
    ∃ K : ℝ, 0 < K ∧
      (∀ᶠ Z : ℕ in atTop,
        ((W Z).card : ℝ) ≤ K * (Z : ℝ) ^ (2 / 125 : ℝ)) ∧
      (∀ᶠ Z : ℕ in atTop,
        ∑ a ∈ W Z, ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤ K) := by
  classical
  obtain ⟨M, hMpos, hMoment⟩ :=
    exists_uniform_eventually_exceptionalFamily_secondMoment_le_of_explicitBurgess
      hC hburgess
  let A : ℝ := M + 2
  let N : ℕ → ℕ := fun Z =>
    Nat.floor (A * (Z : ℝ) ^ (2 / 125 : ℝ))
  let V : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z) := fun Z =>
    taoTruncateFinset (N Z) (W Z)
  have hVsubset : ∀ Z, V Z ⊆ W Z := fun Z => by
    dsimp [V]
    exact taoTruncateFinset_subset _ _
  have hVcardEq : ∀ Z, (V Z).card = min (N Z) (W Z).card := fun Z => by
    dsimp [V]
    exact card_taoTruncateFinset _ _
  have hApos : 0 < A := by dsimp [A]; linarith
  have hVcard : ∀ᶠ Z : ℕ in atTop,
      ((V Z).card : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
    filter_upwards [] with Z
    have harg : 0 ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by positivity
    calc
      ((V Z).card : ℝ) ≤ (N Z : ℝ) := by
        exact_mod_cast (hVcardEq Z ▸ Nat.min_le_left (N Z) (W Z).card)
      _ ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
        dsimp [N]
        exact Nat.floor_le harg
  have hVsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (V Z) := by
    filter_upwards [hsep] with Z hsepZ
    intro a ha b hb hba
    exact hsepZ a (hVsubset Z ha) b (hVsubset Z hb) hba
  have hVMoment := hMoment q₁ V hq₁ hVsep hVcard
  have hWcard : ∀ᶠ Z : ℕ in atTop,
      ((W Z).card : ℝ) ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by
    filter_upwards [hVMoment, hexceptional,
      eventually_ge_atTop (1 : ℕ)] with Z hVMomentZ hexceptionalZ hZ
    have hZpos : (0 : ℝ) < Z := by exact_mod_cast hZ
    have hxpos : 0 < (Z : ℝ) ^ (2 / 125 : ℝ) :=
      Real.rpow_pos_of_pos hZpos _
    have hxone : 1 ≤ (Z : ℝ) ^ (2 / 125 : ℝ) :=
      Real.one_le_rpow (by exact_mod_cast hZ) (by norm_num)
    by_contra hnot
    push Not at hnot
    have harg : 0 ≤ A * (Z : ℝ) ^ (2 / 125 : ℝ) := by positivity
    have hNlt : N Z < (W Z).card := by
      apply_mod_cast lt_of_le_of_lt (Nat.floor_le harg) hnot
    have hVcardN : (V Z).card = N Z := by
      rw [hVcardEq, Nat.min_eq_left hNlt.le]
    have hmarkov : ((V Z).card : ℝ) *
        taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) ≤
          ∑ a ∈ V Z, ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 := by
      calc
        ((V Z).card : ℝ) *
            taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) =
          ∑ _a ∈ V Z,
            taoExceptionalPrimeCharacterThreshold Z ^ (2 : ℕ) := by simp
        _ ≤ ∑ a ∈ V Z,
            ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro a ha
          have haExceptional := hexceptionalZ a (hVsubset Z ha)
          nlinarith [taoExceptionalPrimeCharacterThreshold_nonneg Z,
            norm_nonneg (finiteNormalizedPrimeBandSum Z a.value)]
    have hscaled : ((V Z).card : ℝ) *
        (Z : ℝ) ^ (-(2 : ℝ) / 125) ≤ M := by
      rw [← taoExceptionalPrimeCharacterThreshold_pow_two] 
      exact hmarkov.trans hVMomentZ
    have hVbound : ((V Z).card : ℝ) ≤
        M * (Z : ℝ) ^ (2 / 125 : ℝ) := by
      calc
        ((V Z).card : ℝ) =
            (((V Z).card : ℝ) * (Z : ℝ) ^ (-(2 : ℝ) / 125)) *
              (Z : ℝ) ^ (2 / 125 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add hZpos]
            norm_num
        _ ≤ M * (Z : ℝ) ^ (2 / 125 : ℝ) :=
          mul_le_mul_of_nonneg_right hscaled hxpos.le
    have hfloorLower : (M + 1) * (Z : ℝ) ^ (2 / 125 : ℝ) ≤ N Z := by
      have hfloor := Nat.sub_one_lt_floor
        (A * (Z : ℝ) ^ (2 / 125 : ℝ))
      change A * (Z : ℝ) ^ (2 / 125 : ℝ) - 1 < (N Z : ℝ) at hfloor
      apply le_of_lt
      calc
        (M + 1) * (Z : ℝ) ^ (2 / 125 : ℝ) ≤
            A * (Z : ℝ) ^ (2 / 125 : ℝ) - 1 := by
          dsimp [A]
          nlinarith
        _ < (N Z : ℝ) := hfloor
    rw [hVcardN] at hVbound
    have : (M + 1) * (Z : ℝ) ^ (2 / 125 : ℝ) ≤
        M * (Z : ℝ) ^ (2 / 125 : ℝ) := hfloorLower.trans hVbound
    nlinarith
  have hWMoment := hMoment q₁ W hq₁ hsep hWcard
  refine ⟨A, hApos, hWcard, ?_⟩
  filter_upwards [hWMoment] with Z hsum
  exact hsum.trans (by dsimp [A]; linarith)

/-- Finite Chebyshev inequality for squared norms.  This is the exact
elementary step behind the final `O(λ⁻²)` clause of Tao's Lemma 5.1. -/
theorem card_norm_ge_mul_sq_le_sum_sq
    {α : Type*} [DecidableEq α] (W : Finset α) (f : α → ℂ) (threshold : ℝ)
    (hthresholdNonneg : 0 ≤ threshold) :
    (((W.filter fun a => threshold ≤ ‖f a‖).card : ℕ) : ℝ) *
        threshold ^ (2 : ℕ) ≤
      ∑ a ∈ W, ‖f a‖ ^ (2 : ℕ) := by
  calc
    (((W.filter fun a => threshold ≤ ‖f a‖).card : ℕ) : ℝ) *
        threshold ^ (2 : ℕ) =
        ∑ a ∈ W.filter (fun a => threshold ≤ ‖f a‖),
          threshold ^ (2 : ℕ) := by simp
    _ ≤ ∑ a ∈ W.filter (fun a => threshold ≤ ‖f a‖), ‖f a‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro a ha
      have hthreshold := (Finset.mem_filter.mp ha).2
      nlinarith [norm_nonneg (f a)]
    _ ≤ ∑ a ∈ W, ‖f a‖ ^ (2 : ℕ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _a _ha _hnot => sq_nonneg _)

theorem card_norm_ge_le_of_sum_sq_le
    {α : Type*} [DecidableEq α] {W : Finset α} {f : α → ℂ}
    {threshold K : ℝ} (hthreshold : 0 < threshold)
    (hsum : ∑ a ∈ W, ‖f a‖ ^ (2 : ℕ) ≤ K) :
    (((W.filter fun a => threshold ≤ ‖f a‖).card : ℕ) : ℝ) ≤
      K * threshold⁻¹ ^ (2 : ℕ) := by
  have hraw :=
    (card_norm_ge_mul_sq_le_sum_sq W f threshold hthreshold.le).trans hsum
  calc
    (((W.filter fun a => threshold ≤ ‖f a‖).card : ℕ) : ℝ) ≤
        K / threshold ^ (2 : ℕ) := by
      exact (le_div_iff₀ (sq_pos_of_pos hthreshold)).2 hraw
    _ = K * threshold⁻¹ ^ (2 : ℕ) := by
      rw [div_eq_mul_inv, inv_pow]

/-- Full source-shaped output of Lemma 5.1, conditional only on the explicit
Burgess input: the exceptional family has size `O(Z^0.016)`, has bounded
squared moment, and every positive threshold has an `O(λ⁻²)` tail with the
same absolute constant. -/
theorem exists_eventually_exceptionalFamily_card_secondMoment_and_tail_of_explicitBurgess
    {C : ℝ} {H₀ : ℕ} (hC : 0 ≤ C)
    (hburgess : TaoExplicitCubefreeBurgessBound C H₀)
    (q₁ : ℕ → ℕ)
    (W : ∀ Z, Finset (TaoExceptionalCharacterDatum (q₁ Z) Z))
    (hq₁ : ∀ᶠ Z : ℕ in atTop, Squarefree (q₁ Z))
    (hsep : ∀ᶠ Z : ℕ in atTop,
      IsSeparatedTaoExceptionalFamily (W Z))
    (hexceptional : ∀ᶠ Z : ℕ in atTop,
      ∀ a ∈ W Z, taoExceptionalPrimeCharacterThreshold Z ≤
        ‖finiteNormalizedPrimeBandSum Z a.value‖) :
    ∃ K : ℝ, 0 < K ∧
      (∀ᶠ Z : ℕ in atTop,
        ((W Z).card : ℝ) ≤ K * (Z : ℝ) ^ (2 / 125 : ℝ)) ∧
      (∀ᶠ Z : ℕ in atTop,
        ∑ a ∈ W Z, ‖finiteNormalizedPrimeBandSum Z a.value‖ ^ 2 ≤ K) ∧
      ∀ threshold : ℕ → ℝ, (∀ᶠ Z : ℕ in atTop, 0 < threshold Z) →
        ∀ᶠ Z : ℕ in atTop,
          (((W Z).filter fun a =>
              threshold Z ≤ ‖finiteNormalizedPrimeBandSum Z a.value‖).card : ℝ) ≤
            K * (threshold Z)⁻¹ ^ (2 : ℕ) := by
  classical
  obtain ⟨K, hKpos, hcard, hmoment⟩ :=
    exists_eventually_exceptionalFamily_card_le_and_secondMoment_of_explicitBurgess
      hC hburgess q₁ W hq₁ hsep hexceptional
  refine ⟨K, hKpos, hcard, hmoment, ?_⟩
  intro threshold hthreshold
  filter_upwards [hmoment, hthreshold] with Z hsum hthresholdZ
  exact card_norm_ge_le_of_sum_sq_le hthresholdZ hsum

end Tao2026
