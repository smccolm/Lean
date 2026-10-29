import Dubon2026.SourceGammaOneIntegralToricWeightFour

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> integral toric coordinates. The actual integer coefficient
families reconstruct both toric invariant series over an arbitrary field
with a primitive level root. This identifies the literal Laurent series;
proving that the toric coordinate pair is an exact-order elliptic point
is a subsequent, separate obligation. Adapted from Anthropic FLT,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricFourier
noncomputable section
open HahnSeries
variable {M : ℕ} [NeZero M] (K : Type*) [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

theorem intSeriesC_eq (p : PowerSeries ℤ) : intSeriesC K p = ofPowerSeries ℤ K (p.map (Int.castRingHom K)) := rfl

theorem smul_ofPowerSeries (a : K) (P : PowerSeries K) :
    a • ofPowerSeries ℤ K P = ofPowerSeries ℤ K (PowerSeries.C a * P) := by
  rw [map_mul, ofPowerSeries_C, C_mul_eq_smul]

include hζ in

theorem weightTwo_series (s : ZMod M) (hs : s ≠ 0) :
    (M : LaurentSeries K) ^ 3 * (1 + 12 * ofPowerSeries ℤ K (xS (ζ ^ s.val))) =
      ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (bZ M c)) := by
  have hu : ζ ^ s.val = ψ hζ s := rfl
  rw [hu]

  have lhs : (M : LaurentSeries K) ^ 3 * (1 + 12 * ofPowerSeries ℤ K (xS (ψ hζ s))) =
      ofPowerSeries ℤ K (PowerSeries.C ((M : K) ^ 3) * wS (ψ hζ s)) := by
    rw [wS_eq', map_mul, map_add, map_one, map_mul, map_ofNat, ofPowerSeries_C, map_pow, map_natCast]
  have rhs : ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (bZ M c)) =
      ofPowerSeries ℤ K (∑ c : ZMod M, PowerSeries.C (ψ hζ (s * c)) *
        (PowerSeries.mk (bZ M c)).map (Int.castRingHom K)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_eq, smul_ofPowerSeries]
    rfl
  rw [lhs, rhs]
  congr 1
  ext n
  rw [PowerSeries.coeff_C_mul, map_sum, wS, PowerSeries.coeff_mk, ← sum_ψ_bZ hζ s hs n]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]

include hζ in

theorem weightFour_series (s : ZMod M) (hs : s ≠ 0) :
    (M : LaurentSeries K) ^ 5 * (ofPowerSeries ℤ K (xS (ζ ^ s.val)) + 6 * ofPowerSeries ℤ K (xS (ζ ^ s.val)) ^ 2 +
        2 * intSeriesC K tateA4) =
      ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (dZ M c)) := by
  have hu : ζ ^ s.val = ψ hζ s := rfl
  rw [hu, intSeriesC_eq]
  have lhs : (M : LaurentSeries K) ^ 5 * (ofPowerSeries ℤ K (xS (ψ hζ s)) +
      6 * ofPowerSeries ℤ K (xS (ψ hζ s)) ^ 2 + 2 * ofPowerSeries ℤ K (tateA4.map (Int.castRingHom K))) =
      ofPowerSeries ℤ K (PowerSeries.C ((M : K) ^ 5) * fS (ψ hζ s)) := by
    simp only [fS_eq', map_mul, map_add, map_ofNat, map_pow, map_natCast, sq]
  have rhs : ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (dZ M c)) =
      ofPowerSeries ℤ K (∑ c : ZMod M, PowerSeries.C (ψ hζ (s * c)) *
        (PowerSeries.mk (dZ M c)).map (Int.castRingHom K)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_eq, smul_ofPowerSeries]
    rfl
  rw [lhs, rhs]
  congr 1
  ext n
  rw [PowerSeries.coeff_C_mul, map_sum, fS, PowerSeries.coeff_mk, ← sum_ψ_dZ hζ s hs n]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]
end
end Dubon2026.SourceFunctionField.GammaOne.ToricFourier
