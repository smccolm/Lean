import Dubon2026.SourceTateIntegralCoefficients
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> marked-point chart. Construct the actual integral Tate model
and prove that its Laurent discriminant is a unit in every coefficient
ring. Its first discriminant coefficient is one, so no residue
characteristic is excluded. This discharges the model nonsingularity
input needed by the native torsion specialization route. Adapted from
Anthropic FLT TateFormal, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open PowerSeries HahnSeries

/-- The literal integral Tate Weierstrass curve with coefficients (1,0,0,a4,a6). -/
def tatePowerSeries : WeierstrassCurve (PowerSeries ℤ) := ⟨1, 0, 0, tateA4, tateA6⟩

@[simp] theorem tatePowerSeries_a₁ : tatePowerSeries.a₁ = 1 := rfl
@[simp] theorem tatePowerSeries_a₂ : tatePowerSeries.a₂ = 0 := rfl
@[simp] theorem tatePowerSeries_a₃ : tatePowerSeries.a₃ = 0 := rfl
@[simp] theorem tatePowerSeries_a₄ : tatePowerSeries.a₄ = tateA4 := rfl
@[simp] theorem tatePowerSeries_a₆ : tatePowerSeries.a₆ = tateA6 := rfl

/-- The coefficient and exponent embedding of integer power series into Laurent series. -/
def laurentOfInt (K : Type*) [CommRing K] : PowerSeries ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (Int.castRingHom K))

theorem laurentOfInt_apply (K : Type*) [CommRing K] (f : PowerSeries ℤ) :
    laurentOfInt K f = HahnSeries.ofPowerSeries ℤ K (f.map (Int.castRingHom K)) := rfl

/-- The literal Tate curve over Laurent series, obtained from its integral coefficient model. -/
def tateLaurent (K : Type*) [CommRing K] : WeierstrassCurve (LaurentSeries K) :=
  tatePowerSeries.map (laurentOfInt K)

@[simp] theorem tateLaurent_a₄ (K : Type*) [CommRing K] :
    (tateLaurent K).a₄ = laurentOfInt K tateA4 := rfl

@[simp] theorem tateLaurent_a₆ (K : Type*) [CommRing K] :
    (tateLaurent K).a₆ = laurentOfInt K tateA6 := rfl

instance instIsElliptic_tateLaurent (K : Type*) [CommRing K] : (tateLaurent K).IsElliptic := by
  constructor
  have hΔeq : tatePowerSeries.Δ =
      -tateA6 + tateA4 ^ 2 - PowerSeries.C 64 * tateA4 ^ 3 - PowerSeries.C 432 * tateA6 ^ 2
        + PowerSeries.C 72 * (tateA4 * tateA6) := by
    rw [show (PowerSeries.C (64 : ℤ)) = (64 : PowerSeries ℤ) from map_ofNat _ 64,
      show (PowerSeries.C (432 : ℤ)) = (432 : PowerSeries ℤ) from map_ofNat _ 432,
      show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72]
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃,
      tatePowerSeries_a₄, tatePowerSeries_a₆]
    ring
  have hc0 : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.constantCoeff_C,
      constantCoeff_tateA4, constantCoeff_tateA6]
    ring
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have hsq4 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 1 (tateA6 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 1 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul1, h420, hsq4,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 1 (tateA4 * tateA6) = 0 := by
    rw [hmul1, coeff_zero_tateA4, coeff_zero_tateA6]
    norm_num
  have hc1 : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, hsq4, hsq6, hcb4, hprod,
      coeff_one_tateA6]
    norm_num
  obtain ⟨u, hXu⟩ : (PowerSeries.X : PowerSeries ℤ) ∣ tatePowerSeries.Δ :=
    PowerSeries.X_dvd_iff.mpr hc0
  have h1u : PowerSeries.coeff 1 tatePowerSeries.Δ = PowerSeries.constantCoeff u := by
    rw [hXu, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]
  have hu : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← h1u, hc1]
    exact isUnit_one
  have hΔL : (tateLaurent K).Δ = laurentOfInt K tatePowerSeries.Δ := by
    rw [tateLaurent, WeierstrassCurve.map_Δ]
  rw [hΔL, hXu, map_mul]
  refine IsUnit.mul ?_ (hu.map (laurentOfInt K))
  have hX : laurentOfInt K PowerSeries.X = HahnSeries.single (1 : ℤ) 1 := by
    rw [laurentOfInt_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  rw [hX]
  exact ⟨⟨HahnSeries.single (1 : ℤ) 1, HahnSeries.single (-1 : ℤ) 1,
    by simp [HahnSeries.single_mul_single], by simp [HahnSeries.single_mul_single]⟩, rfl⟩

end
end Dubon2026.SourceFunctionField
