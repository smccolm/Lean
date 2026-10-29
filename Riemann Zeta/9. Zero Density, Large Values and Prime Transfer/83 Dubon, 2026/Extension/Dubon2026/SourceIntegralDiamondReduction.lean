import Dubon2026.SourceEvenWeightIntegralDiamondForm

/-! DUB-17/18 -> original Gamma1 degree/genus -> reduced field action
-> preservation of reduced integral-ratio relations. The actual integer
Fourier reduction has exactly the prime-multiple kernel. Integer scalar
and prime-division identities for actual forms will transport that
kernel through the constructed level-cleared diamond transforms.
Adapted from the pinned Apache-2.0 Anthropic reduced-field-action proof,
using the existing native Fourier map and actual modular diamond. -/
namespace Dubon2026.SourceFunctionField.IntegralDiamond
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm

/-- Coefficient reduction of the original integer Fourier series. -/
def red (ℓ : ℕ) : PowerSeries ℤ →+* LaurentSeries (ZMod ℓ) :=
  (HahnSeries.ofPowerSeries ℤ (ZMod ℓ)).comp (PowerSeries.map (Int.castRingHom (ZMod ℓ)))

theorem red_apply (ℓ : ℕ) [Fact ℓ.Prime] (p : PowerSeries ℤ) :
    red ℓ p = intSeriesC (ZMod ℓ) p := rfl

theorem red_eq_zero_iff (ℓ : ℕ) (p : PowerSeries ℤ) :
    red ℓ p = 0 ↔ ∃ q : PowerSeries ℤ, p = PowerSeries.C (ℓ : ℤ) * q := by
  constructor
  · intro h
    have h1 : p.map (Int.castRingHom (ZMod ℓ)) = 0 :=
      HahnSeries.ofPowerSeries_injective
        (by rw [← RingHom.comp_apply]; exact h.trans (map_zero _).symm)
    have hdvd (n : ℕ) : (ℓ : ℤ) ∣ p.coeff n := by
      have hn := congrArg (PowerSeries.coeff n) h1
      rw [PowerSeries.coeff_map, map_zero, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hn
      exact hn
    refine ⟨PowerSeries.mk fun n => p.coeff n / ℓ, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (hdvd n)]
  · rintro ⟨q, rfl⟩
    rw [map_mul]
    have hC : red ℓ (PowerSeries.C (ℓ : ℤ)) = 0 := by
      rw [red, RingHom.comp_apply, PowerSeries.map_C, eq_intCast, Int.cast_natCast,
        ZMod.natCast_self, map_zero, map_zero]
    rw [hC, zero_mul]

theorem integralQExp_unique {f : ℍ → ℂ} {p q : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (hq : IsIntegralQExp f q) : p = q := by
  apply PowerSeries.map_injective (Int.castRingHom ℂ) Int.cast_injective
  exact hp.trans hq.symm

theorem integralQExp_int_smul {N : ℕ} {k : ℤ}
    (f : ModularForm (Gamma1 N) k) {p : PowerSeries ℤ}
    (hp : IsIntegralQExp f p) (z : ℤ) :
    IsIntegralQExp ((z : ℂ) • (⇑f : ℍ → ℂ)) (PowerSeries.C z * p) := by
  unfold IsIntegralQExp
  rw [map_mul, PowerSeries.map_C, hp, ModularForm.qExpansion_smul one_pos
    (SourceFricke.gammaOne_one_mem_strictPeriods N), PowerSeries.smul_eq_C_mul]
  rfl

theorem integralQExp_inv_int_smul {N : ℕ} {k : ℤ}
    (f : ModularForm (Gamma1 N) k) {p : PowerSeries ℤ} (z : ℤ) (hz : z ≠ 0)
    (hp : IsIntegralQExp f (PowerSeries.C z * p)) :
    IsIntegralQExp ((z : ℂ)⁻¹ • (⇑f : ℍ → ℂ)) p := by
  unfold IsIntegralQExp
  rw [ModularForm.qExpansion_smul one_pos (SourceFricke.gammaOne_one_mem_strictPeriods N),
    ← hp, map_mul, PowerSeries.map_C]
  ext n
  simp only [PowerSeries.coeff_smul, PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
    smul_eq_mul, eq_intCast]
  rw [← mul_assoc, inv_mul_cancel₀ (Int.cast_ne_zero.mpr hz), one_mul]

end
end Dubon2026.SourceFunctionField.IntegralDiamond
