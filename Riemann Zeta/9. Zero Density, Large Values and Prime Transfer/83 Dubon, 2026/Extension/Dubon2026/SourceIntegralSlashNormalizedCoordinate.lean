import Dubon2026.SourceIntegralSlashNormalizedMap
import Dubon2026.SourceIntegralPowerSeriesFrobenius
import Dubon2026.SourceIntegralTranscendentalSeparability

/-! DUB-17/18 -> original Gamma1 genus preservation -> reverse genus inequality
-> cusp residue fiber bounds -> injectivity of the actual reduced slash chart.
The original j is a normalized generator and its chart value is exactly j(q^N),
already proved transcendental. Native power-series expansion and original eta
unit identities supply the computation in every coefficient characteristic. -/
namespace Dubon2026.SourceFunctionField.IntegralSlash
noncomputable section
open UpperHalfPlane CongruenceSubgroup GammaOne
open scoped MatrixGroups ModularForm
local notation "Zbar" => integralClosure ℤ ℂ

theorem ofPowerSeries_reducedSlashSeries_levelOne (N : ℕ) [NeZero N]
    {K : Type*} [Field K] (φ : Zbar →+* K) (hN : (N : K) ≠ 0)
    (β : SL(2, ℤ)) {k : ℤ} (hk : Even k) (f : ModularForm 𝒮ℒ k)
    {p : PowerSeries ℤ} (hp : IsIntegralQExp f p) :
    HahnSeries.ofPowerSeries ℤ K (reducedSlashSeries N hk
      (ModularNormPolynomial.restrict (Subgroup.map_le_range _ (Gamma1 N)) f)
      hp β φ hN) = qExpand K N (intSeriesC K p) := by
  rw [intSeriesC, qExpand_ofPowerSeries_eq_expand]
  congr 1
  ext n
  rw [coeff_reducedSlashSeries_levelOne, PowerSeries.coeff_expand]
  simp only [PowerSeries.coeff_map, eq_intCast]

/-- The original cubed weight-four Eisenstein form, restricted to Gamma1. -/
def gammaOneEisensteinCube (N : ℕ) : ModularForm (Gamma1 N) 12 :=
  ModularNormPolynomial.restrict (Subgroup.map_le_range _ (Gamma1 N))
    ((ModularForm.E₄.pow 3).mcast (by norm_num))

theorem integralQExp_gammaOneEisensteinCube (N : ℕ) :
    IsIntegralQExp (gammaOneEisensteinCube N) (eisenstein4 ^ 3) := by
  change (eisenstein4 ^ 3).map (Int.castRingHom ℂ) =
    qExpansion 1 ((((ModularForm.E₄.pow 3).mcast (by norm_num)) : ModularForm 𝒮ℒ 12) : ℍ → ℂ)
  rw [ModularForm.qExpansion_mcast,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    qExpansion_E4_eq_map_eisenstein4, map_pow]

theorem jqModC_eq_discriminant_normalized (K : Type*) [Field K] :
    jqModC K = intSeriesC K (eisenstein4 ^ 3) / intSeriesC K discriminantSeries := by
  rw [eq_div_iff (intSeriesC_discriminant_ne_zero K)]
  rw [jqModC, discriminantSeries, intSeriesC, intSeriesC, jNum,
    mul_assoc, ← map_mul, ← map_mul,
    show eisenstein4 ^ 3 * dedekindEtaUnitInv * (PowerSeries.X * dedekindEtaUnit) =
      PowerSeries.X * eisenstein4 ^ 3 by
        rw [mul_comm PowerSeries.X dedekindEtaUnit, ← mul_assoc,
          mul_assoc (eisenstein4 ^ 3), mul_comm dedekindEtaUnitInv,
          dedekindEtaUnit_mul_inv, mul_one, mul_comm],
    map_mul, PowerSeries.map_X, map_mul, HahnSeries.ofPowerSeries_X,
    ← mul_assoc, HahnSeries.single_mul_single]
  simp

theorem jqModC_mem_normalizedGenerators (N : ℕ) (K : Type*) [Field K] :
    jqModC K ∈ normalizedGenerators N K := by
  rw [jqModC_eq_discriminant_normalized]
  simpa only [pow_one] using mem_normalizedGenerators (K := K) (r := 1)
    (gammaOneEisensteinCube N) (integralQExp_gammaOneEisensteinCube N) (by norm_num)

theorem normalizedSlashValue_jqModC (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    {K : Type*} [Field K] [CharP K ℓ] (φ : Zbar →+* K) (hN : (N : K) ≠ 0)
    (β : SL(2, ℤ)) : normalizedSlashValue N φ hN β (jqModC K) = qExpand K N (jqModC K) := by
  have he := normalizedSlashValue_eq N φ hN β ℓ (r := 1)
    (gammaOneEisensteinCube N) (integralQExp_gammaOneEisensteinCube N)
    (x := jqModC K) (by rw [pow_one, jqModC_eq_discriminant_normalized])
  have hE := ofPowerSeries_reducedSlashSeries_levelOne N φ hN β (by decide)
    (((ModularForm.E₄.pow 3).mcast (by norm_num)) : ModularForm 𝒮ℒ 12)
    (p := eisenstein4 ^ 3) (integralQExp_gammaOneEisensteinCube N)
  have hD := ofPowerSeries_reducedSlashSeries_levelOne N φ hN β (by decide)
    (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
    (p := discriminantSeries) (integralQExp_gammaOneDiscriminant N)
  rw [he, pow_one]
  exact (congrArg₂ (fun x y : LaurentSeries K => x / y) hE hD).trans (by
    rw [← map_div₀, ← jqModC_eq_discriminant_normalized])

theorem normalizedSlashValue_jqModC_transcendental (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime]
    {K : Type*} [Field K] [CharP K ℓ] (φ : Zbar →+* K) (hN : (N : K) ≠ 0)
    (β : SL(2, ℤ)) : Transcendental K (normalizedSlashValue N φ hN β (jqModC K)) := by
  rw [normalizedSlashValue_jqModC N ℓ φ hN β]
  exact IntegralJCoordinate.transcendental_qExpand_jqModC K N

end
end Dubon2026.SourceFunctionField.IntegralSlash
