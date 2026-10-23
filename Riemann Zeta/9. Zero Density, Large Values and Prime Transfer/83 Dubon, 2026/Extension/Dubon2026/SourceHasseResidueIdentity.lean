import Dubon2026.SourceSmallCharacteristicHasse
import Dubon2026.SourceHasseIntegralInput

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership. The literal integral Hasse
identity is transported to the residue field, and its proved nonzero leading
coefficient normalizes the identity to one. Characteristics two and three use
the actual E4 coefficient congruence. No Hasse polynomial input is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_starK. The existing coefficient map replaces a new
Laurent ring homomorphism; the integral Hasse input is proved locally. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open HahnSeries PowerSeries

theorem starK_of_240 (K : Type*) [Field K] (h240 : (240 : K) = 0) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by
  refine ⟨1, le_refl 1, ?_, Polynomial.X, Polynomial.natDegree_X, ?_⟩
  · exact_mod_cast one_ne_zero (α := K)
  · rw [Polynomial.aeval_X, pow_one]
    exact jqModC_mul_etaBlock_of_240 h240

theorem starK (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
 :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by
  have hℓp : ℓ.Prime := Fact.out
  rcases lt_or_ge ℓ 5 with hℓ5 | hℓ5
  ·
    have hℓdvd : ℓ ∣ 240 := by
      interval_cases ℓ <;> first | decide | exact absurd hℓp (by decide)
    exact starK_of_240 K ((CharP.cast_eq_zero_iff K ℓ 240).mpr hℓdvd)
  ·
    obtain ⟨T, G₀, hTdvd, hTconst, hGdeg, hGcoeff, hId⟩ := hasse_input hℓ5
    set cT := PowerSeries.constantCoeff T with hcTdef
    have hcTK : ((cT : ℤ) : K) ≠ 0 := fun h =>
      hTconst ((CharP.intCast_eq_zero_iff K ℓ cT).mp h)

    have hmap := congrArg (coeffMap (Int.castRingHom K)) hId
    rw [map_mul, map_pow, coeffMap_int_aeval_jqModC, coeffMap_etaBlock,
      coeffMap_ofPowerSeries, powerSeries_reduction_eq_constant K ℓ T hTdvd,
      HahnSeries.ofPowerSeries_C] at hmap

    refine ⟨ℓ - 1, by omega, ?_,
      Polynomial.C (((cT : ℤ) : K)⁻¹) * G₀.map (Int.castRingHom K), ?_, ?_⟩
    ·
      have h1 : (1 : ℕ) ≤ ℓ := hℓp.one_lt.le
      have : ((ℓ - 1 : ℕ) : K) = (ℓ : K) - 1 := by exact_mod_cast Nat.cast_sub h1
      rw [this, CharP.cast_eq_zero K ℓ, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    ·
      have hdegK : (G₀.map (Int.castRingHom K)).natDegree = ℓ - 1 := by
        refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_ |>.trans hGdeg
        rw [Polynomial.leadingCoeff, hGdeg, hGcoeff]; simpa using hcTK
      rw [Polynomial.natDegree_C_mul (inv_ne_zero hcTK), hdegK]
    ·
      rw [map_mul (Polynomial.aeval (jqModC K)), Polynomial.aeval_C, mul_assoc, ← hmap,
        ← hcTdef, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
        HahnSeries.ofPowerSeries_C, ← map_mul, inv_mul_cancel₀ hcTK, map_one]


end
end Dubon2026.SourceFunctionField
