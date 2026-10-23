import Dubon2026.SourceHassePolynomialDescent
import Dubon2026.SourceIntegralEisensteinReduction
import Mathlib.Data.ZMod.Basic

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime nonmembership. Taking the actual integral
Eisenstein series to the twelfth power permits the proved weight-12N
polynomial descent. The resulting integral polynomial has exact degree
ell - 1 and nonzero leading coefficient modulo ell. No Hasse input is assumed.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_starBank, hasse_input. Reuses the already checked
integral series, constant reduction and level-one polynomial descent. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane
open scoped MatrixGroups

theorem hasse_input {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ∃ (T : PowerSeries ℤ) (G : Polynomial ℤ),
      (∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) ∧ ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T
      ∧ G.natDegree = ℓ - 1 ∧ G.coeff (ℓ - 1) = PowerSeries.constantCoeff T
      ∧ HahnSeries.ofPowerSeries ℤ ℤ T
          = Polynomial.aeval (jqModC ℤ) G
            * (HahnSeries.single (1 : ℤ) (1 : ℤ)
                * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) ^ (ℓ - 1) := by
  have hk : 3 ≤ ℓ - 1 := by omega
  obtain ⟨T, hTmap, hTconst, hTdvd⟩ := eisInt_series hℓ5 hk
  have hnum0 : ¬ (ℓ : ℤ) ∣ (_root_.bernoulli (ℓ - 1)).num :=
    eisInt_not_dvd_num hℓ5

  have hmapZ : T.map (Int.castRingHom (ZMod ℓ))
      = PowerSeries.C (((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) := by
    rw [powerSeries_reduction_eq_constant (ZMod ℓ) ℓ T hTdvd, hTconst]
  have hmapZ12 : (T ^ 12).map (Int.castRingHom (ZMod ℓ))
      = PowerSeries.C ((((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) ^ 12) := by
    rw [map_pow, hmapZ, ← map_pow]
  have hnumZ : (((_root_.bernoulli (ℓ - 1)).num : ZMod ℓ)) ≠ 0 :=
    fun h => hnum0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h)

  have hdvd12 : ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ (T ^ 12).coeff m := by
    intro m hm
    have h1 := congrArg (fun u : PowerSeries (ZMod ℓ) => PowerSeries.coeff m u) hmapZ12
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_C] at h1
    rw [if_neg (by omega : ¬ m = 0)] at h1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1

  have hconst12 : PowerSeries.constantCoeff (T ^ 12) = (_root_.bernoulli (ℓ - 1)).num ^ 12 := by
    rw [map_pow, hTconst]
  have hnot12 : ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff (T ^ 12) := by
    rw [hconst12, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    exact pow_ne_zero 12 hnumZ

  have hw : ((12 : ℕ) : ℤ) * ((ℓ - 1 : ℕ) : ℤ) = 12 * ((ℓ - 1 : ℕ) : ℤ) := by norm_num
  have hT12 : (T ^ 12).map (Int.castRingHom ℂ)
      = UpperHalfPlane.qExpansion 1
          ⇑(ModularForm.mcast hw
              ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12)) := by
    have h1 : UpperHalfPlane.qExpansion 1
        ⇑(ModularForm.mcast hw
            ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12))
        = UpperHalfPlane.qExpansion 1
            ⇑((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12) := rfl
    rw [h1, ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
      ModularForm.IsGLPos.coe_smul,
      ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL, map_pow, hTmap]
  have h0 : PowerSeries.constantCoeff (T ^ 12) ≠ 0 := by
    rw [hconst12]
    intro h
    exact hnum0 ((pow_eq_zero_iff (by norm_num : (12 : ℕ) ≠ 0)).mp h ▸ dvd_zero _)
  obtain ⟨G, hGdeg, hGcoeff, hGid⟩ := hassePolyDescent
    (ModularForm.mcast hw ((((_root_.bernoulli (ℓ - 1)).num : ℂ) • ModularForm.E hk).pow 12))
    hT12 h0
  exact ⟨T ^ 12, G, hdvd12, hnot12, hGdeg, hGcoeff, hGid⟩


end
end Dubon2026.SourceFunctionField
