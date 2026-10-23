import Dubon2026.SourceIntegralEisensteinSeries
import Mathlib.Algebra.CharP.Basic

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> exact
residue-field degree -> prime j nonmembership. The actual integral Eisenstein
series reduces to its nonzero constant in characteristic ell. This supplies
the arithmetic input to Hasse-polynomial descent, not the descent itself. -/
namespace Dubon2026.SourceFunctionField
noncomputable section

theorem powerSeries_reduction_eq_constant (K : Type*) [CommRing K]
    (ℓ : ℕ) [CharP K ℓ] (T : PowerSeries ℤ)
    (hT : ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) :
    T.map (Int.castRingHom K) = PowerSeries.C ((PowerSeries.constantCoeff T : ℤ) : K) := by
  ext m
  rw [PowerSeries.coeff_map]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_C,
      Int.coe_castRingHom]
  · rw [PowerSeries.coeff_C, if_neg hm.ne']
    exact (CharP.intCast_eq_zero_iff K ℓ _).2 (hT m hm)

theorem eisInt_nonzero_constant_reduction (K : Type*) [CommRing K]
    {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (hℓ5 : 5 ≤ ℓ) :
    ∃ T : PowerSeries ℤ,
      T.map (Int.castRingHom ℂ) = ((bernoulli (ℓ - 1)).num : ℂ) •
        UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E (show 3 ≤ ℓ - 1 by omega))) ∧
      PowerSeries.constantCoeff T = (bernoulli (ℓ - 1)).num ∧
      T.map (Int.castRingHom K) = PowerSeries.C ((bernoulli (ℓ - 1)).num : K) ∧
      ((bernoulli (ℓ - 1)).num : K) ≠ 0 := by
  obtain ⟨T, hT, h0, hdiv⟩ := eisInt_series hℓ5 (show 3 ≤ ℓ - 1 by omega)
  refine ⟨T, hT, h0, ?_, ?_⟩
  · rw [powerSeries_reduction_eq_constant K ℓ T hdiv, h0]
  · exact fun h => eisInt_not_dvd_num hℓ5 ((CharP.intCast_eq_zero_iff K ℓ _).1 h)

end
end Dubon2026.SourceFunctionField
