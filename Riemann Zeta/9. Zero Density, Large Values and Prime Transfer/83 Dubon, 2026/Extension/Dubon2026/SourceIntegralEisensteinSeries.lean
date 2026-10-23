import Dubon2026.SourceIntegralEisensteinCoefficients

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> automorphy and residual association -> original Frobenius/inertia
-> modular-curve good reduction -> exact residue-field degree -> prime j
nonmembership. The integral Eisenstein series of weight ell - 1 supplies the
Hasse polynomial input with nonzero constant reduction. This file does not yet
construct that polynomial or prove unconditional prime nonmembership.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_StarBank_eisInt_series. Reuses the pinned Mathlib
von Staudt-Clausen and Eisenstein q-expansion theorems directly. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open scoped ArithmeticFunction.sigma
open Finset

theorem eisInt_series {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) :
    ∃ T : PowerSeries ℤ,
      T.map (Int.castRingHom ℂ)
        = ((bernoulli (ℓ - 1)).num : ℂ) • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))
      ∧ PowerSeries.constantCoeff T = (bernoulli (ℓ - 1)).num
      ∧ ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m := by
  classical
  refine ⟨PowerSeries.mk fun m => (eisInt_coeff hℓ5 hk m).choose,
    ?_, ?_, ?_⟩
  · ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul]
    exact (eisInt_coeff hℓ5 hk m).choose_spec.1.symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (eisInt_coeff hℓ5 hk 0).choose_spec.2.1 rfl
  · intro m hm
    rw [PowerSeries.coeff_mk]
    exact (eisInt_coeff hℓ5 hk m).choose_spec.2.2 hm


end
end Dubon2026.SourceFunctionField
