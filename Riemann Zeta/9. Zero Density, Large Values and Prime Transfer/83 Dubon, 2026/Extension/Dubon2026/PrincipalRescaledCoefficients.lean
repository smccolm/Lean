import Dubon2026.CuspUpperCongruence
import Dubon2026.PrincipalCuspOrbit

/-! # Actual coefficients in the principal-level rescaling used by the newform main lemma -/

namespace Dubon2026

open Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

noncomputable section

/-- Principal-level cusp coefficients use the genuine period-N cusp parameter. -/
def principalCuspCoefficients {N : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (n : ℕ) : ℂ :=
  (qExpansion N f).coeff n

/-- The actual principal-level Fourier series converges at every upper-half-plane point. -/
theorem principalCuspCoefficients_hasSum {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma N).map (mapGL ℝ)) k) (τ : ℍ) :
    HasSum (fun n => principalCuspCoefficients f n * Function.Periodic.qParam N τ ^ n) (f τ) := by
  have hp : (N : ℝ) ∈ ((Gamma N).map (mapGL ℝ)).strictPeriods := by simp
  simpa only [principalCuspCoefficients, smul_eq_mul] using UpperHalfPlane.hasSum_qExpansion
    (Nat.cast_pos.mpr (Nat.pos_of_neZero N))
    (SlashInvariantFormClass.periodic_comp_ofComplex f hp) f.holo'
    (ModularFormClass.bdd_at_infty f) τ

/-- Period-N coefficients uniquely determine the actual principal-level cusp form. -/
theorem principalCuspCoefficients_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (principalCuspCoefficients (N := N) (k := k)) := by
  intro f g h
  ext τ
  exact (principalCuspCoefficients_hasSum f τ).unique (h ▸ principalCuspCoefficients_hasSum g τ)

/-- Evaluation of each genuine principal-level Fourier coefficient is complex linear. -/
def principalCuspCoefficientLinear (N : ℕ) [NeZero N] (k : ℤ) (n : ℕ) :
    CuspForm ((Gamma N).map (mapGL ℝ)) k →ₗ[ℂ] ℂ where
  toFun f := principalCuspCoefficients f n
  map_add' f g := by
    change (qExpansion N (f + g)).coeff n = _
    rw [ModularForm.qExpansion_add (Nat.cast_pos.mpr (Nat.pos_of_neZero N)) (by simp), map_add]
    rfl
  map_smul' c f := by
    change (qExpansion N (c • f)).coeff n = _
    rw [ModularForm.qExpansion_smul (Nat.cast_pos.mpr (Nat.pos_of_neZero N)) (by simp),
      PowerSeries.coeff_smul]
    rfl

/-- The rescaled Gamma0 form is an actual principal-level cusp form, by restriction from Γ⁰(N). -/
def cuspRescaledPrincipal (N : ℕ) [NeZero N] (k : ℤ) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma N).map (mapGL ℝ)) k where
  toFun f := cuspRestrictSubgroup (Subgroup.map_mono (Gamma_le_GammaUpper N)) (cuspUpperRescale N k f)
  map_add' f g := by ext τ; exact DFunLike.congr_fun (map_add (cuspUpperRescale N k) f g) τ
  map_smul' c f := by ext τ; exact DFunLike.congr_fun (map_smul (cuspUpperRescale N k) c f) τ

/-- Pointwise rescaling is literally f(z/N). -/
theorem cuspRescaledPrincipal_apply (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (τ : ℍ) :
    cuspRescaledPrincipal N k f τ = f (heckeUpperPoint N 0 τ) :=
  cuspUpperRescale_apply N k f τ

/-- Rescaling the argument transforms the standard cusp parameter into the period-N parameter. -/
theorem qParam_heckeUpperPoint_zero (N : ℕ) [NeZero N] (τ : ℍ) :
    Function.Periodic.qParam 1 (heckeUpperPoint N 0 τ : ℍ) = Function.Periodic.qParam N τ := by
  unfold Function.Periodic.qParam
  congr 1
  change 2 * (Real.pi : ℂ) * Complex.I * (((τ : ℂ) + (0 : ℕ)) / N) / 1 = _
  push_cast
  ring1

/-- Rescaling preserves every original coefficient exactly, with the correct period-N parameter. -/
theorem cuspRescaledPrincipal_coeff (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (n : ℕ) :
    principalCuspCoefficients (cuspRescaledPrincipal N k f) n = cuspCoefficients f n := by
  have hs : ∀ τ : ℍ, HasSum (fun j => cuspCoefficients f j •
      Function.Periodic.qParam N τ ^ j) (cuspRescaledPrincipal N k f τ) := by
    intro τ
    rw [cuspRescaledPrincipal_apply]
    have h := cuspCoefficients_hasSum f (heckeUpperPoint N 0 τ)
    simpa only [qParam_heckeUpperPoint_zero, smul_eq_mul] using h
  exact (ModularFormClass.qExpansion_coeff_unique
    (Nat.cast_pos.mpr (Nat.pos_of_neZero N)) (by simp) hs n).symm

attribute [local instance] principalNormal
/-- The actual rescaled principal form is fixed by every upper-congruence matrix. -/
theorem cuspRescaledPrincipal_upper_fixed (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ)) (hγ : γ ∈ GammaUpper N) :
    normalCuspAction (Gamma N) k γ (cuspRescaledPrincipal N k f) = cuspRescaledPrincipal N k f := by
  apply DFunLike.coe_injective
  exact (cuspUpperRescale N k f).slash_action_eq' _
    ⟨γ⁻¹, (GammaUpper N).inv_mem hγ, rfl⟩

end
end Dubon2026
