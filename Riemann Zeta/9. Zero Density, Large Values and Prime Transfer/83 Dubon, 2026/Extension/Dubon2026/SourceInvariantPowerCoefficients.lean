import Dubon2026.SourceRealizedPowerSeries

/-! DUB-17/18 -> cusp-form lower dimension bound -> regular differential
realization -> original finite function-field extension -> modular polynomial
relations -> rational coefficient descent. This selects the literal Laurent
principal-part removal and the actual analytic realization argument, reusing
pinned weight-zero constancy and q-expansion coefficient uniqueness. No
polynomial relation or coefficient descent is postulated.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_coeff_eq_zero_of_hasSum_of_slash_invariant.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane Complex Filter Topology Function Polynomial
open scoped MatrixGroups ModularForm
local notation "𝕢" => Function.Periodic.qParam

theorem coeff_eq_zero_of_hasSum_of_slash_invariant {F : UpperHalfPlane → ℂ} {c : ℕ → ℂ} (hF : ∀ τ : UpperHalfPlane, HasSum (fun m : ℕ => c m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (hinv : ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane), F (γ • τ) = F τ) {m : ℕ} (hm : m ≠ 0) : c m = 0 := by
  have hslash : ∀ γ : SL(2, ℤ), F ∣[(0 : ℤ)] γ = F := fun γ => by
    funext τ
    rw [ModularForm.SL_slash_apply, hinv, neg_zero, zpow_zero, mul_one]
  let f : ModularForm 𝒮ℒ 0 :=
    { toFun := F
      slash_action_eq' := fun A hA => by
        obtain ⟨γ, rfl⟩ := hA
        exact hslash γ
      holo' := Realized.mdifferentiable one_pos hF
      bdd_at_cusps' := fun {cusp} hc => by
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hslash γ]
        exact Realized.isBoundedAtImInfty one_pos hF }
  obtain ⟨κ, hκ⟩ := ModularForm.eq_const_of_weight_zero f
  have hFκ : ∀ τ : ℍ, F τ = κ := fun τ => by
    exact congr_fun hκ τ

  have hF' : ∀ τ : ℍ, HasSum (fun m : ℕ => (Pi.single (M := fun _ => ℂ) 0 κ m) * 𝕢 1 (τ : ℂ) ^ m) (F τ) := by
    intro τ
    rw [hFκ τ]
    have := hasSum_ite_eq 0 κ
    refine this.congr_fun fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · simp [hn]
  have hc := ModularFormClass.qExpansion_coeff_unique one_pos
    one_mem_strictPeriods_SL (f := f)
    (fun τ => by simpa only [smul_eq_mul] using hF τ) m
  have hd := ModularFormClass.qExpansion_coeff_unique one_pos
    one_mem_strictPeriods_SL (f := f)
    (fun τ => by simpa only [smul_eq_mul] using hF' τ) m
  rw [hc, ← hd, Pi.single_apply, if_neg hm]

end
end Dubon2026.SourceFunctionField
