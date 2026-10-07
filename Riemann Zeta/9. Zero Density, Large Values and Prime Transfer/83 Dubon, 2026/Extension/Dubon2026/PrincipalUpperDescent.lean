import Dubon2026.PrincipalLowerProjection

/-! # Actual descent from upper-invariant principal forms to Gamma0 -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

noncomputable section
attribute [local instance] principalNormal

/-- The actual subspace fixed by the integral upper congruence group in the principal slash action. -/
def principalUpperInvariantSpace (N : ℕ) (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma N).map (mapGL ℝ)) k) :=
  Representation.invariants ((normalCuspAction (Gamma N) k).comp (GammaUpper N).subtype)

/-- A fixed principal form is genuinely a cusp form for the upper congruence group. -/
def principalUpperDescent (N : ℕ) [NeZero N] (k : ℤ) :
    principalUpperInvariantSpace N k →ₗ[ℂ] CuspForm ((GammaUpper N).map (mapGL ℝ)) k where
  toFun v := {
    toFun := v.val
    slash_action_eq' := by
      rintro γ ⟨δ, hδ, rfl⟩
      have hv := v.property ⟨δ⁻¹, (GammaUpper N).inv_mem hδ⟩
      change normalCuspAction (Gamma N) k δ⁻¹ v.val = v.val at hv
      have he := congrArg (fun f : CuspForm ((Gamma N).map (mapGL ℝ)) k => (f : ℍ → ℂ)) hv
      simpa only [normalCuspAction_apply, inv_inv] using he
    holo' := v.val.holo'
    zero_at_cusps' hc := by
      apply v.val.zero_at_cusps'
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
      exact hc.mono (Subgroup.map_le_range (mapGL ℝ) (GammaUpper N))
  }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Dilating an upper-level cusp form by N gives exactly the Gamma0(N) transformation group. -/
theorem Gamma0_le_conj_GammaUpper (N : ℕ) [NeZero N] :
    (Gamma0 N).map (mapGL ℝ) ≤
      ConjAct.toConjAct (levelRaiseMatrix N)⁻¹ • (GammaUpper N).map (mapGL ℝ) := by
  rintro g ⟨γ, hγ, rfl⟩
  have hd : (N : ℤ) ∣ γ.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (levelRaiseConjOfDvd N γ hd), ⟨_, ?_, rfl⟩, ?_⟩
  · change (((N : ℤ) * γ 0 1 : ℤ) : ZMod N) = 0
    simp
  · change (levelRaiseMatrix N)⁻¹ * mapGL ℝ (levelRaiseConjOfDvd N γ hd) *
      levelRaiseMatrix N = mapGL ℝ γ
    rw [mul_assoc, levelRaiseMatrix_mul_mapGL, inv_mul_cancel_left]

/-- The genuine linear cusp-form map F(z) ↦ F(Nz) from upper to lower congruence level N. -/
def upperCuspToGamma0 (N : ℕ) [NeZero N] (k : ℤ) :
    CuspForm ((GammaUpper N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun f := ((N : ℂ) ^ (1 - k)) •
    cuspRestrictSubgroup (Gamma0_le_conj_GammaUpper N) (CuspForm.translate f (levelRaiseMatrix N))
  map_add' f g := by
    ext τ
    change ((N : ℂ) ^ (1 - k)) • ((⇑(f + g) ∣[k] levelRaiseMatrix N) τ) =
      ((N : ℂ) ^ (1 - k)) • ((⇑f ∣[k] levelRaiseMatrix N) τ) +
        ((N : ℂ) ^ (1 - k)) • ((⇑g ∣[k] levelRaiseMatrix N) τ)
    simp only [CuspForm.coe_add, SlashAction.add_slash, Pi.add_apply, smul_add]
  map_smul' c f := by
    ext τ
    change ((N : ℂ) ^ (1 - k)) • ((⇑(c • f) ∣[k] levelRaiseMatrix N) τ) =
      c • (((N : ℂ) ^ (1 - k)) • ((⇑f ∣[k] levelRaiseMatrix N) τ))
    simp only [show (⇑(c • f) : ℍ → ℂ) = c • ⇑f from rfl,
      ModularForm.smul_slash, σ_levelRaiseMatrix N, ContinuousAlgEquiv.refl_apply,
      Pi.smul_apply, smul_eq_mul]
    ring1

/-- The linear descent of actual upper-invariant principal forms to Gamma0(N). -/
def principalUpperToGamma0 (N : ℕ) [NeZero N] (k : ℤ) :
    principalUpperInvariantSpace N k →ₗ[ℂ] CuspForm ((Gamma0 N).map (mapGL ℝ)) k :=
  (upperCuspToGamma0 N k).comp (principalUpperDescent N k)

/-- The descended form evaluates as exactly F(Nz). -/
theorem principalUpperToGamma0_apply (N : ℕ) [NeZero N] (k : ℤ)
    (v : principalUpperInvariantSpace N k) (τ : ℍ) :
    principalUpperToGamma0 N k v τ = v.val (levelRaiseMatrix N • τ) :=
  levelRaiseFun_apply N k v.val τ

/-- Rescaling the descended actual Gamma0 form recovers the original principal form. -/
theorem cuspRescaledPrincipal_upperToGamma0 (N : ℕ) [NeZero N] (k : ℤ)
    (v : principalUpperInvariantSpace N k) :
    cuspRescaledPrincipal N k (principalUpperToGamma0 N k v) = v.val := by
  ext τ
  rw [cuspRescaledPrincipal_apply, principalUpperToGamma0_apply]
  congr 1
  apply UpperHalfPlane.ext
  simp only [coe_levelRaiseMatrix_smul, heckeUpperPoint, Nat.cast_zero, add_zero]
  exact mul_div_cancel₀ _ (show (N : ℂ) ≠ 0 from Nat.cast_ne_zero.mpr (NeZero.ne N))

/-- The descended period-one coefficients are exactly the original principal period-N coefficients. -/
theorem principalUpperToGamma0_coeff (N : ℕ) [NeZero N] (k : ℤ)
    (v : principalUpperInvariantSpace N k) (n : ℕ) :
    cuspCoefficients (principalUpperToGamma0 N k v) n = principalCuspCoefficients v.val n := by
  have he := congrArg (fun g => principalCuspCoefficients g n) (cuspRescaledPrincipal_upperToGamma0 N k v)
  dsimp only at he
  rwa [cuspRescaledPrincipal_coeff] at he

end
end Dubon2026
