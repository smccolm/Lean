import Dubon2026.FrickeMatrices

/-! # The actual Fricke endomorphism of the Gamma0 cusp space -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

/-- Integral conjugation by W_N, using the actual level divisibility of the lower-left entry. -/
def frickeConjugate (N : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) : SL(2, ℤ) :=
  ⟨!![γ 1 1, -(γ 1 0 / N); -(N : ℤ) * γ 0 1, γ 0 0], by
    have hd : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
    rw [Matrix.det_fin_two_of]
    linear_combination (Matrix.det_fin_two γ.val).symm.trans γ.property -
      γ 0 1 * Int.ediv_mul_cancel hd⟩

/-- The Fricke conjugate remains in the same actual Gamma0 group. -/
theorem frickeConjugate_mem (N : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    frickeConjugate N γ hγ ∈ Gamma0 N := by
  rw [Gamma0_mem]
  change (((-(N : ℤ) * γ 0 1 : ℤ)) : ZMod N) = 0
  simp

/-- Exact real matrix identity for the integral Fricke conjugate. -/
theorem frickeConjugate_identity (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    mapGL ℝ (frickeConjugate N γ hγ) * frickeMatrix N = frickeMatrix N * mapGL ℝ γ := by
  have hd : (N : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  have hr := congrArg (fun z : ℤ => (z : ℝ)) (Int.ediv_mul_cancel hd)
  push_cast at hr
  ext i j
  simp only [GeneralLinearGroup.coe_mul, frickeMatrix_val, mapGL_coe_matrix,
    frickeConjugate, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp <;> nlinarith [hr]

/-- W_N transports the actual same-level invariance group back into itself. -/
theorem Gamma0_le_conj_fricke (N : ℕ) [NeZero N] :
    (Gamma0 N).map (mapGL ℝ) ≤
      ConjAct.toConjAct (frickeMatrix N)⁻¹ • (Gamma0 N).map (mapGL ℝ) := by
  rintro g ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (frickeConjugate N γ hγ), ⟨_, frickeConjugate_mem N γ hγ, rfl⟩, ?_⟩
  rw [ConjAct.toConjAct_smul, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact frickeConjugate_identity N γ hγ

/-- The actual determinant-normalized Fricke map on genuine cusp forms. -/
def cuspFricke (N : ℕ) [NeZero N] (k : ℤ) :
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun f := cuspRestrictSubgroup (Gamma0_le_conj_fricke N) (CuspForm.translate f (frickeMatrix N))
  map_add' f g := by
    ext τ
    change ((⇑(f + g) ∣[k] frickeMatrix N) τ) = _
    simp only [CuspForm.coe_add, SlashAction.add_slash, Pi.add_apply]
    rfl
  map_smul' c f := by
    ext τ
    change (((c • ⇑f) ∣[k] frickeMatrix N) τ) = c • ((⇑f ∣[k] frickeMatrix N) τ)
    rw [ModularForm.smul_slash]
    have hσ : UpperHalfPlane.σ (frickeMatrix N) = ContinuousAlgEquiv.refl ℝ ℂ := by
      unfold UpperHalfPlane.σ
      rw [if_pos (frickeMatrix_det_pos N)]
    rw [hσ, ContinuousAlgEquiv.refl_apply]
    rfl

/-- The bundled Fricke endomorphism is the literal slash transform. -/
theorem cuspFricke_apply (N : ℕ) [NeZero N] (k : ℤ)
    (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (τ : ℍ) :
    cuspFricke N k f τ = ((f : ℍ → ℂ) ∣[k] frickeMatrix N) τ := rfl

/-- At level one, the Fricke map is the identity on actual cusp forms. -/
theorem cuspFricke_one (k : ℤ) : cuspFricke 1 k = 1 := by
  apply LinearMap.ext
  intro f
  ext τ
  rw [cuspFricke_apply]
  have hlevel : levelRaiseMatrix 1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [levelRaiseMatrix, GeneralLinearGroup.mkOfDetNeZero]
  rw [frickeMatrix, hlevel, mul_one]
  exact congr_fun (f.slash_action_eq' _ ⟨ModularGroup.S, by change ModularGroup.S ∈ Gamma0 1; rw [Gamma0_mem]; exact Subsingleton.elim _ _, rfl⟩) τ

end
end Dubon2026
