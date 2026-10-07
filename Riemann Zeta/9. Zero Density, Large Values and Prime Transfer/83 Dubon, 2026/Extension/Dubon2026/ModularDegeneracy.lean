/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Minimal adaptation of the actual degeneracy maps from LevelRaise.lean,
LeanModularForms 7c41b9b1747d47298f76bdb51f07031087702198.
The source and target groups here are Gamma0, and arbitrary deeper levels
are allowed through the explicit divisibility condition d*M | N.
-/
import Dubon2026.CuspCoefficients

/-! # Actual cusp-form degeneracy maps, including ordinary inclusion -/

namespace Dubon2026

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm Pointwise

noncomputable section

/-- The level-raising matrix `α_d = [[d, 0], [0, 1]]` in `GL(2, ℝ)`. -/
def levelRaiseMatrix (d : ℕ) [NeZero d] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(d : ℝ), 0; 0, 1]
    (by simp [Matrix.det_fin_two, Nat.cast_ne_zero.mpr (NeZero.ne d)])

/-- The level-raising operator at the function level: `(ι_d f)(τ) = f(d·τ)`,
realised as `ι_d f = d^{1-k} · (f ∣[k] α_d)` (the `d^{1-k}` scalar cancels the
`det^{k-1}` factor in the slash action). -/
def levelRaiseFun (d : ℕ) [NeZero d] (k : ℤ) (f : UpperHalfPlane → ℂ) :
    UpperHalfPlane → ℂ :=
  ((d : ℂ) ^ (1 - k)) • (f ∣[k] levelRaiseMatrix d)

/-- The denominator of `levelRaiseMatrix l` at any point is `1` (bottom row
of `α_l` is `(0, 1)`). -/
lemma denom_levelRaiseMatrix (l : ℕ) [NeZero l] (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (levelRaiseMatrix l) (↑τ : ℂ) = 1 := by
  simp [UpperHalfPlane.denom, levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The determinant of `levelRaiseMatrix l` is positive (it equals `l > 0`). -/
lemma levelRaiseMatrix_det_pos (l : ℕ) [NeZero l] :
    (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix l) : ℝ) := by
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two,
    Nat.cast_pos.mpr (Nat.pos_of_neZero l)]

/-- The real absolute determinant of `levelRaiseMatrix l` is `l`. -/
lemma abs_levelRaiseMatrix_det_val (l : ℕ) [NeZero l] :
    |((Matrix.GeneralLinearGroup.det (levelRaiseMatrix l)) : ℝ)| = (l : ℝ) := by
  rw [abs_of_pos (levelRaiseMatrix_det_pos l)]
  simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two]

/-- The conjugation factor `σ` for `levelRaiseMatrix l` is the identity
(positive determinant). -/
lemma σ_levelRaiseMatrix (l : ℕ) [NeZero l] :
    UpperHalfPlane.σ (levelRaiseMatrix l) = ContinuousAlgEquiv.refl ℝ ℂ := by
  unfold UpperHalfPlane.σ; rw [if_pos (levelRaiseMatrix_det_pos l)]

/-- For `γ ∈ Γ₀(d*M)`, the entry `γ.val 1 0` is divisible by `d`. -/
lemma Gamma0_dmul_lower_left_dvd (d M : ℕ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 (d * M)) :
    (d : ℤ) ∣ γ.val 1 0 :=
  dvd_trans ⟨M, by push_cast; ring⟩
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))

/-- Construction of `δ_d γ δ_d⁻¹` as an explicit `SL(2, ℤ)` element when
`d ∣ γ.val 1 0`. The formula `[[a, d*b], [c/d, e]]` is integer by hypothesis. -/
noncomputable def levelRaiseConjOfDvd (d : ℕ) (γ : SL(2, ℤ))
    (hdvd : (d : ℤ) ∣ γ.val 1 0) : SL(2, ℤ) :=
  ⟨!![γ.val 0 0, d * γ.val 0 1; γ.val 1 0 / d, γ.val 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination (Matrix.det_fin_two γ.val).symm.trans γ.property -
      γ.val 0 1 * Int.ediv_mul_cancel hdvd⟩

private lemma natCast_dvd_ediv_of_mul_dvd {d M : ℕ} [NeZero d] {c : ℤ}
    (h : ((d * M : ℕ) : ℤ) ∣ c) : (M : ℤ) ∣ c / d := by
  obtain ⟨j, hj⟩ := h
  refine ⟨j, ?_⟩
  rw [hj]
  push_cast
  rw [mul_assoc, Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne d))]

/-- The conjugated matrix is in `Γ₀(M)` when `γ ∈ Γ₀(d*M)`. The (1,0) entry of
`δ_d γ δ_d⁻¹` is `c/d`, which is divisible by `M` because `c` is divisible by `d*M`. -/
lemma levelRaiseConjOfDvd_mem_Gamma0 (d M : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hγ : γ ∈ Gamma0 (d * M)) :
    levelRaiseConjOfDvd d γ (Gamma0_dmul_lower_left_dvd d M γ hγ) ∈ Gamma0 M := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact natCast_dvd_ediv_of_mul_dvd
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ))
/-- The matrix conjugation identity (in `GL(2, ℝ)`) for `levelRaiseConjOfDvd`:
`α_d * γ * α_d⁻¹ = (levelRaiseConjOfDvd d γ hdvd : GL₂(ℝ))`, equivalently
`levelRaiseMatrix d * mapGL ℝ γ =
mapGL ℝ (levelRaiseConjOfDvd d γ hdvd) * levelRaiseMatrix d`. -/
lemma levelRaiseMatrix_mul_mapGL (d : ℕ) [NeZero d] (γ : SL(2, ℤ))
    (hdvd : (d : ℤ) ∣ γ.val 1 0) :
    mapGL ℝ (levelRaiseConjOfDvd d γ hdvd) * levelRaiseMatrix d =
      levelRaiseMatrix d * mapGL ℝ γ := by
  have hdvd_real : ((d : ℕ) : ℝ) * (((γ.val 1 0 / (d : ℤ)) : ℤ) : ℝ) =
      ((γ.val 1 0 : ℤ) : ℝ) := by
    rw [mul_comm, ← Int.cast_natCast (R := ℝ), ← Int.cast_mul, Int.ediv_mul_cancel hdvd]
  ext i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [levelRaiseMatrix, levelRaiseConjOfDvd, mul_comm, hdvd_real]


/-- Restrict a genuine cusp form along a subgroup inclusion. -/
def cuspRestrictSubgroup {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (h : Γ' ≤ Γ) (f : CuspForm Γ k) : CuspForm Γ' k where
  toFun := f.toFun
  slash_action_eq' γ hγ := f.slash_action_eq' γ (h hγ)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

/-- Conjugating the deeper congruence subgroup gives the source invariance. -/
theorem Gamma0_dmul_le_conj (M : ℕ) (d : ℕ) [NeZero d] :
    (Gamma0 (d * M)).map (mapGL ℝ) ≤
      ConjAct.toConjAct (levelRaiseMatrix d)⁻¹ • (Gamma0 M).map (mapGL ℝ) := by
  intro g hg
  obtain ⟨γ, hγ_mem, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨mapGL ℝ (levelRaiseConjOfDvd d γ (Gamma0_dmul_lower_left_dvd d M γ hγ_mem)),
    Subgroup.mem_map.mpr ⟨_, levelRaiseConjOfDvd_mem_Gamma0 d M γ hγ_mem, rfl⟩, ?_⟩
  rw [ConjAct.toConjAct_smul, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact levelRaiseMatrix_mul_mapGL d γ (Gamma0_dmul_lower_left_dvd d M γ hγ_mem)

/-- The actual linear degeneracy map f(z) ↦ f(dz), initially at level d*M. -/
def cuspLevelRaise (M d : ℕ) [NeZero d] (k : ℤ) :
    CuspForm ((Gamma0 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma0 (d * M)).map (mapGL ℝ)) k where
  toFun f := ((d : ℂ) ^ (1 - k)) •
    cuspRestrictSubgroup (Gamma0_dmul_le_conj M d) (CuspForm.translate f (levelRaiseMatrix d))
  map_add' f₁ f₂ := by
    ext z
    change ((d : ℂ) ^ (1 - k)) • ((⇑(f₁ + f₂) ∣[k] levelRaiseMatrix d) z) =
      ((d : ℂ) ^ (1 - k)) • ((⇑f₁ ∣[k] levelRaiseMatrix d) z) +
      ((d : ℂ) ^ (1 - k)) • ((⇑f₂ ∣[k] levelRaiseMatrix d) z)
    simp only [CuspForm.coe_add, SlashAction.add_slash, Pi.add_apply, smul_add]
  map_smul' c f := by
    ext z
    change ((d : ℂ) ^ (1 - k)) • ((⇑(c • f) ∣[k] levelRaiseMatrix d) z) =
      c • (((d : ℂ) ^ (1 - k)) • ((⇑f ∣[k] levelRaiseMatrix d) z))
    simp only [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
      ModularForm.smul_slash, σ_levelRaiseMatrix d, ContinuousAlgEquiv.refl_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

/-- **Pointwise evaluation of the level-raise operator.** `levelRaiseFun l k f`
evaluates to `f` at the scaled point `α_l • τ`; the `l^{1-k}` prefactor exactly
cancels the `l^{k-1}` factor from the slash action. -/
lemma levelRaiseFun_apply (l : ℕ) [NeZero l] (k : ℤ) (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    levelRaiseFun l k f τ = f ((levelRaiseMatrix l) • τ) := by
  change ((l : ℂ) ^ (1 - k)) • ((f ∣[k] levelRaiseMatrix l) τ) = _
  rw [ModularForm.slash_apply, σ_levelRaiseMatrix, ContinuousAlgEquiv.refl_apply,
    abs_levelRaiseMatrix_det_val, denom_levelRaiseMatrix, one_zpow, mul_one,
    smul_eq_mul, Complex.ofReal_natCast, mul_comm (f _), ← mul_assoc,
    ← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne l))]
  norm_num

/-- The action of `levelRaiseMatrix l = [[l, 0], [0, 1]]` on `ℍ` is the diagonal
scaling `(α_l • τ : ℂ) = l · (↑τ : ℂ)`. -/
lemma coe_levelRaiseMatrix_smul (l : ℕ) [NeZero l] (τ : UpperHalfPlane) :
    ((levelRaiseMatrix l • τ : UpperHalfPlane) : ℂ) = (l : ℂ) * (↑τ : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (levelRaiseMatrix_det_pos l)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, levelRaiseMatrix,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
/-- **Surjectivity of `α_l • _` on `ℍ`.** For every `τ' : ℍ` there exists
`τ : ℍ` with `levelRaiseMatrix l • τ = τ'`; the explicit witness is
`τ = UpperHalfPlane.mk (↑τ' / l)` (with positive imaginary part since
`τ'.im > 0` and `l > 0`). -/
lemma exists_levelRaiseMatrix_smul_eq (l : ℕ) [NeZero l] (τ' : UpperHalfPlane) :
    ∃ τ : UpperHalfPlane, levelRaiseMatrix l • τ = τ' := by
  refine ⟨UpperHalfPlane.mk (↑τ' / (l : ℂ)) ?_, ?_⟩
  · rw [Complex.div_natCast_im]
    exact div_pos τ'.im_pos (Nat.cast_pos.mpr (Nat.pos_of_neZero l))
  · apply UpperHalfPlane.ext
    rw [coe_levelRaiseMatrix_smul, UpperHalfPlane.coe_mk,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne l))]

/-- **Injectivity of `levelRaiseFun l k`.** If two functions `f₁, f₂ : ℍ → ℂ`
have the same level-raise, they are equal. -/
lemma levelRaiseFun_injective (l : ℕ) [NeZero l] (k : ℤ) :
    Function.Injective (levelRaiseFun (k := k) l) := by
  intro f₁ f₂ heq
  funext τ'
  obtain ⟨τ, hτ⟩ := exists_levelRaiseMatrix_smul_eq l τ'
  simpa only [levelRaiseFun_apply, hτ] using congr_fun heq τ


/-- The level raise evaluates to f(dz), without a residual weight factor. -/
theorem cuspLevelRaise_apply (M d : ℕ) [NeZero d] (k : ℤ)
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) (τ : ℍ) :
    cuspLevelRaise M d k f τ = f (levelRaiseMatrix d • τ) :=
  levelRaiseFun_apply d k f τ

/-- Divisibility of levels gives inclusion of the actual congruence subgroups. -/
theorem Gamma0_le_of_dvd {M N : ℕ} (h : M ∣ N) : Gamma0 N ≤ Gamma0 M := by
  intro γ hγ
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hγ

/-- Ordinary inclusion f(z) ↦ f(z) between cusp spaces of dividing levels. -/
def cuspLevelInclusion {M N : ℕ} (h : M ∣ N) (k : ℤ) :
    CuspForm ((Gamma0 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k where
  toFun := cuspRestrictSubgroup (Subgroup.map_mono (Gamma0_le_of_dvd h))
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Inclusion leaves both the function and its actual Fourier coefficients unchanged. -/
theorem cuspLevelInclusion_coeff {M N : ℕ} (h : M ∣ N) {k : ℤ}
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) (n : ℕ) :
    cuspCoefficients (cuspLevelInclusion h k f) n = cuspCoefficients f n := rfl

/-- All classical degeneracy maps into level N; d=1 is deliberately included. -/
def cuspDegeneracyMap {M N : ℕ} (d : ℕ) [NeZero d] (h : d * M ∣ N) (k : ℤ) :
    CuspForm ((Gamma0 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma0 N).map (mapGL ℝ)) k :=
  (cuspLevelInclusion h k).comp (cuspLevelRaise M d k)

/-- Pointwise meaning of every degeneracy map, including ordinary inclusion. -/
theorem cuspDegeneracyMap_apply {M N : ℕ} (d : ℕ) [NeZero d] (h : d * M ∣ N) {k : ℤ}
    (f : CuspForm ((Gamma0 M).map (mapGL ℝ)) k) (τ : ℍ) :
    cuspDegeneracyMap d h k f τ = f (levelRaiseMatrix d • τ) :=
  cuspLevelRaise_apply M d k f τ

/-- Each degeneracy map is injective on the actual cusp forms. -/
theorem cuspDegeneracyMap_injective {M N : ℕ} (d : ℕ) [NeZero d]
    (h : d * M ∣ N) (k : ℤ) : Function.Injective (cuspDegeneracyMap d h k) := by
  intro f g hfg
  apply DFunLike.ext
  intro τ'
  obtain ⟨τ, rfl⟩ := exists_levelRaiseMatrix_smul_eq d τ'
  simpa only [cuspDegeneracyMap_apply] using DFunLike.congr_fun hfg τ

/-- The d=1 degeneracy map is the ordinary lower-level inclusion. -/
theorem cuspDegeneracyMap_one {M N : ℕ} (h : 1 * M ∣ N) (k : ℤ) :
    cuspDegeneracyMap 1 h k = cuspLevelInclusion (by simpa using h) k := by
  ext f τ
  rw [cuspDegeneracyMap_apply]
  change f (levelRaiseMatrix 1 • τ) = f τ
  congr 1
  apply UpperHalfPlane.ext
  simp [coe_levelRaiseMatrix_smul]

end
end Dubon2026
