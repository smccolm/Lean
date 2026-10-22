import Dubon2026.SourceStabilizerMeromorphicOrder

/-! DUB-17/18 -> original torsion cardinality -> elliptic place charts.
The explicit coordinate centered at an upper-half-plane point conjugates
its actual modular stabilizer to multiplication. Its inverse is analytic
with nonzero derivative. This supplies the local coordinate for descent
through the ramification power, using the existing denominator character.
-/
namespace Dubon2026.SourceFunctionField.EllipticCoordinate
noncomputable section
open UpperHalfPlane Filter
open scoped Topology MatrixGroups ComplexConjugate

theorem upper_ne_conj (z τ : ℍ) : (z : ℂ) ≠ conj (τ : ℂ) := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  change z.im = -τ.im at hi
  linarith [z.im_pos, τ.im_pos]

/-- The genuine complex coordinate centered at the given upper-half-plane point. -/
def coord (τ : ℍ) (z : ℂ) : ℂ := (z - τ) / (z - conj (τ : ℂ))

/-- The rational inverse of the centered complex coordinate. -/
def param (τ : ℍ) (u : ℂ) : ℂ := ((τ : ℂ) - u * conj (τ : ℂ)) / (1 - u)

theorem param_zero (τ : ℍ) : param τ 0 = τ := by simp [param]

theorem param_sub_conj (τ : ℍ) {u : ℂ} (hu : u ≠ 1) :
    param τ u - conj (τ : ℂ) = ((τ : ℂ) - conj (τ : ℂ)) / (1 - u) := by
  dsimp only [param]
  field_simp [sub_ne_zero.mpr hu.symm]
  ring

theorem coord_param (τ : ℍ) {u : ℂ} (hu : u ≠ 1) : coord τ (param τ u) = u := by
  have hd : (τ : ℂ) - conj (τ : ℂ) ≠ 0 := sub_ne_zero.mpr (upper_ne_conj τ τ)
  have he : (1 : ℂ) - u ≠ 0 := sub_ne_zero.mpr hu.symm
  unfold coord
  rw [param_sub_conj τ hu]
  dsimp only [param]
  field_simp
  ring

theorem param_coord (τ : ℍ) (z : ℍ) : param τ (coord τ z) = z := by
  have hz : (z : ℂ) - conj (τ : ℂ) ≠ 0 := sub_ne_zero.mpr (upper_ne_conj z τ)
  have hd : (τ : ℂ) - conj (τ : ℂ) ≠ 0 := sub_ne_zero.mpr (upper_ne_conj τ τ)
  have he : 1 - coord τ z = ((τ : ℂ) - conj (τ : ℂ)) / ((z : ℂ) - conj (τ : ℂ)) := by
    dsimp only [coord]
    field_simp
    ring
  unfold param
  rw [he]
  dsimp only [coord]
  field_simp
  ring

theorem analyticAt_param (τ : ℍ) : AnalyticAt ℂ (param τ) 0 := by
  unfold param
  exact (analyticAt_const.sub (analyticAt_id.mul analyticAt_const)).div
    (analyticAt_const.sub analyticAt_id) (by norm_num)

theorem hasDerivAt_param (τ : ℍ) :
    HasDerivAt (param τ) ((τ : ℂ) - conj (τ : ℂ)) 0 := by
  have h := ((hasDerivAt_const (0 : ℂ) (τ : ℂ)).sub
    ((hasDerivAt_id 0).mul_const (conj (τ : ℂ)))).div
      ((hasDerivAt_const (0 : ℂ) (1 : ℂ)).sub (hasDerivAt_id 0)) (by norm_num)
  convert h using 1
  simp
  ring

theorem deriv_param_ne_zero (τ : ℍ) : deriv (param τ) 0 ≠ 0 := by
  rw [(hasDerivAt_param τ).deriv]
  exact sub_ne_zero.mpr (upper_ne_conj τ τ)

theorem param_im_pos_eventually (τ : ℍ) : ∀ᶠ u in 𝓝 (0 : ℂ), 0 < (param τ u).im := by
  have h := (Complex.continuous_im.continuousAt.comp (analyticAt_param τ).continuousAt).tendsto
  apply h.eventually
  apply Ioi_mem_nhds
  simpa only [Function.comp_apply, param_zero] using τ.im_pos

private theorem conj_denom (γ : SL(2, ℤ)) (z : ℂ) :
    conj (denom (γ : GL (Fin 2) ℝ) z) = denom (γ : GL (Fin 2) ℝ) (conj z) := by
  simp [denom]

private theorem conj_moeb (γ : SL(2, ℤ)) (z : ℂ) :
    conj (SubgroupStabilizer.moeb γ z) = SubgroupStabilizer.moeb γ (conj z) := by
  simp [SubgroupStabilizer.moeb, num, denom]

theorem coord_smul (τ : ℍ) (γ : SL(2, ℤ)) (hγ : γ • τ = τ) (z : ℍ) :
    coord τ ((γ • z : ℍ) : ℂ) =
      (conj (denom (γ : GL (Fin 2) ℝ) τ) / denom (γ : GL (Fin 2) ℝ) τ) * coord τ z := by
  have hz := denom_ne_zero (γ : GL (Fin 2) ℝ) z
  have hτ := denom_ne_zero (γ : GL (Fin 2) ℝ) τ
  have hcz : denom (γ : GL (Fin 2) ℝ) (conj (z : ℂ)) ≠ 0 := by
    rw [← conj_denom]
    exact (map_ne_zero (Complex.conjAe.toRingHom)).mpr hz
  have h1 := SubgroupStabilizer.moeb_sub γ τ hγ (z : ℂ) hz
  have h2 := congrArg conj (SubgroupStabilizer.moeb_sub γ τ hγ (conj (z : ℂ)) hcz)
  simp only [map_sub, map_div₀, map_mul, conj_moeb, conj_denom,
    Complex.conj_conj] at h2
  have hzc : (z : ℂ) - conj (τ : ℂ) ≠ 0 := sub_ne_zero.mpr (upper_ne_conj z τ)
  rw [coord, SubgroupStabilizer.coe_smul_eq_moeb, h1, h2]
  rw [← conj_denom]
  dsimp only [coord]
  field_simp

end
end Dubon2026.SourceFunctionField.EllipticCoordinate
