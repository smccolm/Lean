import Dubon2026.SourceSiegelThetaTransform

/-! DUB-17/18 -> original Gamma1 degree/genus preservation -> level-power
slash integrality -> peaked auxiliary existence -> the actual Siegel
product transformation. Reuse the proved literal product/theta equality,
native theta and eta transformations, and native generators of SL(2,Z).
The twelfth-root multiplier is derived from the generator identities;
no slash-invariance or multiplier-existence hypothesis is supplied.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_siegelFun_specialLinearGroup_smul. -/
namespace Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel
noncomputable section
open Complex
open UpperHalfPlane hiding I
open scoped Real MatrixGroups

theorem sprod_S (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℍ) :
    sprod N r s (-1 / (τ : ℂ)) =
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) * sprod N s (-r) τ := by
  have hτ' : 0 < (-1 / (τ : ℂ)).im := by
    have : -1 / (τ : ℂ) = (-(τ : ℂ))⁻¹ := by rw [inv_neg, neg_div, one_div]
    rw [this]; exact τ.im_inv_neg_coe_pos
  have h1 := theta_eq N hN r s hτ'
  have h2 := theta_eq N hN s (-r) τ.2
  have h3 := theta_S N hN r s τ
  rw [h1, h2, P_S] at h3

  have hne : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) *
      cexp (π * I * τ / 12) * P τ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (cpow_half_ne_zero τ) (Complex.exp_ne_zero _))
      (Complex.exp_ne_zero _)) (P_ne_zero τ.2)
  refine mul_left_cancel₀ hne ?_
  rw [h3]
  have he : cexp (-(π * I * (-1 / (τ : ℂ)) / 12)) * cexp (π * I * τ / 12) *
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) =
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) * cexp (-π * I * (τ + 2 * w N s (-r) τ)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
        cexp (-π * I * (τ + 2 * w N s (-r) τ)) * (P τ * sprod N s (-r) τ)
        = (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) * (cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ) *
            cexp (-π * I * (τ + 2 * w N s (-r) τ))) * P τ * sprod N s (-r) τ := by ring
    _ = _ := by rw [← he]; ring

theorem pref_S (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (τ : ℍ) :
    pref N r s (-1 / (τ : ℂ)) *
      cexp (π * I * (w N s (-r) τ + τ) ^ 2 / τ + -π * I * (τ + 2 * w N s (-r) τ) -
        -(π * I * (-1 / (τ : ℂ)) / 12) - π * I * τ / 12) = -I * pref N s (-r) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hI : -I = cexp (-(π / 2 * I)) := by
    rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]
  unfold pref
  rw [hI]
  simp only [neg_mul, mul_neg, neg_inj, ← Complex.exp_add]
  congr 1
  unfold w
  push_cast
  field_simp
  ring

theorem siegelFun_S (N : ℕ) (r s : ℤ) (τ : ℍ) :
    siegelFun N r s (-1 / (τ : ℂ)) = -I * siegelFun N s (-r) τ := by
  rcases eq_or_ne N 0 with rfl | hN
  · simp [siegelFun_level_zero]
  rw [siegelFun_eq, siegelFun_eq, sprod_S N hN, ← mul_assoc, pref_S N hN, mul_assoc]


end
end Dubon2026.SourceFunctionField.GammaOne.PeakedAuxiliary.Siegel
