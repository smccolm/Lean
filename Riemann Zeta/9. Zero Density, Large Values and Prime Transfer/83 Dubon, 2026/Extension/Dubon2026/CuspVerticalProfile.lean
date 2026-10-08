import Dubon2026.CuspPolynomialDecay
import Mathlib.NumberTheory.ModularForms.Identities

/-! # The actual cusp function on the imaginary axis and its modular reciprocal -/

namespace Dubon2026

open UpperHalfPlane ModularGroup Filter Set Asymptotics MeasureTheory
open Matrix.SpecialLinearGroup ConjAct
open scoped MatrixGroups ModularForm Pointwise Topology

noncomputable section

/-- The genuine imaginary-axis value of a cusp form; only positive arguments enter its Mellin integrals. -/
def cuspVerticalProfile {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) (y : ℝ) : ℂ := f (UpperHalfPlane.ofComplex ((y : ℂ) * Complex.I))

/-- The actual positive imaginary-axis profile is continuous. -/
theorem continuousOn_cuspVerticalProfile {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) : ContinuousOn (cuspVerticalProfile f) (Ioi 0) := by
  apply (ModularFormClass.continuous f).continuousOn.comp
    (UpperHalfPlane.ofComplex.continuousOn.comp
      (Complex.continuous_ofReal.mul_const Complex.I).continuousOn ?_) (fun _ _ => Set.mem_univ _)
  intro y hy
  simp only [UpperHalfPlane.ofComplex, OpenPartialHomeomorph.symm_source,
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
  exact ⟨⟨(y : ℂ) * Complex.I, by simpa using hy⟩, rfl⟩

/-- The genuine imaginary-axis curve tends to the cusp at infinity. -/
theorem tendsto_cuspVerticalPoint :
    Tendsto (fun y : ℝ => UpperHalfPlane.ofComplex ((y : ℂ) * Complex.I)) atTop atImInfty := by
  apply tendsto_comap_im_ofComplex.comp
  rw [tendsto_comap_iff]
  simpa only [Function.comp_def, Complex.mul_I_im, Complex.ofReal_re] using
    (tendsto_id : Tendsto (fun y : ℝ => y) atTop atTop)

/-- The genuine profile inherits exponential cusp decay and hence every polynomial decay rate. -/
theorem cuspVerticalProfile_isBigO_rpow {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
    {k : ℤ} (f : CuspForm Γ k) (r : ℝ) :
    cuspVerticalProfile f =O[atTop] (fun y : ℝ => y ^ r) := by
  obtain ⟨c,hc,hdec⟩ := CuspFormClass.exp_decay_atImInfty' f
  have he := hdec.comp_tendsto tendsto_cuspVerticalPoint
  have he' : cuspVerticalProfile f =O[atTop] (fun y : ℝ => Real.exp (-c * y)) := by
    apply he.congr' (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    have hyC : 0 < ((y : ℂ) * Complex.I).im := by simpa using hy
    simp only [Function.comp_def, UpperHalfPlane.ofComplex_apply_of_im_pos hyC,
      UpperHalfPlane.im, Complex.mul_I_im, Complex.ofReal_re]
  exact he'.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO

/-- The actual slashed cusp value gives the exact reciprocal profile with root factor i^k and the original integral weight. -/
theorem cuspVerticalProfile_reciprocal {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (f : CuspForm Γ k) {y : ℝ} (hy : 0 < y) :
    cuspVerticalProfile f (1 / y) =
      (Complex.I ^ k * ((y ^ (k : ℝ) : ℝ) : ℂ)) *
        cuspVerticalProfile (CuspForm.translate f ModularGroup.S) y := by
  let z : ℍ := ⟨(y : ℂ) * Complex.I, by simpa using hy⟩
  have hz : (z : ℂ) ≠ 0 := z.ne_zero
  have hS := SlashInvariantForm.slash_S_apply (⇑f) k z
  have hpoint : (⟨(-(z : ℂ))⁻¹, z.im_inv_neg_coe_pos⟩ : ℍ) =
      UpperHalfPlane.ofComplex (((1 / y : ℝ) : ℂ) * Complex.I) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using one_div_pos.mpr hy)]
    simp [z, one_div, mul_inv_rev, Complex.inv_I, mul_comm]
  rw [hpoint] at hS
  have hp : (z : ℂ) ^ k = Complex.I ^ k * ((y ^ (k : ℝ) : ℝ) : ℂ) := by
    simp [z, mul_zpow, Real.rpow_intCast, Complex.ofReal_zpow, mul_comm]
  unfold cuspVerticalProfile
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < ((y : ℂ) * Complex.I).im by simpa using hy)]
  change _ = (Complex.I ^ k * ((y ^ (k : ℝ) : ℝ) : ℂ)) * ((⇑f ∣[k] ModularGroup.S) z)
  rw [← hp, hS, zpow_neg]
  symm
  calc
    _ = f (UpperHalfPlane.ofComplex (((1 / y : ℝ) : ℂ) * Complex.I)) *
        ((z : ℂ) ^ k * ((z : ℂ) ^ k)⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (zpow_ne_zero k hz), mul_one]

end
end Dubon2026
