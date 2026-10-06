import Dubon2026.TorusGridCharacters

/-! # Finite torus averages as contractions on continuous functions -/

namespace Dubon2026

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- Average over all translations by the full finite product grid. -/
def torusGridAverage (N m : ℕ) [NeZero m] (f : C(PrimeTorus N, ℂ)) : C(PrimeTorus N, ℂ) where
  toFun z := (Fintype.card (PrimeCoordinate N → ZMod m) : ℂ)⁻¹ *
    ∑ j : PrimeCoordinate N → ZMod m, f (z + torusGridPoint N m j)
  continuous_toFun := by fun_prop

theorem torusGridAverage_add (N m : ℕ) [NeZero m] (f g : C(PrimeTorus N, ℂ)) :
    torusGridAverage N m (f + g) = torusGridAverage N m f + torusGridAverage N m g := by
  ext z
  simp only [torusGridAverage, ContinuousMap.coe_mk, ContinuousMap.add_apply,
    Finset.sum_add_distrib, mul_add]

theorem torusGridAverage_sub (N m : ℕ) [NeZero m] (f g : C(PrimeTorus N, ℂ)) :
    torusGridAverage N m (f - g) = torusGridAverage N m f - torusGridAverage N m g := by
  ext z
  simp only [torusGridAverage, ContinuousMap.coe_mk, ContinuousMap.sub_apply,
    Finset.sum_sub_distrib, mul_sub]

theorem torusGridAverage_smul (N m : ℕ) [NeZero m] (c : ℂ) (f : C(PrimeTorus N, ℂ)) :
    torusGridAverage N m (c • f) = c • torusGridAverage N m f := by
  ext z
  simp only [torusGridAverage, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
    smul_eq_mul, ← Finset.mul_sum]
  ring

theorem torusGridAverage_const (N m : ℕ) [NeZero m] (c : ℂ) :
    torusGridAverage N m (ContinuousMap.const _ c) = ContinuousMap.const _ c := by
  have hc : (Fintype.card (PrimeCoordinate N → ZMod m) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (PrimeCoordinate N → ZMod m)).ne'
  ext z
  simp only [torusGridAverage, ContinuousMap.coe_mk, ContinuousMap.const_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem norm_torusGridAverage_le (N m : ℕ) [NeZero m] (f : C(PrimeTorus N, ℂ)) :
    ‖torusGridAverage N m f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro z
  have hc : 0 < (Fintype.card (PrimeCoordinate N → ZMod m) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (PrimeCoordinate N → ZMod m))
  change ‖(Fintype.card (PrimeCoordinate N → ZMod m) : ℂ)⁻¹ *
    ∑ j : PrimeCoordinate N → ZMod m, f (z + torusGridPoint N m j)‖ ≤ ‖f‖
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (Fintype.card (PrimeCoordinate N → ZMod m) : ℝ)⁻¹ *
        ∑ j : PrimeCoordinate N → ZMod m, ‖f‖ :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum (fun j _ => f.norm_coe_le_norm _))) (inv_pos.mpr hc).le
    _ = ‖f‖ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

theorem lipschitz_torusGridAverage (N m : ℕ) [NeZero m] :
    LipschitzWith 1 (torusGridAverage N m) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [dist_eq_norm, ← torusGridAverage_sub, NNReal.coe_one, one_mul] using
    norm_torusGridAverage_le N m (f - g)

theorem torusGridAverage_mFourier_eq_zero {N m : ℕ} [NeZero m]
    (k : PrimeCoordinate N → ℤ) {p : PrimeCoordinate N} (hp : (k p : ZMod m) ≠ 0) :
    torusGridAverage N m (UnitAddTorus.mFourier k) = 0 := by
  ext z
  simp only [torusGridAverage, ContinuousMap.coe_mk, mFourier_add_point,
    ← Finset.mul_sum, sum_mFourier_grid_eq_zero k hp, mul_zero, ContinuousMap.zero_apply]

theorem eventually_torusGridAverage_mFourier (N : ℕ) (k : PrimeCoordinate N → ℤ) :
    ∀ᶠ n : ℕ in atTop, torusGridAverage N (n + 1) (UnitAddTorus.mFourier k) =
      ContinuousMap.const _ (∫ z, UnitAddTorus.mFourier k z ∂torusHaar N) := by
  classical
  rw [integral_mFourier_torusHaar]
  by_cases hk : k = 0
  · subst k
    filter_upwards [] with n
    simp only [UnitAddTorus.mFourier_zero]
    exact torusGridAverage_const N (n + 1) 1
  · obtain ⟨p, hp⟩ : ∃ p, k p ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (funext h)
    filter_upwards [eventually_ge_atTop (k p).natAbs] with n hn
    rw [if_neg hk, torusGridAverage_mFourier_eq_zero k
      (intCast_zmod_ne_zero_of_natAbs_lt hp (by omega))]
    rfl

end

end Dubon2026
