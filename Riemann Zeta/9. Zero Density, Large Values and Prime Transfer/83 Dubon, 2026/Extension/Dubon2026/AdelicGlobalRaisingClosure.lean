import Dubon2026.AdelicGlobalHolomorphicOrbit
import Dubon2026.HolomorphicClosedSubspace

/-! # Global original affine generator membership in the original raising closure -/

namespace Dubon2026

noncomputable section
open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup Filter
open scoped MatrixGroups Topology

private theorem inverse_scalar_cancel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : ℂ) (ha : a ≠ 0) (v : V) : a⁻¹ • (a • v) = v := inv_smul_smul₀ ha v

private theorem scalar_inverse_cancel {V : Type*} [AddCommGroup V] [Module ℂ V]
    (a : ℂ) (ha : a ≠ 0) (v : V) : a • (a⁻¹ • v) = v := smul_inv_smul₀ ha v

private theorem representation_mul_eigen {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g h : G) (v : V) (a : ℂ) (he : ρ h v = a • v) :
    ρ (g * h) v = a • ρ g v := by
  rw [map_mul, Module.End.mul_apply, he, map_smul]

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Near the original point i, the normalized affine Hilbert orbit is exactly its original retracted holomorphic slice. -/
theorem adelicNormalizedAffineHilbertOrbit_eq_local {z : ℂ} (hz : 0 < z.im)
    (hw : ‖z - Complex.I‖ < (1 / 2 : ℝ)) :
    adelicNormalizedAffineHilbertOrbit f z = adelicHolomorphicHilbertCurve f (z - Complex.I) := by
  have hp : (z.re : ℂ) + z.im * Complex.I - Complex.I = z - Complex.I :=
    congrArg (fun w : ℂ => w - Complex.I) (Complex.re_add_im z)
  have h := adelicCyclicHilbertGenerator_affine_positive_formula f z.re hz (hp ▸ hw)
  rw [hp] at h
  have hb : (Real.exp (Real.log z.im * ((k : ℝ) / 2)) : ℂ) ≠ 0 :=
    by exact_mod_cast (Real.exp_pos _).ne'
  exact (adelicNormalizedAffineHilbertOrbit_eq f hz).trans
    ((congrArg (fun v : AdelicCyclicHilbert f =>
      ((Real.exp (Real.log z.im * ((k : ℝ) / 2)) : ℂ))⁻¹ • v) h).trans
        (@inverse_scalar_cancel (AdelicCyclicHilbert f) inferInstance inferInstance _ hb _))

/-- Analytic continuation puts the entire original normalized affine Hilbert orbit in the same original raising closure. -/
theorem adelicNormalizedAffineHilbertOrbit_mem_closedSpan (hf : f ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    adelicNormalizedAffineHilbertOrbit f z ∈ adelicRaisingClosedSpan f := by
  apply @differentiableOn_mem_closedSubmodule (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance (adelicNormalizedAffineHilbertOrbit f)
    upperHalfPlaneSet (adelicNormalizedAffineHilbertOrbit_differentiableOn f)
    isOpen_upperHalfPlaneSet (convex_halfSpace_im_gt 0).isPreconnected
    (adelicRaisingClosedSpan f) (Submodule.isClosed_topologicalClosure _)
    Complex.I (by simp) _ z hz
  have hn : ∀ᶠ w : ℂ in 𝓝 Complex.I, ‖w - Complex.I‖ < (1 / 2 : ℝ) := by
    simpa only [Metric.ball, dist_eq_norm] using
      Metric.ball_mem_nhds Complex.I (show 0 < (1 / 2 : ℝ) by norm_num)
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds (show 0 < Complex.I.im by simp), hn]
    with w hw hn
  exact (adelicNormalizedAffineHilbertOrbit_eq_local f hw hn).symm ▸
    adelicHolomorphicL2Curve_retraction_mem_closedSpan f hf hn

/-- Every genuine positive affine translate of the original cusp generator lies in the original raising closure, with no local coordinate restriction. -/
theorem adelicCyclicHilbertGenerator_affine_mem_closedSpan_global (hf : f ≠ 0)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realAffineMatrix x hy))
      (adelicCyclicHilbertGenerator f) ∈ adelicRaisingClosedSpan f := by
  let z : ℂ := (x : ℂ) + y * Complex.I
  have hz : 0 < z.im := by simpa only [z, Complex.add_im, Complex.ofReal_im,
    Complex.mul_I_im, Complex.ofReal_re, zero_add] using hy
  have h := adelicNormalizedAffineHilbertOrbit_mem_closedSpan f hf hz
  have he := adelicNormalizedAffineHilbertOrbit_eq f hz
  have hb : (Real.exp (Real.log z.im * ((k : ℝ) / 2)) : ℂ) ≠ 0 :=
    by exact_mod_cast (Real.exp_pos _).ne'
  have hm := (adelicRaisingClosedSpan f).smul_mem
    (Real.exp (Real.log z.im * ((k : ℝ) / 2)) : ℂ) h
  have hcancel := @scalar_inverse_cancel (AdelicCyclicHilbert f) inferInstance inferInstance _ hb
    (adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (realAffineMatrix z.re hz))
      (adelicCyclicHilbertGenerator f))
  have hm' := ((congrArg (fun v : AdelicCyclicHilbert f =>
    (Real.exp (Real.log z.im * ((k : ℝ) / 2)) : ℂ) • v) he).trans hcancel) ▸ hm
  simpa only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero, Complex.add_im, Complex.mul_I_im, zero_add] using hm'

/-- Every original real-group translate of the genuine cusp generator lies in its original raising closure. -/
theorem adelicCyclicHilbertGenerator_real_mem_closedSpan (hf : f ≠ 0) (g : SL(2, ℝ)) :
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g)
      (adelicCyclicHilbertGenerator f) ∈ adelicRaisingClosedSpan f := by
  have ha : realAffineMatrix (g • I).re (g • I).im_pos = (g • I).toSL2R := by
    apply congrArg UpperHalfPlane.toSL2R
    apply UpperHalfPlane.ext
    exact Complex.re_add_im ((g • (I : ℍ) : ℍ) : ℂ)
  have he : adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding g)
      (adelicCyclicHilbertGenerator f) = (realCompactWeight k (realIwasawaCompact g) : ℂ) •
        adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding (g • I).toSL2R)
          (adelicCyclicHilbertGenerator f) := by
    have hc := adelicCyclicHilbertGenerator_compact_weight f (realIwasawaCompact g)
    change adelicCyclicHilbertRepresentation f
      (adelicRealSL2Embedding (realIwasawaCompact g).val) (adelicCyclicHilbertGenerator f) =
        (realCompactWeight k (realIwasawaCompact g) : ℂ) • adelicCyclicHilbertGenerator f at hc
    have hg : adelicRealSL2Embedding g = adelicRealSL2Embedding (g • I).toSL2R *
        adelicRealSL2Embedding (realIwasawaCompact g).val :=
      (congrArg adelicRealSL2Embedding (realIwasawa_reconstruct g).symm).trans (map_mul _ _ _)
    exact (congrArg (fun h : RationalAdelicGL2 =>
      adelicCyclicHilbertRepresentation f h (adelicCyclicHilbertGenerator f)) hg).trans
        (@representation_mul_eigen RationalAdelicGL2 (AdelicCyclicHilbert f)
          inferInstance inferInstance inferInstance (adelicCyclicHilbertRepresentation f)
          (adelicRealSL2Embedding (g • I).toSL2R)
          (adelicRealSL2Embedding (realIwasawaCompact g).val)
          (adelicCyclicHilbertGenerator f) (realCompactWeight k (realIwasawaCompact g) : ℂ) hc)
  have hm := adelicCyclicHilbertGenerator_affine_mem_closedSpan_global f hf
    (g • I).re (g • I).im_pos
  have hm' := (congrArg (fun h : SL(2, ℝ) =>
    adelicCyclicHilbertRepresentation f (adelicRealSL2Embedding h) (adelicCyclicHilbertGenerator f)) ha) ▸ hm
  exact he.symm ▸ (adelicRaisingClosedSpan f).smul_mem _ hm'

end
end Dubon2026
