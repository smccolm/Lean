import Dubon2026.SourcePeriodPrimitive
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-! DUB-17/18 -> residual modular Galois association -> parabolic complex
Hecke realization -> Eichler--Shimura period-pair injectivity -> constancy
of an invariant real part. A holomorphic function with periodic real part
and a finite cusp limit is actually periodic. This enables the pinned
removable-cusp and maximum principles, avoiding a separate rectangular
integral argument. The derivative and constancy arguments adapt
anthropics/fermats-last-theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_periodHomPair_injective.lean (Apache 2.0).
-/
namespace Dubon2026
noncomputable section
open Complex UpperHalfPlane Filter
open scoped Topology

/-- A holomorphic function with zero real part has zero complex derivative. -/
theorem sourceHolomorphic_re_zero_deriv {B : ℂ → ℂ} {b : ℂ}
    {τ : ℍ} (hB : HasDerivAt B b (τ : ℂ))
    (hre : ∀ σ : ℍ, (B (σ : ℂ)).re = 0) : b = 0 := by
  have hzero : (Complex.reCLM ∘ B) =ᶠ[𝓝 (τ : ℂ)] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with w hw
    exact hre ⟨w, hw⟩
  have h1 := Complex.reCLM.hasFDerivAt.comp (τ : ℂ)
    (hB.hasFDerivAt.restrictScalars ℝ)
  have h2 : HasFDerivAt (Complex.reCLM ∘ B) (0 : ℂ →L[ℝ] ℝ) (τ : ℂ) :=
    (hasFDerivAt_const (0 : ℝ) (τ : ℂ)).congr_of_eventuallyEq hzero
  have hd := h1.unique h2
  apply Complex.ext
  · simpa using DFunLike.congr_fun hd (1 : ℂ)
  · have hi := DFunLike.congr_fun hd Complex.I
    simpa using hi

/-- A holomorphic function with zero real part is constant on the original
upper half-plane. -/
theorem sourceHolomorphic_re_zero_const {B : ℂ → ℂ} {b : ℍ → ℂ}
    (hB : ∀ τ : ℍ, HasDerivAt B (b τ) (τ : ℂ))
    (hre : ∀ σ : ℍ, (B (σ : ℂ)).re = 0) (z w : ℍ) :
    B (z : ℂ) = B (w : ℂ) := by
  have hd (τ : ℍ) : HasDerivAt B 0 (τ : ℂ) := by
    simpa only [sourceHolomorphic_re_zero_deriv (hB τ) hre] using hB τ
  apply isOpen_upperHalfPlaneSet.is_const_of_fderiv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun x hx => (hd ⟨x, hx⟩).differentiableAt.differentiableWithinAt)
    (fun x hx => ?_) z.2 w.2
  rw [(hd ⟨x, hx⟩).hasFDerivAt.fderiv]
  ext
  simp

/-- Real periodicity and a finite cusp limit force actual complex periodicity
of the holomorphic primitive, with no supplied period-vanishing assumption. -/
theorem sourceHolomorphic_period_of_re_period_of_tendsto
    {B : ℂ → ℂ} {b : ℍ → ℂ} (p : ℝ) (L : ℂ)
    (hB : ∀ τ : ℍ, HasDerivAt B (b τ) (τ : ℂ))
    (hre : ∀ τ : ℍ, (B ((τ : ℂ) + p)).re = (B (τ : ℂ)).re)
    (hlim : Tendsto (fun τ : ℍ => B (τ : ℂ)) atImInfty (𝓝 L))
    (z : ℍ) : B ((z : ℂ) + p) = B (z : ℂ) := by
  let D : ℂ → ℂ := fun w => B (w + p) - B w
  have hd (τ : ℍ) : HasDerivAt D (b (p +ᵥ τ) - b τ) (τ : ℂ) := by
    have ht : HasDerivAt B (b (p +ᵥ τ)) ((τ : ℂ) + p) := by
      simpa only [coe_vadd, add_comm] using hB (p +ᵥ τ)
    simpa only [D, Function.comp_def, id_eq, mul_one] using
      (ht.comp (τ : ℂ) ((hasDerivAt_id (τ : ℂ)).add_const (p : ℂ))).sub (hB τ)
  have hr (τ : ℍ) : (D (τ : ℂ)).re = 0 := by
    simp only [D, Complex.sub_re, hre τ, sub_self]
  have hc (τ : ℍ) : D (τ : ℂ) = D (z : ℂ) :=
    sourceHolomorphic_re_zero_const hd hr τ z
  have ht : Tendsto (fun τ : ℍ => p +ᵥ τ) atImInfty atImInfty := by
    apply tendsto_comap_iff.mpr
    simpa only [Function.comp_def, vadd_im] using
      (show Tendsto UpperHalfPlane.im atImInfty atTop from tendsto_comap)
  have hl : Tendsto (fun τ : ℍ => D (τ : ℂ)) atImInfty (𝓝 0) := by
    simpa only [D, Function.comp_def, coe_vadd, add_comm, sub_self] using
      (hlim.comp ht).sub hlim
  have hD : D (z : ℂ) = 0 := tendsto_nhds_unique
    (tendsto_const_nhds.congr fun τ => (hc τ).symm) hl
  exact sub_eq_zero.mp hD

end
end Dubon2026
