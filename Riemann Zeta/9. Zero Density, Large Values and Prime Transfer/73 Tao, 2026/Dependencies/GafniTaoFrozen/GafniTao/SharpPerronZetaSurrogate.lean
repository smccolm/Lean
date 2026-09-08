import GafniTao.SharpPerronResidue
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RiemannZeta.GuthMaynard.ClassicalDensity

/-!
# The entire zeta surrogate used in the sharp Perron shift

The totalized Mathlib zeta function has its meromorphic pole hidden at the
single point `1`.  The patched function below is the genuine entire function
obtained from `(s - 1) ζ(s)`.  It lets the contour proof keep the zeta zeros
and their analytic multiplicities while handling the pole at one as a
separate explicit rational term.
-/

open Complex Filter Set Topology

noncomputable section

namespace GafniTao

/-- The entire surrogate `(s - 1) ζ(s)`, patched by its limiting value at the
zeta pole. -/
noncomputable def sharpZetaSurrogate (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

@[simp] theorem sharpZetaSurrogate_one : sharpZetaSurrogate 1 = 1 := by
  simp [sharpZetaSurrogate]

/-- Away from one, the surrogate agrees locally with the unpatched product. -/
theorem sharpZetaSurrogate_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    sharpZetaSurrogate =ᶠ[𝓝 s] fun w => (w - 1) * riemannZeta w := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
  simp [sharpZetaSurrogate, Set.mem_compl_singleton_iff.mp hw]

/-- The patched surrogate is entire. -/
theorem sharpZetaSurrogate_differentiable :
    Differentiable ℂ sharpZetaSurrogate := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (c := (1 : ℂ)) Filter.univ_mem]
  constructor
  · intro s hs
    have hs1 : s ≠ 1 := by simpa using hs.2
    have hd : DifferentiableAt ℂ
        (fun w : ℂ => (w - 1) * riemannZeta w) s :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)
    exact (hd.congr_of_eventuallyEq
      (sharpZetaSurrogate_eventuallyEq hs1)).differentiableWithinAt
  · have h1 : sharpZetaSurrogate 1 = 1 := sharpZetaSurrogate_one
    have hev : (fun w : ℂ => (w - 1) * riemannZeta w) =ᶠ[𝓝[≠] (1 : ℂ)]
        sharpZetaSurrogate := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      simp [sharpZetaSurrogate, Set.mem_compl_singleton_iff.mp hw]
    have key : Tendsto sharpZetaSurrogate (𝓝[≠] (1 : ℂ))
        (𝓝 (sharpZetaSurrogate 1)) := by
      rw [h1]
      exact Filter.Tendsto.congr' hev riemannZeta_residue_one
    exact continuousWithinAt_compl_self.mp key

/-- Analyticity form of the preceding entire-function theorem. -/
theorem sharpZetaSurrogate_analytic :
    AnalyticOnNhd ℂ sharpZetaSurrogate Set.univ := by
  rw [Complex.analyticOnNhd_iff_differentiableOn isOpen_univ]
  exact sharpZetaSurrogate_differentiable.differentiableOn

/-- Away from one, surrogate zeros are exactly zeta zeros. -/
theorem sharpZetaSurrogate_eq_zero_iff {s : ℂ} (hs : s ≠ 1) :
    sharpZetaSurrogate s = 0 ↔ riemannZeta s = 0 := by
  rw [sharpZetaSurrogate, if_neg hs, mul_eq_zero]
  exact or_iff_right (sub_ne_zero.mpr hs)

/-- The origin is not a surrogate zero; its exact value is `1/2`. -/
@[simp] theorem sharpZetaSurrogate_zero : sharpZetaSurrogate 0 = 1 / 2 := by
  rw [sharpZetaSurrogate, if_neg (by norm_num : (0 : ℂ) ≠ 1),
    riemannZeta_zero]
  ring

/-- At every point away from one, the surrogate and zeta have the same
analytic order.  In particular this preserves the exact multiplicity of each
nontrivial zero. -/
theorem analyticOrderAt_sharpZetaSurrogate_eq {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt sharpZetaSurrogate s = analyticOrderAt riemannZeta s := by
  have heq := sharpZetaSurrogate_eventuallyEq hs
  have hfactor : AnalyticAt ℂ (fun w : ℂ => w - 1) s := by fun_prop
  have hzeta : AnalyticAt ℂ riemannZeta s :=
    analyticOn_riemannZeta s (by simpa using hs)
  have hfactorOrder : analyticOrderAt (fun w : ℂ => w - 1) s = 0 := by
    exact hfactor.analyticOrderAt_eq_zero.mpr
      (sub_ne_zero.mpr hs)
  calc
    analyticOrderAt sharpZetaSurrogate s =
        analyticOrderAt (fun w : ℂ => (w - 1) * riemannZeta w) s :=
      analyticOrderAt_congr heq
    _ = analyticOrderAt (fun w : ℂ => w - 1) s +
        analyticOrderAt riemannZeta s :=
      analyticOrderAt_mul hfactor hzeta
    _ = analyticOrderAt riemannZeta s := by rw [hfactorOrder, zero_add]

/-- Meromorphic order of the entire surrogate at a zeta zero is the exact
natural analytic multiplicity used by the frozen zero-counting API. -/
theorem meromorphicOrderAt_sharpZetaSurrogate_eq_multiplicity
    {s : ℂ} (hs : s ≠ 1) :
    meromorphicOrderAt sharpZetaSurrogate s =
      ((RiemannZeta.GuthMaynard.analyticVanishingOrder riemannZeta s : ℕ) :
        WithTop ℤ) := by
  have hsur : AnalyticAt ℂ sharpZetaSurrogate s :=
    sharpZetaSurrogate_analytic s (by simp)
  have hfinite : analyticOrderAt riemannZeta s ≠ ⊤ :=
    RiemannZeta.GuthMaynard.riemannZeta_analyticOrderAt_ne_top hs
  rw [hsur.meromorphicOrderAt_eq,
    analyticOrderAt_sharpZetaSurrogate_eq hs]
  unfold RiemannZeta.GuthMaynard.analyticVanishingOrder
  rw [← Nat.cast_analyticOrderNatAt hfinite]
  simp

end GafniTao
