import Mathlib.Analysis.MellinInversion
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannZeta.GuthMaynard.Estermann

open Complex Finset Filter Topology MeasureTheory
open scoped BigOperators Interval
open Classical

namespace RiemannZeta.GuthMaynard

/-!
# Mellin entry to periodic divisor Voronoi summation

This module connects the actual weighted divisor series to the periodic
Estermann continuation.  It proves the right-line identity before contour
shifting.  The assumptions are precisely Mellin inversion and the absolute
Fubini condition; neither contains the desired Voronoi or DFI conclusion.
-/

private theorem hIntegral_const_div_sq (C p : ℂ) (x₁ x₂ y : ℝ)
    (hy : y ≠ p.im) :
    HIntegral (fun s : ℂ => C / (s - p) ^ 2) x₁ x₂ y =
      -C / ((x₂ : ℂ) + (y : ℂ) * I - p) -
        (-C / ((x₁ : ℂ) + (y : ℂ) * I - p)) := by
  let F : ℝ → ℂ := fun x => -C / ((x : ℂ) + (y : ℂ) * I - p)
  let F' : ℝ → ℂ := fun x => C / ((x : ℂ) + (y : ℂ) * I - p) ^ 2
  have hne : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I - p) ≠ 0 := by
    intro x h
    have hi := congrArg Complex.im h
    simp only [sub_im, add_im, ofReal_im, ofReal_re, mul_im, I_im, I_re,
      mul_one, mul_zero, zero_add, zero_im, add_zero] at hi
    exact hy (sub_eq_zero.mp hi)
  have hhas : ∀ x : ℝ, HasDerivAt F (F' x) x := by
    intro x
    dsimp [F, F']
    have hg : HasDerivAt
        (fun x : ℝ => (x : ℂ) + (y : ℂ) * I - p) 1 x := by
      convert (Complex.hasDerivAt_ofReal x).add_const ((y : ℂ) * I - p) using 1
      ext z
      ring
    convert (hasDerivAt_const x (-C)).div hg (hne x) using 1
    ring
  have hd : deriv F = F' := funext fun x => (hhas x).deriv
  have hdiff : ∀ x ∈ Set.uIcc x₁ x₂, DifferentiableAt ℝ F x :=
    fun x _ => (hhas x).differentiableAt
  have hcont : Continuous F' := by
    dsimp [F']
    exact continuous_const.div
      (((continuous_ofReal.add continuous_const).sub continuous_const).pow 2)
      (fun x => pow_ne_zero 2 (hne x))
  simpa [HIntegral, F, F'] using
    intervalIntegral.integral_deriv_eq_sub' F hd hdiff hcont.continuousOn

private theorem vIntegral_const_div_sq (C p : ℂ) (x y₁ y₂ : ℝ)
    (hx : x ≠ p.re) :
    VIntegral (fun s : ℂ => C / (s - p) ^ 2) x y₁ y₂ =
      -C / ((x : ℂ) + (y₂ : ℂ) * I - p) -
        (-C / ((x : ℂ) + (y₁ : ℂ) * I - p)) := by
  let F : ℝ → ℂ := fun y => -C / ((x : ℂ) + (y : ℂ) * I - p)
  let F' : ℝ → ℂ := fun y => C * I / ((x : ℂ) + (y : ℂ) * I - p) ^ 2
  have hne : ∀ y : ℝ, ((x : ℂ) + (y : ℂ) * I - p) ≠ 0 := by
    intro y h
    have hr := congrArg Complex.re h
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, I_im, mul_zero,
      ofReal_im, zero_mul, sub_zero, zero_re, add_zero] at hr
    exact hx (sub_eq_zero.mp hr)
  have hhas : ∀ y : ℝ, HasDerivAt F (F' y) y := by
    intro y
    dsimp [F, F']
    have hg : HasDerivAt
        (fun y : ℝ => (x : ℂ) + (y : ℂ) * I - p) I y := by
      convert ((Complex.hasDerivAt_ofReal y).mul_const I).add_const
        ((x : ℂ) - p) using 1
      · ext z
        ring
      · simp
    convert (hasDerivAt_const y (-C)).div hg (hne y) using 1
    ring
  have hd : deriv F = F' := funext fun y => (hhas y).deriv
  have hdiff : ∀ y ∈ Set.uIcc y₁ y₂, DifferentiableAt ℝ F y :=
    fun y _ => (hhas y).differentiableAt
  have hcont : Continuous F' := by
    dsimp [F']
    exact continuous_const.div
      (((continuous_const.add (continuous_ofReal.mul continuous_const)).sub
        continuous_const).pow 2)
      (fun y => pow_ne_zero 2 (hne y))
  have hFTC := intervalIntegral.integral_deriv_eq_sub' F hd hdiff hcont.continuousOn
  rw [show F' = fun y : ℝ =>
      I * (C / ((x : ℂ) + (y : ℂ) * I - p) ^ 2) by
    funext y
    dsimp [F']
    ring] at hFTC
  rw [intervalIntegral.integral_const_mul] at hFTC
  simpa [VIntegral, F, smul_eq_mul] using hFTC

/-- The double-pole term has zero integral around every rectangle whose
interior contains the pole.  This is the exact higher-pole cancellation
needed before applying the repository's simple-pole residue theorem. -/
theorem rectangleIntegral'_const_div_sq_eq_zero {C p z w : ℂ}
    (hzre : z.re ≤ w.re) (hzim : z.im ≤ w.im)
    (hp : Rectangle z w ∈ 𝓝 p) :
    RectangleIntegral' (fun s : ℂ => C / (s - p) ^ 2) z w = 0 := by
  have hp' := hp
  rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzre, Set.uIoo_of_le hzim,
    mem_reProdIm, Set.mem_Ioo] at hp'
  rcases hp' with ⟨⟨hzpRe, hpwRe⟩, ⟨hzpIm, hpwIm⟩⟩
  have hbottom := hIntegral_const_div_sq C p z.re w.re z.im
    (ne_of_lt hzpIm)
  have htop := hIntegral_const_div_sq C p z.re w.re w.im
    (ne_of_gt hpwIm)
  have hright := vIntegral_const_div_sq C p w.re z.im w.im
    (ne_of_gt hpwRe)
  have hleft := vIntegral_const_div_sq C p z.re z.im w.im
    (ne_of_lt hzpRe)
  unfold RectangleIntegral' RectangleIntegral
  rw [hbottom, htop, hright, hleft]
  ring

/-- Exact finite-height contour shift for a periodic Estermann function
times an entire Mellin multiplier.  The double pole contributes only the
derivative of the multiplier; its pure order-two term cancels around the
rectangle. -/
theorem periodicEstermann_mul_finiteRectangle
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) {d c H : ℝ}
    (hd : d < 1) (hc : 1 < c) (hH : 0 < H) :
    RectangleIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s)
        ((d : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) =
      periodicEstermannPoleCleared q Φ 1 * deriv G 1 +
        periodicEstermannResidueCoeff q Φ * G 1 := by
  let z : ℂ := (d : ℂ) - (H : ℂ) * I
  let w : ℂ := (c : ℂ) + (H : ℂ) * I
  let C : ℂ := periodicEstermannPoleCleared q Φ 1 * G 1
  let N : ℂ → ℂ := fun s =>
    periodicEstermannPoleCleared q Φ 1 * dslope G 1 s +
      periodicEstermannResidueCoeff q Φ * G s
  let A : ℂ := periodicEstermannPoleCleared q Φ 1 * deriv G 1 +
    periodicEstermannResidueCoeff q Φ * G 1
  let R : ℂ → ℂ := fun s => periodicEstermannRegularPart q Φ s * G s
  let f : ℂ → ℂ := fun s => periodicEstermann q Φ s * G s
  let f₁ : ℂ → ℂ := fun s => f s - C / (s - 1) ^ 2
  let g : ℂ → ℂ := fun s => dslope N 1 s + R s
  have hzre : z.re ≤ w.re := by simp [z, w]; linarith
  have hzim : z.im ≤ w.im := by simp [z, w]; linarith
  have hp : Rectangle z w ∈ 𝓝 (1 : ℂ) := by
    rw [rectangle_mem_nhds_iff, mem_reProdIm,
      Set.uIoo_of_le hzre, Set.uIoo_of_le hzim]
    simp [z, w, hd, hc, hH]
  have hN : Differentiable ℂ N := by
    dsimp [N]
    exact differentiable_periodicEstermann_simpleNumerator q Φ G hG
  have hR : Differentiable ℂ R := by
    dsimp [R]
    exact (differentiable_periodicEstermannRegularPart q Φ).mul hG
  have hg : HolomorphicOn g (Rectangle z w) := by
    change DifferentiableOn ℂ g (Rectangle z w)
    exact ((Complex.differentiableOn_dslope
      (s := Set.univ) (c := (1 : ℂ)) univ_mem).2 hN.differentiableOn).add
        hR.differentiableOn |>.mono (by intro s _; exact Set.mem_univ s)
  have hN1 : N 1 = A := by
    dsimp [N, A]
    exact periodicEstermann_simpleNumerator_one q Φ G
  have hprincipal : Set.EqOn
      (f₁ - fun s => A / (s - 1)) g (Rectangle z w \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := hs.2
    have hdecomp := periodicEstermann_mul_eq_double_add_simple_add_regular
      q Φ G hs1
    change f s = C / (s - 1) ^ 2 + N s / (s - 1) + R s at hdecomp
    rw [Pi.sub_apply]
    change f s - C / (s - 1) ^ 2 - A / (s - 1) =
      dslope N 1 s + R s
    rw [hdecomp, dslope_of_ne N hs1]
    unfold slope
    simp only [vsub_eq_sub, smul_eq_mul]
    rw [hN1]
    have hsSub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [hsSub]
    ring
  have hrect₁ := ResidueTheoremOnRectangleWithSimplePole
    (f := f₁) (g := g) (p := (1 : ℂ)) (A := A)
    hzre hzim hp hg hprincipal
  have hdouble := rectangleIntegral'_const_div_sq_eq_zero
    (C := C) (p := (1 : ℂ)) hzre hzim hp
  have hf₁Holo : HolomorphicOn f₁ (Rectangle z w \ {1}) := by
    intro s hs
    have hs1 : s ≠ 1 := hs.2
    apply DifferentiableAt.differentiableWithinAt
    exact ((differentiableAt_periodicEstermann q Φ hs1).mul hG.differentiableAt).sub
      (differentiableAt_const C |>.div
        ((differentiableAt_id.sub_const 1).pow 2)
        (pow_ne_zero 2 (sub_ne_zero.mpr hs1)))
  have hdoubleHolo : HolomorphicOn (fun s : ℂ => C / (s - 1) ^ 2)
      (Rectangle z w \ {1}) := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    exact differentiableAt_const C |>.div
      ((differentiableAt_id.sub_const 1).pow 2)
      (pow_ne_zero 2 (sub_ne_zero.mpr hs.2))
  have hf₁Int : RectangleBorderIntegrable f₁ z w :=
    HolomorphicOn.rectangleBorderIntegrable' hf₁Holo hp
  have hdoubleInt : RectangleBorderIntegrable
      (fun s : ℂ => C / (s - 1) ^ 2) z w :=
    HolomorphicOn.rectangleBorderIntegrable' hdoubleHolo hp
  have hpoint : f = f₁ + fun s : ℂ => C / (s - 1) ^ 2 := by
    funext s
    dsimp [f₁]
    ring
  have hrectAdd : RectangleIntegral f z w = RectangleIntegral f₁ z w +
      RectangleIntegral (fun s : ℂ => C / (s - 1) ^ 2) z w := by
    rw [hpoint]
    exact RectangleBorderIntegrable.add hf₁Int hdoubleInt
  change RectangleIntegral' f z w = A
  unfold RectangleIntegral' at hrect₁ hdouble ⊢
  rw [hrectAdd, smul_add, hrect₁, hdouble, add_zero]

/-- Infinite-height contour shift obtained from the exact finite rectangle.
The sole analytic hypothesis is the vanishing of the two horizontal tails;
the main term and both vertical contours are fixed explicitly. -/
theorem periodicEstermann_mul_vertical_shift
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (G : ℂ → ℂ)
    (hG : Differentiable ℂ G) {d c : ℝ} (hd : d < 1) (hc : 1 < c)
    (hIntD : Integrable (fun u : ℝ =>
      periodicEstermann q Φ ((d : ℂ) + (u : ℂ) * I) *
        G ((d : ℂ) + (u : ℂ) * I)))
    (hIntC : Integrable (fun u : ℝ =>
      periodicEstermann q Φ ((c : ℂ) + (u : ℂ) * I) *
        G ((c : ℂ) + (u : ℂ) * I)))
    (hTails : Tendsto (fun H : ℝ =>
      (1 / (2 * Real.pi * I)) •
        (UpperUIntegral (fun s : ℂ => periodicEstermann q Φ s * G s) d c H -
          LowerUIntegral (fun s : ℂ => periodicEstermann q Φ s * G s) d c H))
      atTop (𝓝 0)) :
    VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s) c -
        VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s) d =
      periodicEstermannPoleCleared q Φ 1 * deriv G 1 +
        periodicEstermannResidueCoeff q Φ * G 1 := by
  let f : ℂ → ℂ := fun s => periodicEstermann q Φ s * G s
  let A : ℂ := periodicEstermannPoleCleared q Φ 1 * deriv G 1 +
    periodicEstermannResidueCoeff q Φ * G 1
  have hEq : ∀ᶠ H : ℝ in atTop,
      VerticalIntegral' f c - VerticalIntegral' f d =
        A + (1 / (2 * Real.pi * I)) •
          (UpperUIntegral f d c H - LowerUIntegral f d c H) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
    have hrect := periodicEstermann_mul_finiteRectangle
      q Φ G hG hd hc hH
    change RectangleIntegral' f
      ((d : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) = A at hrect
    have hdiff := DiffVertRect_eq_UpperLowerUs
      (f := f) (σ := d) (σ' := c) (T := H) hIntD hIntC
    have hdiff' : VerticalIntegral f c - VerticalIntegral f d -
        RectangleIntegral f ((d : ℂ) - (H : ℂ) * I)
          ((c : ℂ) + (H : ℂ) * I) =
        UpperUIntegral f d c H - LowerUIntegral f d c H := by
      simpa [mul_comm] using hdiff
    change (1 / (2 * Real.pi * I)) • RectangleIntegral f
      ((d : ℂ) - (H : ℂ) * I) ((c : ℂ) + (H : ℂ) * I) = A at hrect
    change (1 / (2 * Real.pi * I)) • VerticalIntegral f c -
      (1 / (2 * Real.pi * I)) • VerticalIntegral f d =
        A + (1 / (2 * Real.pi * I)) •
          (UpperUIntegral f d c H - LowerUIntegral f d c H)
    have hsum : VerticalIntegral f c - VerticalIntegral f d =
        RectangleIntegral f ((d : ℂ) - (H : ℂ) * I)
            ((c : ℂ) + (H : ℂ) * I) +
          (UpperUIntegral f d c H - LowerUIntegral f d c H) := by
      linear_combination hdiff'
    calc
      (1 / (2 * Real.pi * I)) • VerticalIntegral f c -
          (1 / (2 * Real.pi * I)) • VerticalIntegral f d =
          (1 / (2 * Real.pi * I)) •
            (VerticalIntegral f c - VerticalIntegral f d) := by module
      _ = (1 / (2 * Real.pi * I)) •
            (RectangleIntegral f ((d : ℂ) - (H : ℂ) * I)
                ((c : ℂ) + (H : ℂ) * I) +
              (UpperUIntegral f d c H - LowerUIntegral f d c H)) := by
        rw [hsum]
      _ = A + (1 / (2 * Real.pi * I)) •
            (UpperUIntegral f d c H - LowerUIntegral f d c H) := by
        rw [smul_add, hrect]
  have hLeft : Tendsto (fun _H : ℝ =>
      VerticalIntegral' f c - VerticalIntegral' f d) atTop
      (𝓝 (VerticalIntegral' f c - VerticalIntegral' f d)) := tendsto_const_nhds
  have hRight : Tendsto (fun H : ℝ =>
      A + (1 / (2 * Real.pi * I)) •
        (UpperUIntegral f d c H - LowerUIntegral f d c H)) atTop (𝓝 A) := by
    simpa [f, A] using tendsto_const_nhds.add hTails
  have hLeftAsRight := hLeft.congr' hEq
  have hFinal : VerticalIntegral' f c - VerticalIntegral' f d = A :=
    tendsto_nhds_unique hLeftAsRight hRight
  simpa [f, A] using hFinal

/-- The left vertical Estermann integrand after the source functional
equation.  This is an exact pointwise equality, not an asymptotic estimate. -/
theorem periodicEstermann_mul_leftLine_reflection
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (G : ℂ → ℂ)
    {d u : ℝ} (hd : d < 0) :
    periodicEstermann q Φ ((d : ℂ) + (u : ℂ) * I) *
        G ((d : ℂ) + (u : ℂ) * I) =
      periodicEstermannDual q Φ (((1 - d : ℝ) : ℂ) - (u : ℂ) * I) *
        G ((d : ℂ) + (u : ℂ) * I) := by
  rw [periodicEstermann_leftLine_reflection q Φ hd]

/-- The reflected analytic function whose right-half-plane Dirichlet
series produces the Voronoi dual sums. -/
noncomputable def periodicEstermannReflectedIntegrand
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (G : ℂ → ℂ) (s : ℂ) : ℂ :=
  periodicEstermannDual q Φ (1 - s) * G s

/-- Exact equality of the left vertical contour with its functional-equation
transform. -/
theorem periodicEstermann_leftVertical_eq_reflected
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (G : ℂ → ℂ)
    {d : ℝ} (hd : d < 0) :
    VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s) d =
      VerticalIntegral' (periodicEstermannReflectedIntegrand q Φ G) d := by
  unfold VerticalIntegral' VerticalIntegral
  congr 2
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [periodicEstermann_mul_leftLine_reflection q Φ G hd]
  unfold periodicEstermannReflectedIntegrand
  congr 2
  push_cast
  ring

/-- A smooth weighted divisor sum with periodic coefficient. -/
noncomputable def periodicDivisorWeightedSum (q : ℕ)
    (Φ : ZMod q → ℂ) (g : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, periodicDivisorCoeff q Φ n * g n

/-- The individual Mellin-line summand whose sum is the Estermann
integrand. -/
noncomputable def periodicDivisorMellinTerm (q : ℕ)
    (Φ : ZMod q → ℂ) (g : ℝ → ℂ) (σ : ℝ) (n : ℕ) (u : ℝ) : ℂ :=
  LSeries.term (periodicDivisorCoeff q Φ)
      ((σ : ℂ) + (u : ℂ) * I) n *
    mellin g ((σ : ℂ) + (u : ℂ) * I)

/-- Termwise Mellin inversion, including the `n=0` convention of the
divisor coefficient. -/
theorem periodicDivisorCoeff_mul_mellinInv
    (q : ℕ) (Φ : ZMod q → ℂ) (g : ℝ → ℂ) (σ : ℝ)
    (n : ℕ) :
    periodicDivisorCoeff q Φ n * mellinInv σ (mellin g) n =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ, periodicDivisorMellinTerm q Φ g σ n u := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [periodicDivisorCoeff, periodicDivisorMellinTerm, mellinInv,
      LSeries.term_zero]
  · unfold mellinInv periodicDivisorMellinTerm
    simp only [smul_eq_mul, Complex.real_smul, ofReal_div, ofReal_one,
      ofReal_mul]
    change periodicDivisorCoeff q Φ n *
        ((1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
          ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) *
            mellin g ((σ : ℂ) + (y : ℂ) * I)) = _
    rw [show periodicDivisorCoeff q Φ n *
        ((1 / (2 * Real.pi) : ℂ) * ∫ y : ℝ,
          ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I)) *
            mellin g ((σ : ℂ) + (y : ℂ) * I)) =
        (1 / (2 * Real.pi) : ℂ) * periodicDivisorCoeff q Φ n *
          ∫ y : ℝ, ((n : ℝ) : ℂ) ^
            (-((σ : ℂ) + (y : ℂ) * I)) *
              mellin g ((σ : ℂ) + (y : ℂ) * I) by ring,
      mul_assoc, ← MeasureTheory.integral_const_mul]
    congr 2
    funext u
    rw [LSeries.term_of_ne_zero hn]
    rw [show ((n : ℝ) : ℂ) = (n : ℂ) by norm_cast, cpow_neg,
      div_eq_mul_inv]
    ring

/-- Exact right-line Mellin identity for the periodic divisor sum.  This is
the starting equality of the divisor Voronoi formula. -/
theorem periodicDivisorWeightedSum_eq_estermannIntegral
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (g : ℝ → ℂ)
    (σ : ℝ) (hσ : 1 < σ)
    (hInv : ∀ n : ℕ, 0 < n → mellinInv σ (mellin g) n = g n)
    (hInt : ∀ n : ℕ, Integrable (periodicDivisorMellinTerm q Φ g σ n))
    (hSum : Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖periodicDivisorMellinTerm q Φ g σ n u‖)) :
    periodicDivisorWeightedSum q Φ g =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ u : ℝ, periodicEstermann q Φ
          ((σ : ℂ) + (u : ℂ) * I) *
          mellin g ((σ : ℂ) + (u : ℂ) * I) := by
  have hInvAll : ∀ n : ℕ,
      periodicDivisorCoeff q Φ n * g n =
        periodicDivisorCoeff q Φ n * mellinInv σ (mellin g) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [periodicDivisorCoeff]
    · rw [hInv n (Nat.pos_of_ne_zero hn)]
  unfold periodicDivisorWeightedSum
  simp_rw [hInvAll, periodicDivisorCoeff_mul_mellinInv]
  rw [tsum_mul_left]
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm hInt hSum]
  congr 2
  funext u
  rw [periodicEstermann_eq_LSeries q Φ (by simpa using hσ)]
  unfold LSeries periodicDivisorMellinTerm
  rw [tsum_mul_right]

/-- The right-line Mellin identity in the repository's normalized vertical
contour notation. -/
theorem periodicDivisorWeightedSum_eq_verticalIntegral
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (g : ℝ → ℂ)
    (σ : ℝ) (hσ : 1 < σ)
    (hInv : ∀ n : ℕ, 0 < n → mellinInv σ (mellin g) n = g n)
    (hInt : ∀ n : ℕ, Integrable (periodicDivisorMellinTerm q Φ g σ n))
    (hSum : Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖periodicDivisorMellinTerm q Φ g σ n u‖)) :
    periodicDivisorWeightedSum q Φ g =
      VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * mellin g s) σ := by
  rw [periodicDivisorWeightedSum_eq_estermannIntegral
    q Φ g σ hσ hInv hInt hSum]
  unfold VerticalIntegral' VerticalIntegral
  simp only [smul_eq_mul]
  rw [MeasureTheory.integral_congr_ae]
  · field_simp [Real.pi_ne_zero]
  · filter_upwards with u
    rfl

/-- Exact periodic divisor Voronoi formula in Mellin--Barnes form.  The
first two terms are the complete logarithmic main term; the last vertical
integral is the reflected four-kernel dual contribution. -/
theorem periodicDivisorVoronoi_mellinBarnes
    (q : ℕ) [NeZero q] (Φ : ZMod q → ℂ) (g : ℝ → ℂ)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    {d c : ℝ} (hd : d < 0) (hc : 1 < c)
    (hMellin : G = mellin g)
    (hInv : ∀ n : ℕ, 0 < n → mellinInv c (mellin g) n = g n)
    (hTermInt : ∀ n : ℕ, Integrable (periodicDivisorMellinTerm q Φ g c n))
    (hTermSum : Summable (fun n : ℕ =>
      ∫ u : ℝ, ‖periodicDivisorMellinTerm q Φ g c n u‖))
    (hIntD : Integrable (fun u : ℝ =>
      periodicEstermann q Φ ((d : ℂ) + (u : ℂ) * I) *
        G ((d : ℂ) + (u : ℂ) * I)))
    (hIntC : Integrable (fun u : ℝ =>
      periodicEstermann q Φ ((c : ℂ) + (u : ℂ) * I) *
        G ((c : ℂ) + (u : ℂ) * I)))
    (hTails : Tendsto (fun H : ℝ =>
      (1 / (2 * Real.pi * I)) •
        (UpperUIntegral (fun s : ℂ => periodicEstermann q Φ s * G s) d c H -
          LowerUIntegral (fun s : ℂ => periodicEstermann q Φ s * G s) d c H))
      atTop (𝓝 0)) :
    periodicDivisorWeightedSum q Φ g =
      periodicEstermannPoleCleared q Φ 1 * deriv G 1 +
        periodicEstermannResidueCoeff q Φ * G 1 +
        VerticalIntegral' (periodicEstermannReflectedIntegrand q Φ G) d := by
  have hEntry := periodicDivisorWeightedSum_eq_verticalIntegral
    q Φ g c hc hInv hTermInt hTermSum
  rw [← hMellin] at hEntry
  have hd1 : d < 1 := hd.trans zero_lt_one
  have hShift := periodicEstermann_mul_vertical_shift
    q Φ G hG hd1 hc hIntD hIntC hTails
  have hReflect := periodicEstermann_leftVertical_eq_reflected q Φ G hd
  rw [hEntry]
  calc
    VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s) c =
        (VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s) c -
          VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s) d) +
          VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s) d := by ring
    _ = (periodicEstermannPoleCleared q Φ 1 * deriv G 1 +
          periodicEstermannResidueCoeff q Φ * G 1) +
          VerticalIntegral' (fun s : ℂ => periodicEstermann q Φ s * G s) d := by
      rw [hShift]
    _ = _ := by rw [hReflect]

end RiemannZeta.GuthMaynard
