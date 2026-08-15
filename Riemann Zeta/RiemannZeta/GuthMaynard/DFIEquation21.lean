import RiemannZeta.GuthMaynard.DFIWeight
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Const

open Set
open scoped ContDiff

namespace RiemannZeta.GuthMaynard

noncomputable def dfiLocalizedWeight
    (f : ℝ → ℝ → ℂ) (φ : ℝ → ℂ) (h : ℝ) (x y : ℝ) : ℂ :=
  f x y * φ (x - y - h)

noncomputable def dfiPartialY (n : ℕ) (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  n.rec g (fun _ prior p => fderiv ℝ prior p (0, 1))

noncomputable def dfiPartialX (n : ℕ) (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  n.rec g (fun _ prior p => fderiv ℝ prior p (1, 0))

theorem contDiff_dfiPartialY (n : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (dfiPartialY n g) := by
  induction n with
  | zero => simpa [dfiPartialY] using hg
  | succ n ih =>
      rw [dfiPartialY]
      exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem dfiPartialY_apply (n : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (x y : ℝ) :
    dfiPartialY n g (x, y) = iteratedDeriv n (fun y' => g (x, y')) y := by
  induction n generalizing x y with
  | zero => simp [dfiPartialY]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      change fderiv ℝ (dfiPartialY n g) (x, y) (0, 1) = _
      have hprior := contDiff_dfiPartialY n hg
      have hc := (hprior.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y
        (hasFDerivAt_prodMk_right x y)
      have hd := hc.hasDerivAt
      have hfun : (fun y' => iteratedDeriv n (fun z => g (x, z)) y') =
          fun y' => dfiPartialY n g (x, y') := by
        funext y'
        exact (ih x y').symm
      calc
        fderiv ℝ (dfiPartialY n g) (x, y) (0, 1) =
            deriv (fun y' => dfiPartialY n g (x, y')) y := by
              simpa [Function.comp_def] using hd.deriv.symm
        _ = deriv (fun y' => iteratedDeriv n (fun z => g (x, z)) y') y :=
          congrArg (fun k : ℝ → ℂ => deriv k y) hfun.symm

theorem contDiff_dfiPartialX (n : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (dfiPartialX n g) := by
  induction n with
  | zero => simpa [dfiPartialX] using hg
  | succ n ih =>
      rw [dfiPartialX]
      exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem dfiPartialX_apply (n : ℕ) {g : ℝ × ℝ → ℂ}
    (hg : ContDiff ℝ ∞ g) (x y : ℝ) :
    dfiPartialX n g (x, y) = iteratedDeriv n (fun x' => g (x', y)) x := by
  induction n generalizing x y with
  | zero => simp [dfiPartialX]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      change fderiv ℝ (dfiPartialX n g) (x, y) (1, 0) = _
      have hprior := contDiff_dfiPartialX n hg
      have hc := (hprior.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left x y)
      have hd := hc.hasDerivAt
      have hfun : (fun x' => iteratedDeriv n (fun z => g (z, y)) x') =
          fun x' => dfiPartialX n g (x', y) := by
        funext x'
        exact (ih x' y).symm
      calc
        fderiv ℝ (dfiPartialX n g) (x, y) (1, 0) =
            deriv (fun x' => dfiPartialX n g (x', y)) x := by
              simpa [Function.comp_def] using hd.deriv.symm
        _ = deriv (fun x' => iteratedDeriv n (fun z => g (z, y)) x') x :=
          congrArg (fun k : ℝ → ℂ => deriv k x) hfun.symm

theorem tsupport_dfiPartialY_subset (n : ℕ) (g : ℝ × ℝ → ℂ) :
    tsupport (dfiPartialY n g) ⊆ tsupport g := by
  induction n with
  | zero => simp [dfiPartialY]
  | succ n ih =>
      exact (tsupport_fderiv_apply_subset ℝ (0, 1)).trans ih

theorem tsupport_dfiPartialX_subset (n : ℕ) (g : ℝ × ℝ → ℂ) :
    tsupport (dfiPartialX n g) ⊆ tsupport g := by
  induction n with
  | zero => simp [dfiPartialX]
  | succ n ih =>
      exact (tsupport_fderiv_apply_subset ℝ (1, 0)).trans ih

theorem dfiMixedDeriv_eq_partialXY
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (i j : ℕ) (x y : ℝ) :
    dfiMixedDeriv i j f x y =
      dfiPartialX i (dfiPartialY j (Function.uncurry f)) (x, y) := by
  rw [dfiPartialX_apply i (contDiff_dfiPartialY j hf)]
  unfold dfiMixedDeriv
  congr 2
  funext x'
  simpa using (dfiPartialY_apply j hf x' y).symm

/-- Every mixed derivative of a smooth two-variable weight is again smooth
as a function on the product. -/
theorem contDiff_uncurry_dfiMixedDeriv
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (i j : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (dfiMixedDeriv i j f)) := by
  have heq : Function.uncurry (dfiMixedDeriv i j f) =
      dfiPartialX i (dfiPartialY j (Function.uncurry f)) := by
    funext p
    exact dfiMixedDeriv_eq_partialXY hf i j p.1 p.2
  rw [heq]
  exact contDiff_dfiPartialX i (contDiff_dfiPartialY j hf)

theorem support_dfiMixedDeriv_subset_tsupport
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (i j : ℕ) :
    Function.support (Function.uncurry (dfiMixedDeriv i j f)) ⊆
      tsupport (Function.uncurry f) := by
  intro p hp
  rcases p with ⟨x, y⟩
  have hne : dfiPartialX i (dfiPartialY j (Function.uncurry f)) (x, y) ≠ 0 := by
    simpa [dfiMixedDeriv_eq_partialXY hf] using hp
  have hpX : (x, y) ∈ tsupport
      (dfiPartialX i (dfiPartialY j (Function.uncurry f))) :=
    subset_tsupport _ hne
  have hpY : (x, y) ∈ tsupport (dfiPartialY j (Function.uncurry f)) :=
    tsupport_dfiPartialX_subset i _ hpX
  exact tsupport_dfiPartialY_subset j _ hpY

theorem contDiff_slice_left
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (y : ℝ) :
    ContDiff ℝ ∞ (fun x => f x y) := by
  exact hf.comp (contDiff_prodMk_left y)

theorem contDiff_slice_right
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (x : ℝ) :
    ContDiff ℝ ∞ (f x) := by
  exact hf.comp (contDiff_prodMk_right x)

theorem contDiff_iteratedDeriv_slice_right
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (s : ℕ) (y : ℝ) :
    ContDiff ℝ ∞ (fun x => iteratedDeriv s (f x) y) := by
  have hp : ContDiff ℝ ∞
      (fun x => dfiPartialY s (Function.uncurry f) (x, y)) :=
    (contDiff_dfiPartialY s hf).comp (contDiff_prodMk_left y)
  convert hp using 1
  funext x
  simpa using (dfiPartialY_apply s hf x y).symm

theorem iteratedDeriv_difference_cutoff_y
    (φ : ℝ → ℂ) (h x y : ℝ) (j : ℕ) :
    iteratedDeriv j (fun y' => φ (x - y' - h)) y =
      ((-1 : ℝ) ^ j) • iteratedDeriv j φ (x - y - h) := by
  have hfun : (fun y' : ℝ => φ (x - y' - h)) =
      fun y' : ℝ => φ ((x - h) - y') := by
    funext y'
    congr 1
    ring
  rw [hfun, iteratedDeriv_comp_const_sub]
  ring

theorem iteratedDeriv_difference_cutoff_x
    (φ : ℝ → ℂ) (h y x : ℝ) (i : ℕ) :
    iteratedDeriv i (fun x' => φ (x' - y - h)) x =
      iteratedDeriv i φ (x - y - h) := by
  have hfun : (fun x' : ℝ => φ (x' - y - h)) =
      fun x' : ℝ => φ (x' - (y + h)) := by
    funext x'
    congr 1
    ring
  rw [hfun, iteratedDeriv_comp_sub_const]
  ring

theorem iteratedDeriv_iteratedDeriv (m n : ℕ) (φ : ℝ → ℂ) (x : ℝ) :
    iteratedDeriv m (iteratedDeriv n φ) x = iteratedDeriv (m + n) φ x := by
  simp only [iteratedDeriv_eq_iterate]
  exact (Function.iterate_add_apply deriv m n φ).symm ▸ rfl

theorem ContDiff.contDiff_iteratedDeriv_top
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n φ) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _hm
  have hlt : ((m + n : ℕ) : ℕ∞ω) < ∞ :=
    ENat.natCast_lt_of_coe_top_le_withTop le_rfl (m + n)
  have hd := hφ.differentiable_iteratedDeriv (m + n) hlt
  convert hd using 1
  funext x
  exact iteratedDeriv_iteratedDeriv m n φ x

theorem iteratedDeriv_dfiLocalizedWeight_y
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hφ : ContDiff ℝ ∞ φ) (h x y : ℝ) (j : ℕ) :
    iteratedDeriv j (dfiLocalizedWeight f φ h x) y =
      ∑ s ∈ Finset.range (j + 1),
        (j.choose s : ℂ) * iteratedDeriv s (f x) y *
          (((-1 : ℝ) ^ (j - s)) •
            iteratedDeriv (j - s) φ (x - y - h)) := by
  have hfs : ContDiffAt ℝ j (f x) y :=
    ((contDiff_slice_right hf x).contDiffAt.of_le (by exact_mod_cast le_top))
  have hφs : ContDiffAt ℝ j (fun y' => φ (x - y' - h)) y := by
    have haff : ContDiff ℝ ∞ (fun y' : ℝ => x - y' - h) :=
      (contDiff_const.sub contDiff_id).sub contDiff_const
    exact (hφ.comp haff).contDiffAt.of_le (by exact_mod_cast le_top)
  change iteratedDeriv j ((f x) * fun y' => φ (x - y' - h)) y = _
  rw [iteratedDeriv_mul hfs hφs]
  apply Finset.sum_congr rfl
  intro s _hs
  rw [iteratedDeriv_difference_cutoff_y]

theorem iteratedDeriv_dfiMixedProduct_x
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hφ : ContDiff ℝ ∞ φ) (h x y : ℝ) (i s k : ℕ) :
    iteratedDeriv i
        (fun x' => iteratedDeriv s (f x') y *
          iteratedDeriv k φ (x' - y - h)) x =
      ∑ r ∈ Finset.range (i + 1),
        (i.choose r : ℂ) * dfiMixedDeriv r s f x y *
          iteratedDeriv ((i - r) + k) φ (x - y - h) := by
  have hfs : ContDiffAt ℝ i (fun x' => iteratedDeriv s (f x') y) x :=
    (contDiff_iteratedDeriv_slice_right hf s y).contDiffAt.of_le
      (by exact_mod_cast le_top)
  have hφs : ContDiffAt ℝ i
      (fun x' => iteratedDeriv k φ (x' - y - h)) x := by
    have haff : ContDiff ℝ ∞ (fun x' : ℝ => x' - y - h) :=
      (contDiff_id.sub contDiff_const).sub contDiff_const
    exact ((ContDiff.contDiff_iteratedDeriv_top hφ k).comp haff).contDiffAt.of_le
      (by exact_mod_cast le_top)
  change iteratedDeriv i
    ((fun x' => iteratedDeriv s (f x') y) *
      fun x' => iteratedDeriv k φ (x' - y - h)) x = _
  rw [iteratedDeriv_mul hfs hφs]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [show iteratedDeriv r (fun x' => iteratedDeriv s (f x') y) x =
      dfiMixedDeriv r s f x y by rfl]
  have hshift := iteratedDeriv_difference_cutoff_x
    (iteratedDeriv k φ) h y x (i - r)
  have hadd := iteratedDeriv_iteratedDeriv (i - r) k φ (x - y - h)
  rw [hshift, hadd]

theorem dfiEquation21Leibniz
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hφ : ContDiff ℝ ∞ φ) (h x y : ℝ) (i j : ℕ) :
    dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y =
      ∑ s ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (i + 1),
        (j.choose s : ℂ) * (i.choose r : ℂ) *
          (((-1 : ℝ) ^ (j - s)) : ℂ) *
          dfiMixedDeriv r s f x y *
          iteratedDeriv ((i - r) + (j - s)) φ (x - y - h) := by
  unfold dfiMixedDeriv
  have hyfun :
      (fun x' => iteratedDeriv j (dfiLocalizedWeight f φ h x') y) =
        fun x' => ∑ s ∈ Finset.range (j + 1),
          (j.choose s : ℂ) * iteratedDeriv s (f x') y *
            (((-1 : ℝ) ^ (j - s)) •
              iteratedDeriv (j - s) φ (x' - y - h)) := by
    funext x'
    exact iteratedDeriv_dfiLocalizedWeight_y hf hφ h x' y j
  rw [hyfun]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro s hs
    have hsmoothF := contDiff_iteratedDeriv_slice_right hf s y
    have hsmoothφ : ContDiff ℝ ∞
        (fun x' => iteratedDeriv (j - s) φ (x' - y - h)) := by
      have haff : ContDiff ℝ ∞ (fun x' : ℝ => x' - y - h) :=
        (contDiff_id.sub contDiff_const).sub contDiff_const
      exact (ContDiff.contDiff_iteratedDeriv_top hφ (j - s)).comp haff
    have hterm :
        (fun x' => (j.choose s : ℂ) * iteratedDeriv s (f x') y *
          (((-1 : ℝ) ^ (j - s)) •
            iteratedDeriv (j - s) φ (x' - y - h))) =
        fun x' => ((j.choose s : ℂ) * (((-1 : ℝ) ^ (j - s)) : ℂ)) *
          (iteratedDeriv s (f x') y *
            iteratedDeriv (j - s) φ (x' - y - h)) := by
      funext x'
      simp only [Complex.real_smul]
      push_cast
      ring
    rw [hterm]
    have hprodSmooth : ContDiffAt ℝ i
        (fun x' => iteratedDeriv s (f x') y *
          iteratedDeriv (j - s) φ (x' - y - h)) x :=
      (hsmoothF.mul hsmoothφ).contDiffAt.of_le (by exact_mod_cast le_top)
    rw [iteratedDeriv_const_mul _ hprodSmooth]
    rw [iteratedDeriv_dfiMixedProduct_x hf hφ]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    simp only [dfiMixedDeriv]
    ring
  · intro s _hs
    have hsmoothF := contDiff_iteratedDeriv_slice_right hf s y
    have hsmoothφ : ContDiff ℝ ∞
        (fun x' => iteratedDeriv (j - s) φ (x' - y - h)) := by
      have haff : ContDiff ℝ ∞ (fun x' : ℝ => x' - y - h) :=
        (contDiff_id.sub contDiff_const).sub contDiff_const
      exact (ContDiff.contDiff_iteratedDeriv_top hφ (j - s)).comp haff
    have hc₁ : ContDiff ℝ ∞ (fun _ : ℝ => (j.choose s : ℂ)) := contDiff_const
    have hc₂ : ContDiff ℝ ∞
        (fun _ : ℝ => ((((-1 : ℝ) ^ (j - s)) : ℝ) : ℂ)) := contDiff_const
    simpa only [Complex.real_smul, map_pow] using
      ((hc₁.mul hsmoothF).mul (hc₂.mul hsmoothφ)).contDiffAt.of_le
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl i)

theorem norm_dfiMixedDeriv_localized_le
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hφ : ContDiff ℝ ∞ φ) {P X Y U Cf Cφ : ℝ}
    (hP : 0 ≤ P) (hX : 0 < X) (hY : 0 < Y)
    (hCf : 0 ≤ Cf)
    (i j : ℕ)
    (hfb : ∀ r ∈ Finset.range (i + 1), ∀ s ∈ Finset.range (j + 1), ∀ x y,
      ‖dfiMixedDeriv r s f x y‖ ≤ Cf * (P / X) ^ r * (P / Y) ^ s)
    (hφb : ∀ k ≤ i + j, ∀ z, ‖iteratedDeriv k φ z‖ ≤ Cφ * U⁻¹ ^ k)
    (h x y : ℝ) :
    ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
      Cf * Cφ * (P / X + U⁻¹) ^ i * (P / Y + U⁻¹) ^ j := by
  rw [dfiEquation21Leibniz hf hφ]
  calc
    ‖∑ s ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (i + 1),
        (j.choose s : ℂ) * (i.choose r : ℂ) *
          (((-1 : ℝ) ^ (j - s)) : ℂ) *
          dfiMixedDeriv r s f x y *
          iteratedDeriv (i - r + (j - s)) φ (x - y - h)‖ ≤
      ∑ s ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (i + 1),
        ‖(j.choose s : ℂ) * (i.choose r : ℂ) *
          (((-1 : ℝ) ^ (j - s)) : ℂ) *
          dfiMixedDeriv r s f x y *
          iteratedDeriv (i - r + (j - s)) φ (x - y - h)‖ := by
            exact norm_sum_le _ _ |>.trans (Finset.sum_le_sum fun s _ => norm_sum_le _ _)
    _ ≤ ∑ s ∈ Finset.range (j + 1), ∑ r ∈ Finset.range (i + 1),
        (j.choose s : ℝ) * (i.choose r : ℝ) *
          (Cf * (P / X) ^ r * (P / Y) ^ s) *
          (Cφ * U⁻¹ ^ (i - r + (j - s))) := by
      apply Finset.sum_le_sum
      intro s hs
      apply Finset.sum_le_sum
      intro r hr
      simp only [norm_mul, Complex.norm_natCast, norm_pow]
      have hsign : ‖(((-1 : ℝ) : ℂ))‖ ^ (j - s) = 1 := by norm_num
      rw [hsign, mul_one]
      have hcoeff : 0 ≤ (j.choose s : ℝ) * (i.choose r : ℝ) := by positivity
      have hFnonneg : 0 ≤ Cf * (P / X) ^ r * (P / Y) ^ s := by positivity
      calc
        (j.choose s : ℝ) * (i.choose r : ℝ) *
            ‖dfiMixedDeriv r s f x y‖ *
            ‖iteratedDeriv (i - r + (j - s)) φ (x - y - h)‖ ≤
          (j.choose s : ℝ) * (i.choose r : ℝ) *
            (Cf * (P / X) ^ r * (P / Y) ^ s) *
            ‖iteratedDeriv (i - r + (j - s)) φ (x - y - h)‖ := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left (hfb r hr s hs x y) hcoeff) (norm_nonneg _)
        _ ≤ (j.choose s : ℝ) * (i.choose r : ℝ) *
            (Cf * (P / X) ^ r * (P / Y) ^ s) *
            (Cφ * U⁻¹ ^ (i - r + (j - s))) := by
              have hk : i - r + (j - s) ≤ i + j := by omega
              exact mul_le_mul_of_nonneg_left (hφb _ hk _)
                (mul_nonneg hcoeff hFnonneg)
    _ = Cf * Cφ * (P / X + U⁻¹) ^ i * (P / Y + U⁻¹) ^ j := by
      rw [add_pow, add_pow]
      simp only [Finset.sum_mul, Finset.mul_sum]
      ring_nf
      apply Finset.sum_congr rfl
      intro s _hs
      apply Finset.sum_congr rfl
      intro r _hr
      ring

/-- The dyadic localization made immediately before DFI equation (21). -/
structure DFILocalizedBox (f : ℝ → ℝ → ℂ) (X Y : ℝ) : Prop where
  support_subset : Function.support (Function.uncurry f) ⊆
    Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y)

/-- The redundant smooth factor introduced before DFI equation (21). -/
structure DFIRedundantCutoff (φ : ℝ → ℂ) (U : ℝ) : Prop where
  U_pos : 0 < U
  smooth : ContDiff ℝ ∞ φ
  compactSupport : HasCompactSupport φ
  support_subset : Function.support φ ⊆ Set.Ioo (-U) U
  value_zero : φ 0 = 1
  derivativeBound : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ z : ℝ, ‖iteratedDeriv k φ z‖ ≤ C * U⁻¹ ^ k

/-- Explicit equation-(21) cutoff derivative constants.  A uniform source
family fixes `D` before varying `U`; this prevents a scale-dependent
existential constant from masquerading as DFI's implicit constant. -/
structure DFIRedundantCutoffProfile {φ : ℝ → ℂ} {U : ℝ}
    (hφ : DFIRedundantCutoff φ U) (D : ℕ → ℝ) : Prop where
  positive : ∀ k, 0 < D k
  bound : ∀ k z, ‖iteratedDeriv k φ z‖ ≤ D k * U⁻¹ ^ k

theorem DFIRedundantCutoff.exists_profile
    {φ : ℝ → ℂ} {U : ℝ} (hφ : DFIRedundantCutoff φ U) :
    ∃ D : ℕ → ℝ, DFIRedundantCutoffProfile hφ D := by
  choose D hD hbound using hφ.derivativeBound
  exact ⟨D, hD, hbound⟩

noncomputable def dfiCutoffFiniteConstant (D : ℕ → ℝ) (J : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (J + 1), D k

theorem DFIRedundantCutoffProfile.le_finiteConstant
    {φ : ℝ → ℂ} {U : ℝ} {hφ : DFIRedundantCutoff φ U}
    {D : ℕ → ℝ} (hD : DFIRedundantCutoffProfile hφ D)
    {k J : ℕ} (hk : k ≤ J) :
    D k ≤ dfiCutoffFiniteConstant D J := by
  unfold dfiCutoffFiniteConstant
  exact Finset.single_le_sum (fun l _hl ↦ (hD.positive l).le) (by simp [hk])

theorem DFIEquation2.localized_derivative_bound
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} (hf : DFIEquation2 f P X Y)
    (hbox : DFILocalizedBox f X Y) (r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      ‖dfiMixedDeriv r s f x y‖ ≤ C * (P / X) ^ r * (P / Y) ^ s := by
  obtain ⟨C, hC, hbound⟩ := hf.derivativeBound r s
  refine ⟨C, hC, fun x y => ?_⟩
  by_cases hzero : dfiMixedDeriv r s f x y = 0
  · rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg hC.le (pow_nonneg (div_nonneg
        (zero_le_one.trans hf.one_le_P) (zero_le_one.trans hf.one_le_X)) _))
      (pow_nonneg (div_nonneg
        (zero_le_one.trans hf.one_le_P) (zero_le_one.trans hf.one_le_Y)) _)
  have hmemSupport : (x, y) ∈
      Function.support (Function.uncurry (dfiMixedDeriv r s f)) := by
    exact hzero
  have hts : tsupport (Function.uncurry f) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
    closure_minimal hbox.support_subset (isClosed_Icc.prod isClosed_Icc)
  have hxy := hts (support_dfiMixedDeriv_subset_tsupport hf.smooth r s hmemSupport)
  have hxX : X ≤ x := hxy.1.1
  have hyY : Y ≤ y := hxy.2.1
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hf.one_le_X
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one hf.one_le_Y
  have hx : 0 < x := hX.trans_le hxX
  have hy : 0 < y := hY.trans_le hyY
  have hdecX0 : 0 ≤ (1 + x / X)⁻¹ := by positivity
  have hdecY0 : 0 ≤ (1 + y / Y)⁻¹ := by positivity
  have hdecX1 : (1 + x / X)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by
      have : 0 ≤ x / X := div_nonneg hx.le hX.le
      linarith)
  have hdecY1 : (1 + y / Y)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by
      have : 0 ≤ y / Y := div_nonneg hy.le hY.le
      linarith)
  have hP : 0 ≤ P := zero_le_one.trans hf.one_le_P
  have hraw : x ^ r * y ^ s * ‖dfiMixedDeriv r s f x y‖ ≤
      C * P ^ (r + s) := by
    calc
      x ^ r * y ^ s * ‖dfiMixedDeriv r s f x y‖ =
          |x| ^ r * |y| ^ s * ‖dfiMixedDeriv r s f x y‖ := by
            rw [abs_of_pos hx, abs_of_pos hy]
      _ ≤ C * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (r + s) :=
        hbound x y hx hy
      _ ≤ C * 1 * 1 * P ^ (r + s) := by gcongr
      _ = C * P ^ (r + s) := by ring
  have hxpow : 0 < x ^ r := pow_pos hx _
  have hypow : 0 < y ^ s := pow_pos hy _
  have hXpow : 0 < X ^ r := pow_pos hX _
  have hYpow : 0 < Y ^ s := pow_pos hY _
  have hdivide : ‖dfiMixedDeriv r s f x y‖ ≤
      C * P ^ (r + s) / (x ^ r * y ^ s) := by
    apply (le_div_iff₀ (mul_pos hxpow hypow)).2
    nlinarith [hraw]
  have hdenom : X ^ r * Y ^ s ≤ x ^ r * y ^ s := by
    exact mul_le_mul (pow_le_pow_left₀ hX.le hxX r)
      (pow_le_pow_left₀ hY.le hyY s) (pow_nonneg hY.le _)
      (pow_nonneg hx.le _)
  calc
    ‖dfiMixedDeriv r s f x y‖ ≤
        C * P ^ (r + s) / (x ^ r * y ^ s) := hdivide
    _ ≤ C * P ^ (r + s) / (X ^ r * Y ^ s) :=
      div_le_div_of_nonneg_left (mul_nonneg hC.le (pow_nonneg hP _))
        (mul_pos hXpow hYpow) hdenom
    _ = C * (P / X) ^ r * (P / Y) ^ s := by
      rw [pow_add, div_pow, div_pow]
      field_simp [hX.ne', hY.ne']

/-- Profile-explicit version of the localized derivative estimate.  Unlike
`DFIEquation2.localized_derivative_bound`, its constant is the actual
equation-(2) profile entry, so it remains uniform when `P`, `X`, `Y`, and
the test function vary through a source family with a common profile. -/
theorem DFIEquation2Profile.localized_derivative_bound
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} {C : ℕ → ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hC : DFIEquation2Profile f P X Y C)
    (hbox : DFILocalizedBox f X Y) (r s : ℕ) (x y : ℝ) :
    ‖dfiMixedDeriv r s f x y‖ ≤
      C r s * (P / X) ^ r * (P / Y) ^ s := by
  by_cases hzero : dfiMixedDeriv r s f x y = 0
  · rw [hzero, norm_zero]
    exact mul_nonneg
      (mul_nonneg (hC.positive r s).le (pow_nonneg (div_nonneg
        (zero_le_one.trans hf.one_le_P) (zero_le_one.trans hf.one_le_X)) _))
      (pow_nonneg (div_nonneg
        (zero_le_one.trans hf.one_le_P) (zero_le_one.trans hf.one_le_Y)) _)
  have hmemSupport : (x, y) ∈
      Function.support (Function.uncurry (dfiMixedDeriv r s f)) := hzero
  have hts : tsupport (Function.uncurry f) ⊆
      Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
    closure_minimal hbox.support_subset (isClosed_Icc.prod isClosed_Icc)
  have hxy := hts
    (support_dfiMixedDeriv_subset_tsupport hf.smooth r s hmemSupport)
  have hxX : X ≤ x := hxy.1.1
  have hyY : Y ≤ y := hxy.2.1
  have hX : 0 < X := lt_of_lt_of_le zero_lt_one hf.one_le_X
  have hY : 0 < Y := lt_of_lt_of_le zero_lt_one hf.one_le_Y
  have hx : 0 < x := hX.trans_le hxX
  have hy : 0 < y := hY.trans_le hyY
  have hdecX0 : 0 ≤ (1 + x / X)⁻¹ := by positivity
  have hdecY0 : 0 ≤ (1 + y / Y)⁻¹ := by positivity
  have hdecX1 : (1 + x / X)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by
      have : 0 ≤ x / X := div_nonneg hx.le hX.le
      linarith)
  have hdecY1 : (1 + y / Y)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by
      have : 0 ≤ y / Y := div_nonneg hy.le hY.le
      linarith)
  have hC0 : 0 ≤ C r s := (hC.positive r s).le
  have hP : 0 ≤ P := zero_le_one.trans hf.one_le_P
  have hraw : x ^ r * y ^ s * ‖dfiMixedDeriv r s f x y‖ ≤
      C r s * P ^ (r + s) := by
    calc
      x ^ r * y ^ s * ‖dfiMixedDeriv r s f x y‖ =
          |x| ^ r * |y| ^ s * ‖dfiMixedDeriv r s f x y‖ := by
            rw [abs_of_pos hx, abs_of_pos hy]
      _ ≤ C r s * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (r + s) :=
        hC.bound r s x y hx hy
      _ ≤ C r s * 1 * 1 * P ^ (r + s) := by gcongr
      _ = C r s * P ^ (r + s) := by ring
  have hxpow : 0 < x ^ r := pow_pos hx _
  have hypow : 0 < y ^ s := pow_pos hy _
  have hXpow : 0 < X ^ r := pow_pos hX _
  have hYpow : 0 < Y ^ s := pow_pos hY _
  have hdivide : ‖dfiMixedDeriv r s f x y‖ ≤
      C r s * P ^ (r + s) / (x ^ r * y ^ s) := by
    apply (le_div_iff₀ (mul_pos hxpow hypow)).2
    nlinarith [hraw]
  have hdenom : X ^ r * Y ^ s ≤ x ^ r * y ^ s := by
    exact mul_le_mul (pow_le_pow_left₀ hX.le hxX r)
      (pow_le_pow_left₀ hY.le hyY s) (pow_nonneg hY.le _)
      (pow_nonneg hx.le _)
  calc
    ‖dfiMixedDeriv r s f x y‖ ≤
        C r s * P ^ (r + s) / (x ^ r * y ^ s) := hdivide
    _ ≤ C r s * P ^ (r + s) / (X ^ r * Y ^ s) :=
      div_le_div_of_nonneg_left
        (mul_nonneg (hC.positive r s).le (pow_nonneg hP _))
        (mul_pos hXpow hYpow) hdenom
    _ = C r s * (P / X) ^ r * (P / Y) ^ s := by
      rw [pow_add, div_pow, div_pow]
      field_simp [hX.ne', hY.ne']

/-- A single explicit equation-(2) profile constant controls every mixed
derivative through the requested rectangle of orders. -/
theorem DFIEquation2Profile.uniform_localized_derivative_bound
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} {C : ℕ → ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hC : DFIEquation2Profile f P X Y C)
    (hbox : DFILocalizedBox f X Y) {i j r s : ℕ}
    (hr : r ≤ i) (hs : s ≤ j) (x y : ℝ) :
    ‖dfiMixedDeriv r s f x y‖ ≤
      dfiEquation2FiniteConstant C (max i j) *
        (P / X) ^ r * (P / Y) ^ s := by
  have hrs : C r s ≤ dfiEquation2FiniteConstant C (max i j) :=
    hC.le_finiteConstant (hr.trans (le_max_left _ _))
      (hs.trans (le_max_right _ _))
  exact (hC.localized_derivative_bound hf hbox r s x y).trans (by
    have hPX : 0 ≤ (P / X) ^ r := pow_nonneg
      (div_nonneg (zero_le_one.trans hf.one_le_P)
        (zero_le_one.trans hf.one_le_X)) _
    have hPY : 0 ≤ (P / Y) ^ s := pow_nonneg
      (div_nonneg (zero_le_one.trans hf.one_le_P)
        (zero_le_one.trans hf.one_le_Y)) _
    gcongr)

theorem DFIEquation2.exists_uniform_localized_derivative_bound
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} (hf : DFIEquation2 f P X Y)
    (hbox : DFILocalizedBox f X Y) (i j : ℕ) :
    ∃ Cf : ℝ, 0 < Cf ∧
      ∀ r ∈ Finset.range (i + 1), ∀ s ∈ Finset.range (j + 1), ∀ x y,
        ‖dfiMixedDeriv r s f x y‖ ≤
          Cf * (P / X) ^ r * (P / Y) ^ s := by
  choose C hC hbound using fun r s => hf.localized_derivative_bound hbox r s
  let Cf := ∑ r ∈ Finset.range (i + 1), ∑ s ∈ Finset.range (j + 1), C r s
  have hCf : 0 < Cf := by
    dsimp [Cf]
    have hinner : ∀ r ∈ Finset.range (i + 1),
        0 < ∑ s ∈ Finset.range (j + 1), C r s := by
      intro r _hr
      exact Finset.sum_pos (fun s _hs => hC r s) ⟨0, by simp⟩
    exact Finset.sum_pos hinner ⟨0, by simp⟩
  refine ⟨Cf, hCf, fun r hr s hs x y => ?_⟩
  have hC_le : C r s ≤ Cf := by
    dsimp [Cf]
    exact (Finset.single_le_sum (fun t _ => (hC r t).le) hs).trans
      (Finset.single_le_sum (fun t _ => (Finset.sum_nonneg fun u _ => (hC t u).le)) hr)
  have hPX : 0 ≤ (P / X) ^ r := pow_nonneg
    (div_nonneg (zero_le_one.trans hf.one_le_P) (zero_le_one.trans hf.one_le_X)) _
  have hPY : 0 ≤ (P / Y) ^ s := pow_nonneg
    (div_nonneg (zero_le_one.trans hf.one_le_P) (zero_le_one.trans hf.one_le_Y)) _
  exact (hbound r s x y).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC_le hPX) hPY)

theorem DFIRedundantCutoff.exists_uniform_derivative_bound
    {φ : ℝ → ℂ} {U : ℝ} (hφ : DFIRedundantCutoff φ U) (n : ℕ) :
    ∃ Cφ : ℝ, 0 < Cφ ∧ ∀ k ≤ n, ∀ z,
      ‖iteratedDeriv k φ z‖ ≤ Cφ * U⁻¹ ^ k := by
  choose C hC hbound using hφ.derivativeBound
  let Cφ := ∑ k ∈ Finset.range (n + 1), C k
  have hCφ : 0 < Cφ := by
    dsimp [Cφ]
    exact Finset.sum_pos (fun _ _ => hC _) ⟨0, by simp⟩
  refine ⟨Cφ, hCφ, fun k hk z => ?_⟩
  have hkmem : k ∈ Finset.range (n + 1) := by simp [hk]
  have hC_le : C k ≤ Cφ := by
    dsimp [Cφ]
    exact Finset.single_le_sum (fun t _ => (hC t).le) hkmem
  exact (hbound k z).trans
    (mul_le_mul_of_nonneg_right hC_le (pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _))

theorem dfiLocalizedWeight_eq_of_sub_eq
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {U h x y : ℝ}
    (hφ : DFIRedundantCutoff φ U) (hxy : x - y = h) :
    dfiLocalizedWeight f φ h x y = f x y := by
  simp [dfiLocalizedWeight, hxy, hφ.value_zero]

/-- DFI equation (21), with both implicit constants represented by one
order-dependent positive constant.  The first estimate is the exact
two-variable Leibniz scale; the second is the paper's simplification under
`U ≤ P⁻¹ min(X,Y)`. -/
theorem dfiEquation21
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (h : ℝ) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℝ,
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        C * (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j ∧
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        C * U⁻¹ ^ (i + j) := by
  obtain ⟨Cf, hCf, hfb⟩ := hf.exists_uniform_localized_derivative_bound hbox i j
  obtain ⟨Cφ, hCφ, hφb⟩ := hφ.exists_uniform_derivative_bound (i + j)
  let C := Cf * Cφ * 2 ^ (i + j)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hUX : U * P ≤ X := by
    calc
      U * P ≤ (P⁻¹ * min X Y) * P :=
        mul_le_mul_of_nonneg_right hscale hP.le
      _ = min X Y := by field_simp [hP.ne']
      _ ≤ X := min_le_left _ _
  have hUY : U * P ≤ Y := by
    calc
      U * P ≤ (P⁻¹ * min X Y) * P :=
        mul_le_mul_of_nonneg_right hscale hP.le
      _ = min X Y := by field_simp [hP.ne']
      _ ≤ Y := min_le_right _ _
  have hPX : P / X ≤ U⁻¹ := by
    rw [div_le_iff₀ hX]
    rw [← div_eq_inv_mul]
    rw [le_div_iff₀ hφ.U_pos]
    nlinarith [hUX]
  have hPY : P / Y ≤ U⁻¹ := by
    rw [div_le_iff₀ hY]
    rw [← div_eq_inv_mul]
    rw [le_div_iff₀ hφ.U_pos]
    nlinarith [hUY]
  have hUinv : 0 ≤ U⁻¹ := inv_nonneg.mpr hφ.U_pos.le
  have hfactorX : 0 ≤ U⁻¹ + P / X := by positivity
  have hfactorY : 0 ≤ U⁻¹ + P / Y := by positivity
  have htwoX : U⁻¹ + P / X ≤ 2 * U⁻¹ := by linarith
  have htwoY : U⁻¹ + P / Y ≤ 2 * U⁻¹ := by linarith
  refine ⟨C, hC, fun x y => ?_⟩
  have hbase := norm_dfiMixedDeriv_localized_le hf.smooth hφ.smooth
    (zero_le_one.trans hf.one_le_P) hX hY hCf.le i j hfb hφb h x y
  have hbase' :
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        Cf * Cφ * (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j := by
    simpa [add_comm] using hbase
  constructor
  · exact hbase'.trans (by
      dsimp [C]
      have hone : (1 : ℝ) ≤ 2 ^ (i + j) := one_le_pow₀ (by norm_num)
      have hK : 0 ≤ Cf * Cφ := mul_nonneg hCf.le hCφ.le
      have hKC : Cf * Cφ ≤ Cf * Cφ * 2 ^ (i + j) :=
        le_mul_of_one_le_right hK hone
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKC (pow_nonneg hfactorX _))
        (pow_nonneg hfactorY _))
  · calc
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
          Cf * Cφ * (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j := hbase'
      _ ≤ Cf * Cφ * (2 * U⁻¹) ^ i * (2 * U⁻¹) ^ j := by gcongr
      _ = C * U⁻¹ ^ (i + j) := by
        dsimp [C]
        rw [mul_pow, mul_pow, pow_add, pow_add]
        ring

/-- Uniform-in-the-shift form of DFI equation (21).  The source derivative
constants and cutoff constants are chosen before the shift `h`; consequently
the displayed constant cannot depend on the additive-divisor shift. -/
theorem dfiEquation21_uniform_in_shift
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    (hf : DFIEquation2 f P X Y) (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U)
    (hscale : U ≤ P⁻¹ * min X Y) (i j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h x y : ℝ),
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        C * (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j ∧
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        C * U⁻¹ ^ (i + j) := by
  obtain ⟨Cf, hCf, hfb⟩ := hf.exists_uniform_localized_derivative_bound hbox i j
  obtain ⟨Cφ, hCφ, hφb⟩ := hφ.exists_uniform_derivative_bound (i + j)
  let C := Cf * Cφ * 2 ^ (i + j)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hUX : U * P ≤ X := by
    calc
      U * P ≤ (P⁻¹ * min X Y) * P :=
        mul_le_mul_of_nonneg_right hscale hP.le
      _ = min X Y := by field_simp [hP.ne']
      _ ≤ X := min_le_left _ _
  have hUY : U * P ≤ Y := by
    calc
      U * P ≤ (P⁻¹ * min X Y) * P :=
        mul_le_mul_of_nonneg_right hscale hP.le
      _ = min X Y := by field_simp [hP.ne']
      _ ≤ Y := min_le_right _ _
  have hPX : P / X ≤ U⁻¹ := by
    rw [div_le_iff₀ hX, ← div_eq_inv_mul, le_div_iff₀ hφ.U_pos]
    nlinarith [hUX]
  have hPY : P / Y ≤ U⁻¹ := by
    rw [div_le_iff₀ hY, ← div_eq_inv_mul, le_div_iff₀ hφ.U_pos]
    nlinarith [hUY]
  have hUinv : 0 ≤ U⁻¹ := inv_nonneg.mpr hφ.U_pos.le
  have hfactorX : 0 ≤ U⁻¹ + P / X :=
    add_nonneg hUinv (div_nonneg hP.le hX.le)
  have hfactorY : 0 ≤ U⁻¹ + P / Y :=
    add_nonneg hUinv (div_nonneg hP.le hY.le)
  have htwoX : U⁻¹ + P / X ≤ 2 * U⁻¹ := by linarith
  have htwoY : U⁻¹ + P / Y ≤ 2 * U⁻¹ := by linarith
  have htwoNonneg : 0 ≤ 2 * U⁻¹ := mul_nonneg (by norm_num) hUinv
  refine ⟨C, hC, ?_⟩
  intro h x y
  have hbase := norm_dfiMixedDeriv_localized_le hf.smooth hφ.smooth
    (zero_le_one.trans hf.one_le_P) hX hY hCf.le i j hfb hφb h x y
  have hbase' :
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        Cf * Cφ * (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j := by
    simpa [add_comm] using hbase
  constructor
  · exact hbase'.trans (by
      dsimp [C]
      have hone : (1 : ℝ) ≤ 2 ^ (i + j) := one_le_pow₀ (by norm_num)
      have hK : 0 ≤ Cf * Cφ := mul_nonneg hCf.le hCφ.le
      have hKC : Cf * Cφ ≤ Cf * Cφ * 2 ^ (i + j) :=
        le_mul_of_one_le_right hK hone
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKC (pow_nonneg hfactorX _))
        (pow_nonneg hfactorY _))
  · calc
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
          Cf * Cφ * (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j := hbase'
      _ ≤ Cf * Cφ * (2 * U⁻¹) ^ i * (2 * U⁻¹) ^ j := by
        have hK : 0 ≤ Cf * Cφ := mul_nonneg hCf.le hCφ.le
        have hpowX : (U⁻¹ + P / X) ^ i ≤ (2 * U⁻¹) ^ i :=
          pow_le_pow_left₀ hfactorX htwoX i
        have hpowY : (U⁻¹ + P / Y) ^ j ≤ (2 * U⁻¹) ^ j :=
          pow_le_pow_left₀ hfactorY htwoY j
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hpowX hK) hpowY
          (pow_nonneg hfactorY _)
          (mul_nonneg hK (pow_nonneg htwoNonneg _))
      _ = C * U⁻¹ ^ (i + j) := by
        dsimp [C]
        rw [mul_pow, mul_pow, pow_add, pow_add]
        ring

/-- Scale-uniform equation-(21) estimate with every implicit derivative
constant replaced by a finite, explicit source profile aggregate.  This is
the form needed by the published DFI error theorem: its displayed constant
does not arise from an existential chosen after `P`, `X`, `Y`, or `U`. -/
theorem dfiEquation21_of_profiles_uniform_in_shift
    {f : ℝ → ℝ → ℂ} {φ : ℝ → ℂ} {P X Y U : ℝ}
    {Cf : ℕ → ℕ → ℝ} {Cφ : ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hfC : DFIEquation2Profile f P X Y Cf)
    (hbox : DFILocalizedBox f X Y)
    (hφ : DFIRedundantCutoff φ U) (hφC : DFIRedundantCutoffProfile hφ Cφ)
    (hscale : U ≤ P⁻¹ * min X Y) (i j : ℕ) :
    ∀ (h x y : ℝ),
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        (dfiEquation2FiniteConstant Cf (max i j) *
            dfiCutoffFiniteConstant Cφ (i + j) * 2 ^ (i + j)) *
          (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j ∧
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        (dfiEquation2FiniteConstant Cf (max i j) *
            dfiCutoffFiniteConstant Cφ (i + j) * 2 ^ (i + j)) *
          U⁻¹ ^ (i + j) := by
  let A := dfiEquation2FiniteConstant Cf (max i j)
  let B := dfiCutoffFiniteConstant Cφ (i + j)
  have hA : 0 < A := hfC.finiteConstant_pos (max i j)
  have hB : 0 < B := by
    dsimp [B, dfiCutoffFiniteConstant]
    exact Finset.sum_pos (fun k _hk ↦ hφC.positive k) ⟨0, by simp⟩
  have hfb : ∀ r ∈ Finset.range (i + 1),
      ∀ s ∈ Finset.range (j + 1), ∀ x y,
        ‖dfiMixedDeriv r s f x y‖ ≤
          A * (P / X) ^ r * (P / Y) ^ s := by
    intro r hr s hs x y
    exact hfC.uniform_localized_derivative_bound hf hbox
      (Finset.mem_range_succ_iff.mp hr) (Finset.mem_range_succ_iff.mp hs) x y
  have hφb : ∀ k ≤ i + j, ∀ z,
      ‖iteratedDeriv k φ z‖ ≤ B * U⁻¹ ^ k := by
    intro k hk z
    exact (hφC.bound k z).trans
      (mul_le_mul_of_nonneg_right (hφC.le_finiteConstant hk)
        (pow_nonneg (inv_nonneg.mpr hφ.U_pos.le) _))
  have hP : 0 < P := zero_lt_one.trans_le hf.one_le_P
  have hX : 0 < X := zero_lt_one.trans_le hf.one_le_X
  have hY : 0 < Y := zero_lt_one.trans_le hf.one_le_Y
  have hUX : U * P ≤ X := by
    calc
      U * P ≤ (P⁻¹ * min X Y) * P :=
        mul_le_mul_of_nonneg_right hscale hP.le
      _ = min X Y := by field_simp [hP.ne']
      _ ≤ X := min_le_left _ _
  have hUY : U * P ≤ Y := by
    calc
      U * P ≤ (P⁻¹ * min X Y) * P :=
        mul_le_mul_of_nonneg_right hscale hP.le
      _ = min X Y := by field_simp [hP.ne']
      _ ≤ Y := min_le_right _ _
  have hPX : P / X ≤ U⁻¹ := by
    rw [div_le_iff₀ hX, ← div_eq_inv_mul, le_div_iff₀ hφ.U_pos]
    nlinarith [hUX]
  have hPY : P / Y ≤ U⁻¹ := by
    rw [div_le_iff₀ hY, ← div_eq_inv_mul, le_div_iff₀ hφ.U_pos]
    nlinarith [hUY]
  have hUinv : 0 ≤ U⁻¹ := inv_nonneg.mpr hφ.U_pos.le
  have hfactorX : 0 ≤ U⁻¹ + P / X :=
    add_nonneg hUinv (div_nonneg hP.le hX.le)
  have hfactorY : 0 ≤ U⁻¹ + P / Y :=
    add_nonneg hUinv (div_nonneg hP.le hY.le)
  have htwoX : U⁻¹ + P / X ≤ 2 * U⁻¹ := by linarith
  have htwoY : U⁻¹ + P / Y ≤ 2 * U⁻¹ := by linarith
  intro h x y
  have hbase := norm_dfiMixedDeriv_localized_le hf.smooth hφ.smooth
    (zero_le_one.trans hf.one_le_P) hX hY hA.le i j hfb hφb h x y
  have hbase' :
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
        A * B * (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j := by
    simpa [add_comm] using hbase
  constructor
  · exact hbase'.trans (by
      have hone : (1 : ℝ) ≤ 2 ^ (i + j) := one_le_pow₀ (by norm_num)
      have hAB : 0 ≤ A * B := mul_nonneg hA.le hB.le
      have hABC : A * B ≤ A * B * 2 ^ (i + j) :=
        le_mul_of_one_le_right hAB hone
      dsimp only [A, B]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hABC (pow_nonneg hfactorX _))
        (pow_nonneg hfactorY _))
  · calc
      ‖dfiMixedDeriv i j (dfiLocalizedWeight f φ h) x y‖ ≤
          A * B * (U⁻¹ + P / X) ^ i * (U⁻¹ + P / Y) ^ j := hbase'
      _ ≤ A * B * (2 * U⁻¹) ^ i * (2 * U⁻¹) ^ j := by gcongr
      _ = (dfiEquation2FiniteConstant Cf (max i j) *
            dfiCutoffFiniteConstant Cφ (i + j) * 2 ^ (i + j)) *
          U⁻¹ ^ (i + j) := by
        dsimp [A, B]
        rw [mul_pow, mul_pow, pow_add, pow_add]
        ring

end RiemannZeta.GuthMaynard
