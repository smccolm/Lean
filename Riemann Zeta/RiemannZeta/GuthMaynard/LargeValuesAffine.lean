import RiemannZeta.GuthMaynard.LargeValuesS3
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.PoissonSummation

open Complex Finset Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff FourierTransform Topology

namespace RiemannZeta.GuthMaynard

/-!
# Guth--Maynard Section 9: affine transformations

This module formalizes the exact finite affine family underlying `J(f)` in
Section 9 of Guth--Maynard.  The paper writes dyadic conditions using
`\sim` and `\ll`; here those ranges are the closed integer shells below.
The theorem layer is stated uniformly for every admissible triple of
subscales, which is equivalent to bounding the finite supremum `J(f)`.
-/

/-- The signed dyadic shell `M ≤ |m| ≤ 2M`. -/
noncomputable def gmAffineSignedShell (M : ℕ) : Finset ℤ :=
  (Finset.Icc (-(2 * M : ℕ) : ℤ) (-(M : ℕ) : ℤ)) ∪
    Finset.Icc (M : ℤ) (2 * M : ℤ)

/-- The positive dyadic shell `M ≤ m ≤ 2M`. -/
noncomputable def gmAffinePositiveShell (M : ℕ) : Finset ℤ :=
  Finset.Icc (M : ℤ) (2 * M : ℤ)

/-- A source-faithful finite realization of `|m₃| ≪ M₃`.  The factor eight
dominates every support constant used by the Section 8 smoother. -/
noncomputable def gmAffineCentralShell (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(8 * M : ℕ) : ℤ) (8 * M : ℤ)

/-- The doubled central shell supporting the smooth Poisson majorant from
Guth--Maynard equation (9.2). -/
noncomputable def gmAffineSmoothCentralShell (M : ℕ) : Finset ℤ :=
  Finset.Icc (-(16 * M : ℕ) : ℤ) (16 * M : ℤ)

/-- The smooth central-frequency weight used before Poisson summation.  It is
one on `|m₃| ≤ 8M` and vanishes for `|m₃| ≥ 16M`. -/
noncomputable def gmAffineCentralWeight (M : ℕ) (m : ℤ) : ℝ :=
  gmCubicLocalBump ((m : ℝ) / (8 * M : ℝ))

theorem mem_gmAffineSignedShell {M : ℕ} {m : ℤ} :
    m ∈ gmAffineSignedShell M ↔
      (-(2 * M : ℕ) : ℤ) ≤ m ∧ m ≤ -(M : ℕ) ∨
      (M : ℤ) ≤ m ∧ m ≤ 2 * M := by
  simp [gmAffineSignedShell]

theorem mem_gmAffinePositiveShell {M : ℕ} {m : ℤ} :
    m ∈ gmAffinePositiveShell M ↔ (M : ℤ) ≤ m ∧ m ≤ 2 * M := by
  simp [gmAffinePositiveShell]

theorem mem_gmAffineCentralShell {M : ℕ} {m : ℤ} :
    m ∈ gmAffineCentralShell M ↔
      (-(8 * M : ℕ) : ℤ) ≤ m ∧ m ≤ 8 * M := by
  simp [gmAffineCentralShell]

theorem mem_gmAffineSmoothCentralShell {M : ℕ} {m : ℤ} :
    m ∈ gmAffineSmoothCentralShell M ↔
      (-(16 * M : ℕ) : ℤ) ≤ m ∧ m ≤ 16 * M := by
  simp [gmAffineSmoothCentralShell]

theorem gmAffineCentralWeight_nonneg (M : ℕ) (m : ℤ) :
    0 ≤ gmAffineCentralWeight M m :=
  gmCubicLocalBump_nonneg _

theorem gmAffineCentralWeight_le_one (M : ℕ) (m : ℤ) :
    gmAffineCentralWeight M m ≤ 1 :=
  gmCubicLocalBump_le_one _

theorem gmAffineCentralWeight_eq_one
    {M : ℕ} (hM : 0 < M) {m : ℤ} (hm : m ∈ gmAffineCentralShell M) :
    gmAffineCentralWeight M m = 1 := by
  apply gmCubicLocalBump_one
  rw [abs_div]
  have hMpos : (0 : ℝ) < 8 * M := by positivity
  rw [abs_of_pos hMpos]
  rw [div_le_one hMpos]
  rcases mem_gmAffineCentralShell.mp hm with ⟨hmLower, hmUpper⟩
  rw [abs_le]
  constructor
  · exact_mod_cast hmLower
  · exact_mod_cast hmUpper

theorem gmAffineCentralWeight_eq_zero_of_not_mem
    {M : ℕ} (hM : 0 < M) {m : ℤ} (hm : m ∉ gmAffineSmoothCentralShell M) :
    gmAffineCentralWeight M m = 0 := by
  apply gmCubicLocalBump_eq_zero_of_two_le_abs
  rw [abs_div]
  have hMpos : (0 : ℝ) < 8 * M := by positivity
  rw [abs_of_pos hMpos]
  rw [le_div_iff₀ hMpos]
  have hmOutside : m < (-(16 * M : ℕ) : ℤ) ∨ (16 * M : ℤ) < m := by
    rw [mem_gmAffineSmoothCentralShell, not_and_or] at hm
    exact Or.imp lt_of_not_ge lt_of_not_ge hm
  rcases hmOutside with hmLower | hmUpper
  · rw [abs_of_nonpos]
    · have hbound : (16 * M : ℤ) ≤ -m := by omega
      have hboundReal : (16 * M : ℝ) ≤ -(m : ℝ) := by exact_mod_cast hbound
      nlinarith only [hboundReal]
    · exact_mod_cast (show m ≤ 0 by omega)
  · rw [abs_of_nonneg]
    · have hboundReal : (16 * M : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hmUpper.le
      nlinarith only [hboundReal]
    · exact_mod_cast (show (0 : ℤ) ≤ m by omega)

/-! ### A Schwartz central weight and exact Poisson summation -/

/-- The fixed local bump, complexified as a Schwartz function. -/
noncomputable def gmAffineLocalBumpFunction (x : ℝ) : ℂ :=
  (gmCubicLocalBump x : ℂ)

theorem contDiff_gmAffineLocalBumpFunction :
    ContDiff ℝ ∞ gmAffineLocalBumpFunction := by
  unfold gmAffineLocalBumpFunction gmCubicLocalBump
  exact Complex.ofRealCLM.contDiff.comp
    (dfiUnitRedundantBump.contDiff.comp (by fun_prop))

theorem hasCompactSupport_gmAffineLocalBumpFunction :
    HasCompactSupport gmAffineLocalBumpFunction := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-2 : ℝ) 2))
  intro x hx
  have hxOutside : x < -2 ∨ 2 < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  have habs : 2 ≤ |x| := by
    rcases hxOutside with hleft | hright
    · rw [abs_of_neg (hleft.trans (by norm_num))]
      linarith
    · rw [abs_of_pos ((by norm_num : (0 : ℝ) < 2).trans hright)]
      linarith
  simp only [gmAffineLocalBumpFunction,
    gmCubicLocalBump_eq_zero_of_two_le_abs habs, Complex.ofReal_zero]

noncomputable def gmAffineLocalBumpSchwartz : SchwartzMap ℝ ℂ :=
  hasCompactSupport_gmAffineLocalBumpFunction.toSchwartzMap
    contDiff_gmAffineLocalBumpFunction

@[simp]
theorem gmAffineLocalBumpSchwartz_apply (x : ℝ) :
    gmAffineLocalBumpSchwartz x = (gmCubicLocalBump x : ℂ) := rfl

/-- The central bump as a complex-valued real-variable function. -/
noncomputable def gmAffineCentralWeightFunction (M : ℕ) (x : ℝ) : ℂ :=
  (gmCubicLocalBump (x / (8 * M : ℝ)) : ℂ)

theorem contDiff_gmAffineCentralWeightFunction (M : ℕ) :
    ContDiff ℝ ∞ (gmAffineCentralWeightFunction M) := by
  unfold gmAffineCentralWeightFunction gmCubicLocalBump
  apply Complex.ofRealCLM.contDiff.comp
  apply dfiUnitRedundantBump.contDiff.comp
  fun_prop

theorem hasCompactSupport_gmAffineCentralWeightFunction
    {M : ℕ} (hM : 0 < M) :
    HasCompactSupport (gmAffineCentralWeightFunction M) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (-(16 * M : ℝ)) (16 * M : ℝ)))
  intro x hx
  have hxOutside : x < -(16 * M : ℝ) ∨ (16 * M : ℝ) < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  have hMpos : (0 : ℝ) < 8 * M := by positivity
  have habs : 2 ≤ |x / (8 * M : ℝ)| := by
    rw [abs_div, abs_of_pos hMpos, le_div_iff₀ hMpos]
    rcases hxOutside with hleft | hright
    · have hxneg : x < 0 := hleft.trans_le (neg_nonpos.mpr (by positivity))
      rw [abs_of_neg hxneg]
      nlinarith
    · have hxpos : 0 < x := (by positivity : (0 : ℝ) ≤ 16 * M).trans_lt hright
      rw [abs_of_pos hxpos]
      nlinarith
  simp only [gmAffineCentralWeightFunction,
    gmCubicLocalBump_eq_zero_of_two_le_abs habs, Complex.ofReal_zero]

/-- The exact central bump as an element of Schwartz space. -/
noncomputable def gmAffineCentralWeightSchwartz
    (M : ℕ) (hM : 0 < M) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_gmAffineCentralWeightFunction hM).toSchwartzMap
    (contDiff_gmAffineCentralWeightFunction M)

@[simp]
theorem gmAffineCentralWeightSchwartz_apply
    (M : ℕ) (hM : 0 < M) (x : ℝ) :
    gmAffineCentralWeightSchwartz M hM x =
      (gmCubicLocalBump (x / (8 * M : ℝ)) : ℂ) := rfl

theorem gmAffineCentralWeightSchwartz_int_apply
    (M : ℕ) (hM : 0 < M) (m : ℤ) :
    gmAffineCentralWeightSchwartz M hM (m : ℝ) =
      (gmAffineCentralWeight M m : ℂ) := rfl

/-- The dual Schwartz kernel occurring after Poisson summation of the
translation variable. -/
noncomputable def gmAffineCentralPoissonKernel
    (M : ℕ) (hM : 0 < M) : SchwartzMap ℝ ℂ :=
  𝓕⁻ (gmAffineCentralWeightSchwartz M hM)

/-- Exact dilation formula for the inverse Fourier kernel.  This exposes
the `M₃ * Fourier(bump)(M₃·)` shape used throughout (9.3)--(9.8). -/
theorem gmAffineCentralPoissonKernel_eq_scaled
    (M : ℕ) (hM : 0 < M) (y : ℝ) :
    gmAffineCentralPoissonKernel M hM y =
      ((8 * M : ℝ) : ℂ) *
        𝓕⁻ gmAffineLocalBumpSchwartz ((8 * M : ℝ) * y) := by
  have hs : (0 : ℝ) < 8 * M := by positivity
  rw [gmAffineCentralPoissonKernel, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  simp only [Real.inner_apply, smul_eq_mul, gmAffineCentralWeightSchwartz_apply,
    gmAffineLocalBumpSchwartz_apply]
  let q : ℝ → ℂ := fun z =>
    Complex.exp ((((2 * Real.pi * (z * ((8 * M : ℝ) * y)) : ℝ) : ℂ) * I)) *
      (gmCubicLocalBump z : ℂ)
  calc
    (∫ x : ℝ, Complex.exp ((((2 * Real.pi * (x * y) : ℝ) : ℂ) * I)) *
        (gmCubicLocalBump (x / (8 * M : ℝ)) : ℂ)) =
        ∫ x : ℝ, q (x / (8 * M : ℝ)) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [q]
      rw [show (x / (8 * M : ℝ)) * ((8 * M : ℝ) * y) = x * y by
        field_simp [hs.ne']]
    _ = |(8 * M : ℝ)| * ∫ z : ℝ, q z :=
      MeasureTheory.Measure.integral_comp_div q (8 * M : ℝ)
    _ = ((8 * M : ℝ) : ℂ) *
          ∫ z : ℝ,
            Complex.exp ((((2 * Real.pi *
              (z * ((8 * M : ℝ) * y)) : ℝ) : ℂ) * I)) *
              (gmCubicLocalBump z : ℂ) := by
      rw [abs_of_pos hs]

/-- The fixed inverse-Fourier transform of the local bump.  Separating this
Schwartz function from the scale parameter makes the uniformity in (9.3)
explicit. -/
noncomputable def gmAffineLocalBumpDual : SchwartzMap ℝ ℂ :=
  𝓕⁻ gmAffineLocalBumpSchwartz

@[simp]
theorem gmAffineLocalBumpDual_apply (x : ℝ) :
    gmAffineLocalBumpDual x = 𝓕⁻ gmAffineLocalBumpSchwartz x := rfl

/-- Arbitrary polynomial decay of the fixed kernel used in the affine
Poisson expansion. -/
theorem gmAffineLocalBumpDual_polynomial_decay (n : ℕ) (x : ℝ) :
    |x| ^ n * ‖gmAffineLocalBumpDual x‖ ≤
      SchwartzMap.seminorm ℝ n 0 gmAffineLocalBumpDual := by
  have h := SchwartzMap.le_seminorm' (𝕜 := ℝ) n 0 gmAffineLocalBumpDual x
  rw [iteratedDeriv_zero] at h
  exact h

/-- Scaled arbitrary-order decay for the actual Poisson kernel.  The sole
scale loss is the expected dilation factor `8M`. -/
theorem gmAffineCentralPoissonKernel_polynomial_decay
    (n : ℕ) (M : ℕ) (hM : 0 < M) (y : ℝ) :
    |(8 * M : ℝ) * y| ^ n * ‖gmAffineCentralPoissonKernel M hM y‖ ≤
      (8 * M : ℝ) * SchwartzMap.seminorm ℝ n 0 gmAffineLocalBumpDual := by
  rw [gmAffineCentralPoissonKernel_eq_scaled]
  change |(8 * M : ℝ) * y| ^ n *
      ‖(((8 * M : ℝ) : ℂ) * gmAffineLocalBumpDual ((8 * M : ℝ) * y))‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hs : 0 ≤ (8 * M : ℝ) := by positivity
  rw [abs_of_nonneg hs]
  calc
    |(8 * M : ℝ) * y| ^ n *
          ((8 * M : ℝ) * ‖gmAffineLocalBumpDual ((8 * M : ℝ) * y)‖) =
        (8 * M : ℝ) * (|(8 * M : ℝ) * y| ^ n *
          ‖gmAffineLocalBumpDual ((8 * M : ℝ) * y)‖) := by ring
    _ ≤ (8 * M : ℝ) * SchwartzMap.seminorm ℝ n 0 gmAffineLocalBumpDual :=
      mul_le_mul_of_nonneg_left
        (gmAffineLocalBumpDual_polynomial_decay n ((8 * M : ℝ) * y)) hs

/-- After translating by the floor of a real number, every lattice point
except the two adjacent to the origin is at least half its integer index
away.  These are precisely the two exceptional terms in the uniform
shifted-lattice tail estimate. -/
theorem half_abs_intCast_le_abs_fract_add
    (alpha : ℝ) (j : ℤ) (hj0 : j ≠ 0) (hjneg : j ≠ -1) :
    |(j : ℝ)| / 2 ≤ |Int.fract alpha + (j : ℝ)| := by
  have hr0 : 0 ≤ Int.fract alpha := Int.fract_nonneg alpha
  have hr1 : Int.fract alpha < 1 := Int.fract_lt_one alpha
  by_cases hj : 0 ≤ j
  · have hj1 : 1 ≤ j := by omega
    have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
    rw [abs_of_nonneg (by exact_mod_cast hj)]
    rw [abs_of_nonneg (add_nonneg hr0 (by exact_mod_cast hj))]
    linarith
  · have hj2 : j ≤ -2 := by omega
    have hjr : (j : ℝ) ≤ -2 := by exact_mod_cast hj2
    have hsum : Int.fract alpha + (j : ℝ) ≤ 0 := by linarith
    have hjr0 : (j : ℝ) ≤ 0 := by linarith
    rw [abs_of_nonpos hjr0, abs_of_nonpos hsum]
    linarith

/-- Re-centering an arbitrary real translate of the integer lattice at its
floor. -/
theorem add_int_eq_fract_add_translated
    (alpha : ℝ) (ell : ℤ) :
    alpha + (ell : ℝ) =
      Int.fract alpha + ((ell + ⌊alpha⌋) : ℤ) := by
  calc
    alpha + (ell : ℝ) =
        (Int.fract alpha + (⌊alpha⌋ : ℝ)) + (ell : ℝ) := by
      rw [Int.fract_add_floor]
    _ = Int.fract alpha + ((ell + ⌊alpha⌋) : ℤ) := by
      push_cast
      ring

/-- The nonnegative norm of an omitted Poisson mode.  The cutoff is in the
scaled frequency variable, exactly as in equation (9.3). -/
noncomputable def gmAffinePoissonFarMode
    (M : ℕ) (hM : 0 < M) (alpha Q : ℝ) (ell : ℤ) : ℝ :=
  if Q ≤ |(8 * M : ℝ) * (alpha + ell)| then
    ‖gmAffineCentralPoissonKernel M hM (alpha + ell)‖
  else 0

theorem gmAffinePoissonFarMode_nonneg
    (M : ℕ) (hM : 0 < M) (alpha Q : ℝ) (ell : ℤ) :
    0 ≤ gmAffinePoissonFarMode M hM alpha Q ell := by
  unfold gmAffinePoissonFarMode
  split_ifs <;> positivity

/-- A far mode which is not one of the two floor-adjacent lattice points
is controlled by the fixed quadratic integer profile, with an arbitrary
additional power of the scaled cutoff. -/
theorem gmAffinePoissonFarMode_le_decayProfile
    (n : ℕ) {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q)
    (ell : ℤ) (hj0 : ell + ⌊alpha⌋ ≠ 0)
    (hjneg : ell + ⌊alpha⌋ ≠ -1) :
    gmAffinePoissonFarMode M hM alpha Q ell ≤
      (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ n) *
        gmIntDecayProfile 2 (ell + ⌊alpha⌋) := by
  unfold gmAffinePoissonFarMode
  split_ifs with hfar
  · let j : ℤ := ell + ⌊alpha⌋
    let s : ℝ := 8 * M
    let C : ℝ := SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual
    have hs : 0 < s := by dsimp only [s]; positivity
    have hy : alpha + (ell : ℝ) = Int.fract alpha + (j : ℝ) := by
      simpa only [j] using add_int_eq_fract_add_translated alpha ell
    have hjhalf : |(j : ℝ)| / 2 ≤ |alpha + (ell : ℝ)| := by
      rw [hy]
      exact half_abs_intCast_le_abs_fract_add alpha j hj0 hjneg
    have hjabs : 0 < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj0)
    have hsy : 0 < |s * (alpha + (ell : ℝ))| := by
      have : 0 < |alpha + (ell : ℝ)| := lt_of_lt_of_le (by positivity) hjhalf
      rw [abs_mul, abs_of_pos hs]
      positivity
    have hQpow : Q ^ n ≤ |s * (alpha + (ell : ℝ))| ^ n := by
      exact pow_le_pow_left₀ hQ.le hfar n
    have hjpow : (s ^ 2 * (|(j : ℝ)| / 2) ^ 2) ≤
        |s * (alpha + (ell : ℝ))| ^ 2 := by
      calc
        s ^ 2 * (|(j : ℝ)| / 2) ^ 2 =
            (s * (|(j : ℝ)| / 2)) ^ 2 := by ring
        _ ≤ (s * |alpha + (ell : ℝ)|) ^ 2 := by
          exact pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left hjhalf hs.le) 2
        _ = |s * (alpha + (ell : ℝ))| ^ 2 := by
          rw [abs_mul, abs_of_pos hs]
    have hdecay := gmAffineCentralPoissonKernel_polynomial_decay
      (n + 2) M hM (alpha + (ell : ℝ))
    have hfactor :
        Q ^ n * (s ^ 2 * (|(j : ℝ)| / 2) ^ 2) ≤
          |s * (alpha + (ell : ℝ))| ^ (n + 2) := by
      rw [pow_add]
      exact mul_le_mul hQpow hjpow (by positivity) (by positivity)
    have hbound :
        ‖gmAffineCentralPoissonKernel M hM (alpha + (ell : ℝ))‖ ≤
          (s * C) /
            (Q ^ n * (s ^ 2 * (|(j : ℝ)| / 2) ^ 2)) := by
      rw [le_div_iff₀ (mul_pos (pow_pos hQ n)
        (mul_pos (pow_pos hs 2) (pow_pos (by positivity : 0 < |(j : ℝ)| / 2) 2)))]
      calc
        ‖gmAffineCentralPoissonKernel M hM (alpha + (ell : ℝ))‖ *
              (Q ^ n * (s ^ 2 * (|(j : ℝ)| / 2) ^ 2)) ≤
            ‖gmAffineCentralPoissonKernel M hM (alpha + (ell : ℝ))‖ *
              |s * (alpha + (ell : ℝ))| ^ (n + 2) := by gcongr
        _ = |s * (alpha + (ell : ℝ))| ^ (n + 2) *
              ‖gmAffineCentralPoissonKernel M hM (alpha + (ell : ℝ))‖ := by ring
        _ ≤ s * C := by simpa only [s, C] using hdecay
    have hj0' : j ≠ 0 := by exact hj0
    have hprofile : gmIntDecayProfile 2 j = 1 / |(j : ℝ)| ^ 2 := by
      simp [gmIntDecayProfile, hj0']
    have hC : 0 ≤ C := by dsimp only [C]; positivity
    have hsone : 1 ≤ s := by
      dsimp only [s]
      have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith
    rw [hprofile]
    calc
      ‖gmAffineCentralPoissonKernel M hM (alpha + (ell : ℝ))‖ ≤
          (s * C) / (Q ^ n * (s ^ 2 * (|(j : ℝ)| / 2) ^ 2)) := hbound
      _ = (4 * C / (s * Q ^ n)) * (1 / |(j : ℝ)| ^ 2) := by
        field_simp [hs.ne', hjabs.ne', hQ.ne']
        ring
      _ ≤ (4 * C / Q ^ n) * (1 / |(j : ℝ)| ^ 2) := by
        have hden : 0 < Q ^ n := pow_pos hQ n
        have hleft : 4 * C / (s * Q ^ n) ≤ 4 * C / Q ^ n := by
          exact div_le_div_of_nonneg_left (by positivity) hden
            (by
              simpa only [one_mul] using
                (mul_le_mul_of_nonneg_right hsone hden.le))
        gcongr
  · have hprofile0 : 0 ≤ gmIntDecayProfile 2 (ell + ⌊alpha⌋) := by
      unfold gmIntDecayProfile
      split_ifs <;> positivity
    exact mul_nonneg (by positivity) hprofile0

/-- Direct bound for either floor-adjacent exceptional mode.  Its scale
factor is retained; Section 9 later uses `M ≤ T⁴` and chooses the decay
order after the epsilon budget. -/
theorem gmAffinePoissonFarMode_le_exception
    (n : ℕ) {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q)
    (ell : ℤ) :
    gmAffinePoissonFarMode M hM alpha Q ell ≤
      (8 * M : ℝ) *
        SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ (n + 2) := by
  unfold gmAffinePoissonFarMode
  split_ifs with hfar
  · let s : ℝ := 8 * M
    let C : ℝ := SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual
    have hs : 0 < s := by dsimp only [s]; positivity
    have hfreq : 0 < |s * (alpha + (ell : ℝ))| :=
      lt_of_lt_of_le hQ hfar
    have hpow : Q ^ (n + 2) ≤
        |s * (alpha + (ell : ℝ))| ^ (n + 2) :=
      pow_le_pow_left₀ hQ.le hfar (n + 2)
    have hdecay := gmAffineCentralPoissonKernel_polynomial_decay
      (n + 2) M hM (alpha + (ell : ℝ))
    rw [le_div_iff₀ (pow_pos hQ (n + 2))]
    calc
      ‖gmAffineCentralPoissonKernel M hM (alpha + (ell : ℝ))‖ *
            Q ^ (n + 2) ≤
          ‖gmAffineCentralPoissonKernel M hM (alpha + (ell : ℝ))‖ *
            |s * (alpha + (ell : ℝ))| ^ (n + 2) := by gcongr
      _ = |s * (alpha + (ell : ℝ))| ^ (n + 2) *
            ‖gmAffineCentralPoissonKernel M hM (alpha + (ell : ℝ))‖ := by ring
      _ ≤ s * C := by simpa only [s, C] using hdecay
  · positivity

theorem summable_gmIntDecayProfile_floorTranslate (alpha : ℝ) :
    Summable (fun ell : ℤ => gmIntDecayProfile 2 (ell + ⌊alpha⌋)) := by
  simpa only [Function.comp_def, add_comm] using
    (summable_gmIntDecayProfile (q := 2) (by norm_num)).comp_injective
      (add_right_injective (⌊alpha⌋ : ℤ))

/-- A summable pointwise majorant for every omitted translated mode. -/
noncomputable def gmAffinePoissonFarMajorant
    (n : ℕ) (M : ℕ) (alpha Q : ℝ) (ell : ℤ) : ℝ :=
  (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ n) *
      gmIntDecayProfile 2 (ell + ⌊alpha⌋) +
    (if ell + ⌊alpha⌋ = 0 then
      (8 * M : ℝ) * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        Q ^ (n + 2)
    else 0) +
    (if ell + ⌊alpha⌋ = -1 then
      (8 * M : ℝ) * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        Q ^ (n + 2)
    else 0)

theorem gmAffinePoissonFarMode_le_majorant
    (n : ℕ) {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q)
    (ell : ℤ) :
    gmAffinePoissonFarMode M hM alpha Q ell ≤
      gmAffinePoissonFarMajorant n M alpha Q ell := by
  let j : ℤ := ell + ⌊alpha⌋
  let D : ℝ := (8 * M : ℝ) *
    SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ (n + 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  by_cases hj0 : j = 0
  · have hex := gmAffinePoissonFarMode_le_exception n hM
      (alpha := alpha) hQ ell
    unfold gmAffinePoissonFarMajorant
    rw [show ell + ⌊alpha⌋ = 0 from hj0]
    simpa [gmIntDecayProfile] using hex
  · by_cases hjneg : j = -1
    · have hex := gmAffinePoissonFarMode_le_exception n hM
        (alpha := alpha) hQ ell
      unfold gmAffinePoissonFarMajorant
      rw [show ell + ⌊alpha⌋ = -1 from hjneg]
      have hmain0 : 0 ≤
          4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
            Q ^ n := by
        positivity
      simpa [gmIntDecayProfile] using
        hex.trans (le_add_of_nonneg_left hmain0)
    · have hmain := gmAffinePoissonFarMode_le_decayProfile n hM hQ ell hj0 hjneg
      unfold gmAffinePoissonFarMajorant
      rw [if_neg hj0, if_neg hjneg, add_zero, add_zero]
      exact hmain

theorem summable_gmAffinePoissonFarMajorant
    (n M : ℕ) (alpha Q : ℝ) :
    Summable (gmAffinePoissonFarMajorant n M alpha Q) := by
  unfold gmAffinePoissonFarMajorant
  have hmain := (summable_gmIntDecayProfile_floorTranslate alpha).mul_left
    (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ n)
  have hzero : Summable (fun ell : ℤ =>
      if ell + ⌊alpha⌋ = 0 then
        (8 * M : ℝ) * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ (n + 2)
      else 0) := by
    apply (hasSum_single (-⌊alpha⌋) (fun ell hell => ?_)).summable
    rw [if_neg]
    intro heq
    apply hell
    omega
  have hneg : Summable (fun ell : ℤ =>
      if ell + ⌊alpha⌋ = -1 then
        (8 * M : ℝ) * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ (n + 2)
      else 0) := by
    apply (hasSum_single (-1 - ⌊alpha⌋) (fun ell hell => ?_)).summable
    rw [if_neg]
    intro heq
    apply hell
    omega
  exact (hmain.add hzero).add hneg

theorem tsum_gmIntDecayProfile_floorTranslate (alpha : ℝ) :
    (∑' ell : ℤ, gmIntDecayProfile 2 (ell + ⌊alpha⌋)) =
      ∑' j : ℤ, gmIntDecayProfile 2 j := by
  simpa only [Equiv.coe_addRight, add_comm] using
    (Equiv.addRight (⌊alpha⌋ : ℤ)).tsum_eq (gmIntDecayProfile 2)

theorem tsum_gmAffinePoissonFarMajorant
    (n M : ℕ) (alpha Q : ℝ) :
    (∑' ell : ℤ, gmAffinePoissonFarMajorant n M alpha Q ell) =
      (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ n) *
          (∑' j : ℤ, gmIntDecayProfile 2 j) +
        2 * ((8 * M : ℝ) *
          SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
            Q ^ (n + 2)) := by
  let A : ℝ :=
    4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ n
  let D : ℝ := (8 * M : ℝ) *
    SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ (n + 2)
  let F : ℤ → ℝ := fun ell => A * gmIntDecayProfile 2 (ell + ⌊alpha⌋)
  let Z : ℤ → ℝ := fun ell => if ell + ⌊alpha⌋ = 0 then D else 0
  let L : ℤ → ℝ := fun ell => if ell + ⌊alpha⌋ = -1 then D else 0
  have hF : Summable F := by
    exact (summable_gmIntDecayProfile_floorTranslate alpha).mul_left A
  have hZ : Summable Z := by
    apply (hasSum_single (-⌊alpha⌋) (fun ell hell => ?_)).summable
    dsimp only [Z]
    rw [if_neg]
    intro heq
    apply hell
    omega
  have hL : Summable L := by
    apply (hasSum_single (-1 - ⌊alpha⌋) (fun ell hell => ?_)).summable
    dsimp only [L]
    rw [if_neg]
    intro heq
    apply hell
    omega
  have hZsum : (∑' ell : ℤ, Z ell) = D := by
    calc
      (∑' ell : ℤ, Z ell) =
          ∑' ell : ℤ, if ell = -⌊alpha⌋ then D else 0 := by
        apply tsum_congr
        intro ell
        dsimp only [Z]
        by_cases h : ell + ⌊alpha⌋ = 0
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      _ = D := tsum_ite_eq (-⌊alpha⌋) (fun _ : ℤ => D)
  have hLsum : (∑' ell : ℤ, L ell) = D := by
    calc
      (∑' ell : ℤ, L ell) =
          ∑' ell : ℤ, if ell = -1 - ⌊alpha⌋ then D else 0 := by
        apply tsum_congr
        intro ell
        dsimp only [L]
        by_cases h : ell + ⌊alpha⌋ = -1
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      _ = D := tsum_ite_eq (-1 - ⌊alpha⌋) (fun _ : ℤ => D)
  change tsum (fun x : ℤ => (F x + Z x) + L x) = _
  rw [(hF.add hZ).tsum_add hL, hF.tsum_add hZ, hZsum, hLsum]
  rw [show (∑' ell : ℤ, F ell) =
      A * (∑' j : ℤ, gmIntDecayProfile 2 j) by
    dsimp only [F]
    rw [tsum_mul_left, tsum_gmIntDecayProfile_floorTranslate]]
  dsimp only [A, D]
  ring

theorem summable_gmAffinePoissonFarMode
    (n : ℕ) {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q) :
    Summable (gmAffinePoissonFarMode M hM alpha Q) := by
  apply Summable.of_nonneg_of_le
    (gmAffinePoissonFarMode_nonneg M hM alpha Q)
    (fun ell => gmAffinePoissonFarMode_le_majorant n hM hQ ell)
  exact summable_gmAffinePoissonFarMajorant n M alpha Q

/-- Uniform complete-tail estimate behind the `O(T⁻¹⁰⁰)` in (9.3).
The translated quadratic profile contributes an absolute fixed constant;
the only exceptional loss is the explicitly displayed dilation factor. -/
theorem tsum_gmAffinePoissonFarMode_le
    (n : ℕ) {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q) :
    (∑' ell : ℤ, gmAffinePoissonFarMode M hM alpha Q ell) ≤
      (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ n) *
          (∑' j : ℤ, gmIntDecayProfile 2 j) +
        2 * ((8 * M : ℝ) *
          SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
            Q ^ (n + 2)) := by
  have hfar := summable_gmAffinePoissonFarMode n hM
    (alpha := alpha) hQ
  have hmajor := summable_gmAffinePoissonFarMajorant n M alpha Q
  exact (hfar.tsum_le_tsum
    (fun ell => gmAffinePoissonFarMode_le_majorant n hM
      (alpha := alpha) hQ ell)
    hmajor).trans_eq (tsum_gmAffinePoissonFarMajorant n M alpha Q)

/-- The actual omitted complex Poisson mode.  Its norm is exactly the
nonnegative quantity estimated above; keeping the complex term separate
prevents the Section 9 truncation from losing phase information. -/
noncomputable def gmAffinePoissonFarTerm
    (M : ℕ) (hM : 0 < M) (alpha Q : ℝ) (ell : ℤ) : ℂ :=
  if Q ≤ |(8 * M : ℝ) * (alpha + ell)| then
    gmAffineCentralPoissonKernel M hM (alpha + ell)
  else 0

@[simp]
theorem norm_gmAffinePoissonFarTerm
    (M : ℕ) (hM : 0 < M) (alpha Q : ℝ) (ell : ℤ) :
    ‖gmAffinePoissonFarTerm M hM alpha Q ell‖ =
      gmAffinePoissonFarMode M hM alpha Q ell := by
  unfold gmAffinePoissonFarTerm gmAffinePoissonFarMode
  split_ifs <;> simp

/-- Absolute summability of the complete omitted complex-frequency
series. -/
theorem summable_gmAffinePoissonFarTerm
    (n : ℕ) {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q) :
    Summable (gmAffinePoissonFarTerm M hM alpha Q) := by
  apply summable_norm_iff.mp
  simpa only [norm_gmAffinePoissonFarTerm] using
    (summable_gmAffinePoissonFarMode n hM (alpha := alpha) hQ)

/-- The complete omitted part of the translated Poisson series. -/
noncomputable def gmAffinePoissonFarSeries
    (M : ℕ) (hM : 0 < M) (alpha Q : ℝ) : ℂ :=
  ∑' ell : ℤ, gmAffinePoissonFarTerm M hM alpha Q ell

/-- Quantitative norm estimate for the complete omitted complex series.
This is the phase-preserving version of the preceding scalar tail bound. -/
theorem norm_gmAffinePoissonFarSeries_le
    (n : ℕ) {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q) :
    ‖gmAffinePoissonFarSeries M hM alpha Q‖ ≤
      (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual / Q ^ n) *
          (∑' j : ℤ, gmIntDecayProfile 2 j) +
        2 * ((8 * M : ℝ) *
          SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
            Q ^ (n + 2)) := by
  unfold gmAffinePoissonFarSeries
  have hnorm : Summable (fun ell : ℤ =>
      ‖gmAffinePoissonFarTerm M hM alpha Q ell‖) := by
    simpa only [norm_gmAffinePoissonFarTerm] using
      (summable_gmAffinePoissonFarMode n hM (alpha := alpha) hQ)
  exact (norm_tsum_le_tsum_norm hnorm).trans
    (by simpa only [norm_gmAffinePoissonFarTerm] using
      (tsum_gmAffinePoissonFarMode_le n hM (alpha := alpha) hQ))

/-- The finite set of frequencies retained in equation (9.3).  The raw
integer interval is centered at `-floor alpha`; filtering it by the exact
scaled cutoff makes later identities literal rather than asymptotic. -/
noncomputable def gmAffinePoissonNearSet
    (M : ℕ) (alpha Q : ℝ) : Finset ℤ :=
  let R : ℤ := ⌈Q / (8 * M : ℝ) + 1⌉
  (Finset.Icc (-R - ⌊alpha⌋) (R - ⌊alpha⌋)).filter
    (fun ell : ℤ => |(8 * M : ℝ) * (alpha + ell)| < Q)

/-- Every mode satisfying the exact near-frequency inequality belongs to
the displayed finite interval. -/
theorem mem_gmAffinePoissonNearSet_of_lt
    {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} {ell : ℤ}
    (hnear : |(8 * M : ℝ) * (alpha + ell)| < Q) :
    ell ∈ gmAffinePoissonNearSet M alpha Q := by
  let s : ℝ := 8 * M
  let j : ℤ := ell + ⌊alpha⌋
  let R : ℤ := ⌈Q / s + 1⌉
  have hs : 0 < s := by dsimp only [s]; positivity
  have hy : alpha + (ell : ℝ) = Int.fract alpha + (j : ℝ) := by
    simpa only [j] using add_int_eq_fract_add_translated alpha ell
  have hyabs : |alpha + (ell : ℝ)| < Q / s := by
    rw [abs_mul, abs_of_pos hs] at hnear
    exact (lt_div_iff₀ hs).mpr (by simpa only [mul_comm] using hnear)
  have hfractAbs : |Int.fract alpha| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg alpha)]
    exact Int.fract_lt_one alpha
  have hjReal : |(j : ℝ)| < Q / s + 1 := by
    have hjEq : (j : ℝ) = (alpha + (ell : ℝ)) - Int.fract alpha := by
      rw [hy]
      ring
    rw [hjEq]
    exact (abs_sub _ _).trans_lt (add_lt_add hyabs hfractAbs)
  have hjUpperReal : (j : ℝ) ≤ (R : ℝ) := by
    exact (le_abs_self (j : ℝ)).trans
      ((le_of_lt hjReal).trans (Int.le_ceil (Q / s + 1)))
  have hjLowerReal : -(R : ℝ) ≤ (j : ℝ) := by
    have hneg : -(R : ℝ) ≤ -|(j : ℝ)| := by
      exact neg_le_neg ((le_of_lt hjReal).trans (Int.le_ceil (Q / s + 1)))
    exact hneg.trans (neg_abs_le (j : ℝ))
  have hjUpper : j ≤ R := by exact_mod_cast hjUpperReal
  have hjLower : -R ≤ j := by exact_mod_cast hjLowerReal
  unfold gmAffinePoissonNearSet
  dsimp only
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · dsimp only [R, j, s] at hjUpper hjLower ⊢
    constructor <;> omega
  · exact hnear

/-- The retained frequency set has the expected finite interval
cardinality.  This is the exact floor/ceiling form used before replacing
it by the softer `O(Q/M + 1)` estimate. -/
theorem card_gmAffinePoissonNearSet_le
    (M : ℕ) (alpha Q : ℝ) :
    (gmAffinePoissonNearSet M alpha Q).card ≤
      (2 * ⌈Q / (8 * M : ℝ) + 1⌉ + 1).toNat := by
  let R : ℤ := ⌈Q / (8 * M : ℝ) + 1⌉
  calc
    (gmAffinePoissonNearSet M alpha Q).card ≤
        (Finset.Icc (-R - ⌊alpha⌋) (R - ⌊alpha⌋)).card := by
      unfold gmAffinePoissonNearSet
      dsimp only [R]
      exact Finset.card_filter_le _ _
    _ = (2 * R + 1).toNat := by
      rw [Int.card_Icc]
      congr 1
      ring

/-- Real cardinality bound for the retained modes.  The harmless absolute
constant five accounts exactly for the two endpoints and the ceiling. -/
theorem card_gmAffinePoissonNearSet_real_le
    {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q) :
    ((gmAffinePoissonNearSet M alpha Q).card : ℝ) ≤
      2 * (Q / (8 * M : ℝ)) + 5 := by
  let x : ℝ := Q / (8 * M : ℝ) + 1
  let R : ℤ := ⌈x⌉
  have hs : (0 : ℝ) < 8 * M := by positivity
  have hx : 0 < x := by dsimp only [x]; positivity
  have hRnonneg : 0 ≤ R := Int.ceil_nonneg hx.le
  have hcard := card_gmAffinePoissonNearSet_le M alpha Q
  have hcard' : (gmAffinePoissonNearSet M alpha Q).card ≤
      (2 * R + 1).toNat := by
    simpa only [R, x] using hcard
  have hcardReal : ((gmAffinePoissonNearSet M alpha Q).card : ℝ) ≤
      (((2 * R + 1).toNat : ℕ) : ℝ) := by
    exact_mod_cast hcard'
  have htoNat : (((2 * R + 1).toNat : ℕ) : ℤ) = 2 * R + 1 :=
    Int.toNat_of_nonneg (by omega)
  have hRlt : (R : ℝ) < x + 1 := by
    exact Int.ceil_lt_add_one x
  calc
    ((gmAffinePoissonNearSet M alpha Q).card : ℝ) ≤
        (((2 * R + 1).toNat : ℕ) : ℝ) := hcardReal
    _ = 2 * (R : ℝ) + 1 := by
      exact_mod_cast htoNat
    _ ≤ 2 * x + 3 := by linarith
    _ = 2 * (Q / (8 * M : ℝ)) + 5 := by
      dsimp only [x]
      ring

/-- The retained complex Poisson mode. -/
noncomputable def gmAffinePoissonNearTerm
    (M : ℕ) (hM : 0 < M) (alpha Q : ℝ) (ell : ℤ) : ℂ :=
  if |(8 * M : ℝ) * (alpha + ell)| < Q then
    gmAffineCentralPoissonKernel M hM (alpha + ell)
  else 0

theorem gmAffinePoissonNearTerm_eq_zero_of_not_mem
    {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} {ell : ℤ}
    (hell : ell ∉ gmAffinePoissonNearSet M alpha Q) :
    gmAffinePoissonNearTerm M hM alpha Q ell = 0 := by
  unfold gmAffinePoissonNearTerm
  split_ifs with hnear
  · exact False.elim (hell (mem_gmAffinePoissonNearSet_of_lt hM hnear))
  · rfl

theorem hasFiniteSupport_gmAffinePoissonNearTerm
    {M : ℕ} (hM : 0 < M) (alpha Q : ℝ) :
    Function.HasFiniteSupport (gmAffinePoissonNearTerm M hM alpha Q) := by
  apply Set.Finite.subset (gmAffinePoissonNearSet M alpha Q).finite_toSet
  intro ell hell
  simp only [Function.mem_support, ne_eq] at hell
  by_contra hmem
  exact hell (gmAffinePoissonNearTerm_eq_zero_of_not_mem hM hmem)

theorem summable_gmAffinePoissonNearTerm
    {M : ℕ} (hM : 0 < M) (alpha Q : ℝ) :
    Summable (gmAffinePoissonNearTerm M hM alpha Q) :=
  summable_of_hasFiniteSupport
    (hasFiniteSupport_gmAffinePoissonNearTerm hM alpha Q)

/-- The near and far terms form an exact partition of every translated
Poisson mode. -/
theorem gmAffineCentralPoissonKernel_eq_near_add_far
    {M : ℕ} (hM : 0 < M) (alpha Q : ℝ) (ell : ℤ) :
    gmAffineCentralPoissonKernel M hM (alpha + ell) =
      gmAffinePoissonNearTerm M hM alpha Q ell +
        gmAffinePoissonFarTerm M hM alpha Q ell := by
  unfold gmAffinePoissonNearTerm gmAffinePoissonFarTerm
  by_cases hnear : |(8 * M : ℝ) * (alpha + ell)| < Q
  · rw [if_pos hnear, if_neg (not_le.mpr hnear)]
    simp
  · rw [if_neg hnear, if_pos (le_of_not_gt hnear)]
    simp

/-- The retained near series is literally the finite sum over the exact
near-frequency set. -/
theorem tsum_gmAffinePoissonNearTerm_eq_sum
    {M : ℕ} (hM : 0 < M) (alpha Q : ℝ) :
    (∑' ell : ℤ, gmAffinePoissonNearTerm M hM alpha Q ell) =
      ∑ ell ∈ gmAffinePoissonNearSet M alpha Q,
        gmAffineCentralPoissonKernel M hM (alpha + ell) := by
  rw [tsum_eq_sum (s := gmAffinePoissonNearSet M alpha Q)]
  · apply Finset.sum_congr rfl
    intro ell hell
    unfold gmAffinePoissonNearTerm
    rw [if_pos (Finset.mem_filter.mp hell).2]
  · intro ell hell
    exact gmAffinePoissonNearTerm_eq_zero_of_not_mem hM hell

/-- Exact retained/omitted decomposition of the complete Poisson series.
The omitted piece is the absolutely summable complex remainder estimated
above. -/
theorem tsum_gmAffineCentralPoissonKernel_eq_near_add_far
    (n : ℕ) {M : ℕ} (hM : 0 < M) {alpha Q : ℝ} (hQ : 0 < Q) :
    (∑' ell : ℤ, gmAffineCentralPoissonKernel M hM (alpha + ell)) =
      (∑ ell ∈ gmAffinePoissonNearSet M alpha Q,
        gmAffineCentralPoissonKernel M hM (alpha + ell)) +
          gmAffinePoissonFarSeries M hM alpha Q := by
  have hnear := summable_gmAffinePoissonNearTerm hM alpha Q
  have hfar := summable_gmAffinePoissonFarTerm n hM (alpha := alpha) hQ
  calc
    (∑' ell : ℤ, gmAffineCentralPoissonKernel M hM (alpha + ell)) =
        ∑' ell : ℤ, (gmAffinePoissonNearTerm M hM alpha Q ell +
          gmAffinePoissonFarTerm M hM alpha Q ell) := by
      apply tsum_congr
      intro ell
      exact gmAffineCentralPoissonKernel_eq_near_add_far hM alpha Q ell
    _ = (∑' ell : ℤ, gmAffinePoissonNearTerm M hM alpha Q ell) +
          ∑' ell : ℤ, gmAffinePoissonFarTerm M hM alpha Q ell :=
      hnear.tsum_add hfar
    _ = (∑ ell ∈ gmAffinePoissonNearSet M alpha Q,
          gmAffineCentralPoissonKernel M hM (alpha + ell)) +
          gmAffinePoissonFarSeries M hM alpha Q := by
      rw [tsum_gmAffinePoissonNearTerm_eq_sum]
      rfl

/-- Exact Poisson summation for the weighted translation modes.  It is the
untruncated identity behind the outer `ℓ`-sum in Guth--Maynard (9.3). -/
theorem gmAffineCentralWeight_poisson
    (M : ℕ) (hM : 0 < M) (alpha : ℝ) :
    (∑' m : ℤ, (gmAffineCentralWeight M m : ℂ) *
        Complex.exp ((((2 * Real.pi * (m : ℝ) * alpha : ℝ) : ℂ) * I))) =
      ∑' ell : ℤ, gmAffineCentralPoissonKernel M hM (alpha + ell) := by
  have hPoisson :=
    SchwartzMap.tsum_eq_tsum_fourier (gmAffineCentralPoissonKernel M hM) alpha
  rw [gmAffineCentralPoissonKernel, fourier_fourierInv_eq] at hPoisson
  rw [gmAffineCentralPoissonKernel]
  rw [hPoisson]
  apply tsum_congr
  intro m
  rw [gmAffineCentralWeightSchwartz_int_apply]
  simp only [_root_.fourier_coe_apply]
  congr 2
  push_cast
  ring

theorem gmAffinePositiveShell_ne_zero
    {M : ℕ} (hM : 0 < M) {m : ℤ} (hm : m ∈ gmAffinePositiveShell M) :
    m ≠ 0 := by
  have hm' := (mem_gmAffinePositiveShell.mp hm).1
  exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast hM) hm')

theorem gmAffineSignedShell_ne_zero
    {M : ℕ} (hM : 0 < M) {m : ℤ} (hm : m ∈ gmAffineSignedShell M) :
    m ≠ 0 := by
  rcases mem_gmAffineSignedShell.mp hm with hmneg | hmpos
  · have hMposInt : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
    exact ne_of_lt (hmneg.2.trans_lt (neg_neg_of_pos hMposInt))
  · exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast hM) hmpos.1)

/-- One affine summand from (9.1). -/
noncomputable def gmAffineTerm (f : ℝ → ℝ) (m₁ m₂ m₃ : ℤ) (u : ℝ) : ℝ :=
  f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))

/-- The finite affine transformation sum inside `J(f)`. -/
noncomputable def gmAffineTransformSum
    (f : ℝ → ℝ) (M₁ M₂ M₃ : ℕ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ gmAffineSignedShell M₁,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      ∑ m₃ ∈ gmAffineCentralShell M₃, gmAffineTerm f m₁ m₂ m₃ u

/-- The smooth finite majorant `g` from equation (9.2).  The sum is finite
because `gmAffineCentralWeight` vanishes outside the doubled shell. -/
noncomputable def gmAffineSmoothTransformSum
    (f : ℝ → ℝ) (M₁ M₂ M₃ : ℕ) (u : ℝ) : ℝ :=
  ∑ m₁ ∈ gmAffineSignedShell M₁,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      ∑ m₃ ∈ gmAffineSmoothCentralShell M₃,
        gmAffineCentralWeight M₃ m₃ * gmAffineTerm f m₁ m₂ m₃ u

theorem gmAffineCentralShell_subset_smooth
    (M : ℕ) : gmAffineCentralShell M ⊆ gmAffineSmoothCentralShell M := by
  intro m hm
  rw [mem_gmAffineSmoothCentralShell]
  rcases mem_gmAffineCentralShell.mp hm with ⟨hmLower, hmUpper⟩
  constructor <;> omega

theorem gmAffineSmoothTransformSum_nonneg
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (M₁ M₂ M₃ : ℕ) (u : ℝ) :
    0 ≤ gmAffineSmoothTransformSum f M₁ M₂ M₃ u := by
  unfold gmAffineSmoothTransformSum
  apply Finset.sum_nonneg
  intro m₁ hm₁
  apply Finset.sum_nonneg
  intro m₂ hm₂
  apply Finset.sum_nonneg
  intro m₃ hm₃
  exact mul_nonneg (gmAffineCentralWeight_nonneg M₃ m₃) (hf _)

/-- Pointwise source bridge from the sharp finite central window to the
smooth Poisson majorant. -/
theorem gmAffineTransformSum_le_smooth
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x)
    {M₁ M₂ M₃ : ℕ} (hM₃ : 0 < M₃) (u : ℝ) :
    gmAffineTransformSum f M₁ M₂ M₃ u ≤
      gmAffineSmoothTransformSum f M₁ M₂ M₃ u := by
  unfold gmAffineTransformSum gmAffineSmoothTransformSum
  apply Finset.sum_le_sum
  intro m₁ hm₁
  apply Finset.sum_le_sum
  intro m₂ hm₂
  calc
    (∑ m₃ ∈ gmAffineCentralShell M₃, gmAffineTerm f m₁ m₂ m₃ u) =
        ∑ m₃ ∈ gmAffineCentralShell M₃,
          gmAffineCentralWeight M₃ m₃ * gmAffineTerm f m₁ m₂ m₃ u := by
      apply Finset.sum_congr rfl
      intro m₃ hm₃
      rw [gmAffineCentralWeight_eq_one hM₃ hm₃, one_mul]
    _ ≤ ∑ m₃ ∈ gmAffineSmoothCentralShell M₃,
          gmAffineCentralWeight M₃ m₃ * gmAffineTerm f m₁ m₂ m₃ u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (gmAffineCentralShell_subset_smooth M₃)
      intro m₃ hm₃ hnot
      exact mul_nonneg (gmAffineCentralWeight_nonneg M₃ m₃) (hf _)

/-! ## Schwartz realization and equation (9.2) -/

/-- A single affine pullback as a Schwartz function.  Both integer
coefficients are nonzero on the source shells. -/
noncomputable def gmAffineTermSchwartz
    (f : SchwartzMap ℝ ℂ) (m₁ m₂ m₃ : ℤ) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) :
    SchwartzMap ℝ ℂ := by
  let a : ℝ := (m₁ : ℝ) / (m₂ : ℝ)
  let b : ℝ := (m₃ : ℝ) / (m₂ : ℝ)
  have ha : a ≠ 0 := div_ne_zero (by exact_mod_cast hm₁) (by exact_mod_cast hm₂)
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 a ha)
  exact SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
    (f.compSubConstCLM ℂ (-b))

@[simp]
theorem gmAffineTermSchwartz_apply
    (f : SchwartzMap ℝ ℂ) (m₁ m₂ m₃ : ℤ) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)
    (u : ℝ) :
    gmAffineTermSchwartz f m₁ m₂ m₃ hm₁ hm₂ u =
      f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) := by
  dsimp only [gmAffineTermSchwartz]
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    SchwartzMap.compSubConstCLM_apply, ContinuousLinearEquiv.smulLeft_apply_apply,
    Units.smul_def, Units.val_mk0, smul_eq_mul, sub_neg_eq_add]
  congr 1
  field_simp [show (m₂ : ℝ) ≠ 0 by exact_mod_cast hm₂]

/-- Exact Fourier transform of one affine pullback.  The absolute Jacobian
is retained because the signed `m₁` shell contains both orientations. -/
theorem gmAffineTermSchwartz_fourier
    (f : SchwartzMap ℝ ℂ) (m₁ m₂ m₃ : ℤ) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)
    (ξ : ℝ) :
    𝓕 (gmAffineTermSchwartz f m₁ m₂ m₃ hm₁ hm₂) ξ =
      ((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * (m₃ : ℝ) * ξ / (m₁ : ℝ) : ℝ) : ℂ) * I)) *
          𝓕 f (((m₂ : ℝ) / (m₁ : ℝ)) * ξ) := by
  let a : ℝ := (m₁ : ℝ) / (m₂ : ℝ)
  let b : ℝ := (m₃ : ℝ) / (m₂ : ℝ)
  let q : ℝ → ℂ := fun x =>
    Complex.exp (((-2 * Real.pi * (((x - b) / a) * ξ) : ℝ) : ℂ) * I) * f x
  have hm₁R : (m₁ : ℝ) ≠ 0 := by exact_mod_cast hm₁
  have hm₂R : (m₂ : ℝ) ≠ 0 := by exact_mod_cast hm₂
  have ha : a ≠ 0 := div_ne_zero hm₁R hm₂R
  have hpoint : ∀ u : ℝ,
      Complex.exp (((-2 * Real.pi * (u * ξ) : ℝ) : ℂ) * I) *
          gmAffineTermSchwartz f m₁ m₂ m₃ hm₁ hm₂ u =
        q (a * u + b) := by
    intro u
    rw [gmAffineTermSchwartz_apply]
    dsimp only [q]
    have harg : (a * u + b - b) / a = u := by
      rw [show a * u + b - b = a * u by ring]
      exact mul_div_cancel_left₀ u ha
    rw [harg]
    congr 2
    dsimp only [a, b]
    field_simp [hm₂R]
  have hchange : (∫ u : ℝ, q (a * u + b)) = |a⁻¹| * ∫ x : ℝ, q x := by
    calc
      (∫ u : ℝ, q (a * u + b)) =
          |a⁻¹| * ∫ y : ℝ, q (y + b) := by
        simpa only [Function.comp_apply] using
          (MeasureTheory.Measure.integral_comp_mul_left (fun y : ℝ => q (y + b)) a)
      _ = |a⁻¹| * ∫ x : ℝ, q x := by rw [integral_add_right_eq_self]
  have hphase : ∀ x : ℝ,
      Complex.exp (((-2 * Real.pi * (((x - b) / a) * ξ) : ℝ) : ℂ) * I) =
        Complex.exp ((((2 * Real.pi * b * ξ / a : ℝ) : ℂ) * I)) *
          Complex.exp (((-2 * Real.pi * (x * (ξ / a)) : ℝ) : ℂ) * I) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp [ha]
    ring
  have hratio : ξ / ((m₁ : ℝ) / (m₂ : ℝ)) =
      ((m₂ : ℝ) / (m₁ : ℝ)) * ξ := by field_simp [hm₁R, hm₂R]
  have hphaseArg : 2 * Real.pi * b * ξ / a =
      2 * Real.pi * (m₃ : ℝ) * ξ / (m₁ : ℝ) := by
    dsimp only [a, b]
    field_simp [hm₁R, hm₂R]
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [Real.inner_apply, smul_eq_mul]
  calc
    (∫ u : ℝ,
        Complex.exp (((-2 * Real.pi * (u * ξ) : ℝ) : ℂ) * I) *
          gmAffineTermSchwartz f m₁ m₂ m₃ hm₁ hm₂ u) =
        ∫ u : ℝ, q (a * u + b) := by
      apply integral_congr_ae
      exact Eventually.of_forall hpoint
    _ = ((|a⁻¹| : ℝ) : ℂ) * ∫ x : ℝ, q x := hchange
    _ = ((|a⁻¹| : ℝ) : ℂ) *
          (Complex.exp ((((2 * Real.pi * b * ξ / a : ℝ) : ℂ) * I)) *
            ∫ x : ℝ,
              Complex.exp (((-2 * Real.pi * (x * (ξ / a)) : ℝ) : ℂ) * I) * f x) := by
      congr 1
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [q]
      rw [hphase x]
      ring_nf
    _ = ((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
          Complex.exp ((((2 * Real.pi * (m₃ : ℝ) * ξ / (m₁ : ℝ) : ℝ) : ℂ) * I)) *
            ∫ x : ℝ,
              Complex.exp (((-2 * Real.pi * (x *
                (((m₂ : ℝ) / (m₁ : ℝ)) * ξ)) : ℝ) : ℂ) * I) * f x := by
      rw [show |a⁻¹| = |(m₂ : ℝ) / (m₁ : ℝ)| by
        dsimp only [a]
        rw [inv_div]]
      rw [hratio]
      rw [hphaseArg]
      ring
    _ = ((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
          Complex.exp ((((2 * Real.pi * (m₃ : ℝ) * ξ / (m₁ : ℝ) : ℝ) : ℂ) * I)) *
            𝓕 f (((m₂ : ℝ) / (m₁ : ℝ)) * ξ) := by
      rw [SchwartzMap.fourier_coe, Real.fourier_eq']
      simp only [Real.inner_apply, smul_eq_mul]

/-- A total affine Schwartz term; the zero-coefficient cases never occur in
the positive dyadic shells but making them explicit keeps the finite sum
definition proof-independent. -/
noncomputable def gmAffineTermSchwartzTotal
    (f : SchwartzMap ℝ ℂ) (m₁ m₂ m₃ : ℤ) : SchwartzMap ℝ ℂ :=
  if hm₁ : m₁ = 0 then 0
  else if hm₂ : m₂ = 0 then 0
  else gmAffineTermSchwartz f m₁ m₂ m₃ hm₁ hm₂

theorem gmAffineTermSchwartzTotal_apply_of_ne
    (f : SchwartzMap ℝ ℂ) {m₁ m₂ : ℤ} (m₃ : ℤ) (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0)
    (u : ℝ) :
    gmAffineTermSchwartzTotal f m₁ m₂ m₃ u =
      f (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) := by
  rw [gmAffineTermSchwartzTotal, dif_neg hm₁, dif_neg hm₂]
  exact gmAffineTermSchwartz_apply f m₁ m₂ m₃ hm₁ hm₂ u

theorem gmAffineTermSchwartzTotal_fourier_of_ne
    (f : SchwartzMap ℝ ℂ) {m₁ m₂ : ℤ} (m₃ : ℤ)
    (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (ξ : ℝ) :
    𝓕 (gmAffineTermSchwartzTotal f m₁ m₂ m₃) ξ =
      ((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
        Complex.exp ((((2 * Real.pi * (m₃ : ℝ) * ξ / (m₁ : ℝ) : ℝ) : ℂ) * I)) *
          𝓕 f (((m₂ : ℝ) / (m₁ : ℝ)) * ξ) := by
  rw [gmAffineTermSchwartzTotal, dif_neg hm₁, dif_neg hm₂]
  exact gmAffineTermSchwartz_fourier f m₁ m₂ m₃ hm₁ hm₂ ξ

/-- Complexification of a real Schwartz function, used with Mathlib's
unitary Fourier transform. -/
noncomputable def gmAffineComplexify (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℂ :=
  f.postcompCLM Complex.ofRealCLM

@[simp]
theorem gmAffineComplexify_apply (f : SchwartzMap ℝ ℝ) (u : ℝ) :
    gmAffineComplexify f u = (f u : ℂ) := rfl

/-- The Schwartz-space realization of the smooth finite majorant `g`. -/
noncomputable def gmAffineSmoothTransformSchwartz
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) : SchwartzMap ℝ ℂ :=
  ∑ m₁ ∈ gmAffineSignedShell M₁,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      ∑ m₃ ∈ gmAffineSmoothCentralShell M₃,
        (gmAffineCentralWeight M₃ m₃ : ℂ) •
          gmAffineTermSchwartzTotal (gmAffineComplexify f) m₁ m₂ m₃

@[simp]
theorem gmAffineSmoothTransformSchwartz_apply
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (u : ℝ) :
    gmAffineSmoothTransformSchwartz f M₁ M₂ M₃ u =
      (gmAffineSmoothTransformSum f M₁ M₂ M₃ u : ℂ) := by
  unfold gmAffineSmoothTransformSchwartz gmAffineSmoothTransformSum
  simp only [SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  apply Finset.sum_congr rfl
  intro m₃ hm₃
  rw [gmAffineTermSchwartzTotal_apply_of_ne (gmAffineComplexify f) m₃
    (gmAffineSignedShell_ne_zero hM₁ hm₁)
    (gmAffinePositiveShell_ne_zero hM₂ hm₂)]
  rfl

/-- Exact finite Fourier expansion of the smooth affine majorant before
Poisson summation in the translation variable.  This is the literal first
line of Guth--Maynard's computation preceding equation (9.3). -/
theorem gmAffineSmoothTransformSchwartz_fourier
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ξ : ℝ) :
    𝓕 (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) ξ =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∑ m₃ ∈ gmAffineSmoothCentralShell M₃,
            (gmAffineCentralWeight M₃ m₃ : ℂ) *
              (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
                Complex.exp ((((2 * Real.pi * (m₃ : ℝ) * ξ /
                  (m₁ : ℝ) : ℝ) : ℂ) * I)) *
                  𝓕 (gmAffineComplexify f)
                    (((m₂ : ℝ) / (m₁ : ℝ)) * ξ)) := by
  unfold gmAffineSmoothTransformSchwartz
  simp only [fourier_sum, fourier_smul, SchwartzMap.sum_apply, SchwartzMap.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  apply Finset.sum_congr rfl
  intro m₃ hm₃
  rw [gmAffineTermSchwartzTotal_fourier_of_ne (gmAffineComplexify f) m₃
    (gmAffineSignedShell_ne_zero hM₁ hm₁)
    (gmAffinePositiveShell_ne_zero hM₂ hm₂)]

/-- The finite translation-character sum appearing after the affine change
of variables. -/
noncomputable def gmAffineTranslationPhaseSum
    (M : ℕ) (m₁ : ℤ) (ξ : ℝ) : ℂ :=
  ∑ m₃ ∈ gmAffineSmoothCentralShell M,
    (gmAffineCentralWeight M m₃ : ℂ) *
      Complex.exp ((((2 * Real.pi * (m₃ : ℝ) * ξ / (m₁ : ℝ) : ℝ) : ℂ) * I))

theorem gmAffineTranslationPhaseSum_eq_tsum
    {M : ℕ} (hM : 0 < M) (m₁ : ℤ) (ξ : ℝ) :
    gmAffineTranslationPhaseSum M m₁ ξ =
      ∑' m₃ : ℤ, (gmAffineCentralWeight M m₃ : ℂ) *
        Complex.exp ((((2 * Real.pi * (m₃ : ℝ) *
          (ξ / (m₁ : ℝ)) : ℝ) : ℂ) * I)) := by
  unfold gmAffineTranslationPhaseSum
  rw [tsum_eq_sum (s := gmAffineSmoothCentralShell M)]
  · apply Finset.sum_congr rfl
    intro m₃ hm₃
    congr 2
    push_cast
    ring
  · intro m₃ hm₃
    rw [gmAffineCentralWeight_eq_zero_of_not_mem hM hm₃]
    simp

/-- Exact Poisson form of the finite translation-character sum. -/
theorem gmAffineTranslationPhaseSum_poisson
    {M : ℕ} (hM : 0 < M) (m₁ : ℤ) (ξ : ℝ) :
    gmAffineTranslationPhaseSum M m₁ ξ =
      ∑' ell : ℤ, gmAffineCentralPoissonKernel M hM
        (ξ / (m₁ : ℝ) + ell) := by
  rw [gmAffineTranslationPhaseSum_eq_tsum hM m₁]
  exact gmAffineCentralWeight_poisson M hM (ξ / (m₁ : ℝ))

/-- Regroup the exact finite Fourier expansion into one translation phase
sum for each pair `(m₁,m₂)`. -/
theorem gmAffineSmoothTransformSchwartz_fourier_regroup
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (ξ : ℝ) :
    𝓕 (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) ξ =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
            𝓕 (gmAffineComplexify f)
              (((m₂ : ℝ) / (m₁ : ℝ)) * ξ)) *
            gmAffineTranslationPhaseSum M₃ m₁ ξ := by
  rw [gmAffineSmoothTransformSchwartz_fourier f hM₁ hM₂ ξ]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  unfold gmAffineTranslationPhaseSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m₃ hm₃
  ring

/-- The complete, untruncated Poisson expansion underlying (9.3).  No
frequency has yet been discarded, so this is an equality rather than an
asymptotic estimate. -/
theorem gmAffineSmoothTransformSchwartz_fourier_poisson
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) (ξ : ℝ) :
    𝓕 (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) ξ =
      ∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
            𝓕 (gmAffineComplexify f)
              (((m₂ : ℝ) / (m₁ : ℝ)) * ξ)) *
            (∑' ell : ℤ, gmAffineCentralPoissonKernel M₃ hM₃
              (ξ / (m₁ : ℝ) + ell)) := by
  rw [gmAffineSmoothTransformSchwartz_fourier_regroup f hM₁ hM₂ ξ]
  apply Finset.sum_congr rfl
  intro m₁ hm₁
  apply Finset.sum_congr rfl
  intro m₂ hm₂
  rw [gmAffineTranslationPhaseSum_poisson hM₃ m₁]

/-- The retained part of the affine Fourier transform in equation (9.3).
All three frequency variables are now finite. -/
noncomputable def gmAffinePoissonMainFourier
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (Q ξ : ℝ) : ℂ :=
  ∑ m₁ ∈ gmAffineSignedShell M₁,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
        𝓕 (gmAffineComplexify f)
          (((m₂ : ℝ) / (m₁ : ℝ)) * ξ)) *
        (∑ ell ∈ gmAffinePoissonNearSet M₃ (ξ / (m₁ : ℝ)) Q,
          gmAffineCentralPoissonKernel M₃ hM₃
            (ξ / (m₁ : ℝ) + ell))

/-- The complete omitted-frequency contribution in equation (9.3). -/
noncomputable def gmAffinePoissonFarFourier
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (hM₃ : 0 < M₃)
    (Q ξ : ℝ) : ℂ :=
  ∑ m₁ ∈ gmAffineSignedShell M₁,
    ∑ m₂ ∈ gmAffinePositiveShell M₂,
      (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
        𝓕 (gmAffineComplexify f)
          (((m₂ : ℝ) / (m₁ : ℝ)) * ξ)) *
        gmAffinePoissonFarSeries M₃ hM₃ (ξ / (m₁ : ℝ)) Q

/-- Exact equation (9.3): finite retained modes plus the complete
absolutely summable omitted-frequency contribution. -/
theorem gmAffineSmoothTransformSchwartz_fourier_eq_main_add_far
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 0 < Q) (ξ : ℝ) :
    𝓕 (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) ξ =
      gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q ξ +
        gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q ξ := by
  rw [gmAffineSmoothTransformSchwartz_fourier_poisson f hM₁ hM₂ hM₃ ξ]
  have hsplit : ∀ m₁ : ℤ,
      (∑' ell : ℤ, gmAffineCentralPoissonKernel M₃ hM₃
          (ξ / (m₁ : ℝ) + ell)) =
        (∑ ell ∈ gmAffinePoissonNearSet M₃ (ξ / (m₁ : ℝ)) Q,
          gmAffineCentralPoissonKernel M₃ hM₃
            (ξ / (m₁ : ℝ) + ell)) +
          gmAffinePoissonFarSeries M₃ hM₃ (ξ / (m₁ : ℝ)) Q := by
    intro m₁
    exact tsum_gmAffineCentralPoissonKernel_eq_near_add_far
      n hM₃ (alpha := ξ / (m₁ : ℝ)) hQ
  simp_rw [hsplit, mul_add, Finset.sum_add_distrib]
  rfl

/-- Equation (9.2): exact Plancherel for the smooth affine majorant. -/
theorem integral_gmAffineSmoothTransformSum_sq_eq_fourier
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    (∫ u : ℝ, gmAffineSmoothTransformSum f M₁ M₂ M₃ u ^ 2) =
      ∫ ξ : ℝ, ‖𝓕 (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) ξ‖ ^ 2 := by
  rw [SchwartzMap.integral_norm_sq_fourier]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [gmAffineSmoothTransformSchwartz_apply f hM₁ hM₂ u]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### The three frequency regions in the proof of Lemma 9.2 -/

/-- Region I of (9.4). -/
def gmAffineLowFrequencyRegion (X : ℝ) : Set ℝ :=
  {xi : ℝ | |xi| ≤ X}

/-- Region II of (9.4).  The lower endpoint is deliberately open, so the
three regions form an exact disjoint partition. -/
def gmAffineMiddleFrequencyRegion (X Y : ℝ) : Set ℝ :=
  {xi : ℝ | X < |xi| ∧ |xi| ≤ Y}

/-- Region III of (9.4). -/
def gmAffineHighFrequencyRegion (Y : ℝ) : Set ℝ :=
  {xi : ℝ | Y < |xi|}

theorem measurableSet_gmAffineLowFrequencyRegion (X : ℝ) :
    MeasurableSet (gmAffineLowFrequencyRegion X) := by
  exact measurableSet_le continuous_abs.measurable measurable_const

theorem measurableSet_gmAffineMiddleFrequencyRegion (X Y : ℝ) :
    MeasurableSet (gmAffineMiddleFrequencyRegion X Y) := by
  exact (measurableSet_lt measurable_const continuous_abs.measurable).inter
    (measurableSet_le continuous_abs.measurable measurable_const)

theorem measurableSet_gmAffineHighFrequencyRegion (Y : ℝ) :
    MeasurableSet (gmAffineHighFrequencyRegion Y) := by
  exact measurableSet_lt measurable_const continuous_abs.measurable

theorem gmAffine_frequency_regions_union
    (X Y : ℝ) :
    gmAffineLowFrequencyRegion X ∪
        (gmAffineMiddleFrequencyRegion X Y ∪
          gmAffineHighFrequencyRegion Y) = Set.univ := by
  ext xi
  simp only [gmAffineLowFrequencyRegion, gmAffineMiddleFrequencyRegion,
    gmAffineHighFrequencyRegion, Set.mem_union, Set.mem_setOf_eq,
    Set.mem_univ, iff_true]
  by_cases hlow : |xi| ≤ X
  · exact Or.inl hlow
  · right
    by_cases hhigh : Y < |xi|
    · exact Or.inr hhigh
    · exact Or.inl ⟨lt_of_not_ge hlow, le_of_not_gt hhigh⟩

theorem disjoint_gmAffineLowFrequencyRegion_middle
    (X Y : ℝ) :
    Disjoint (gmAffineLowFrequencyRegion X)
      (gmAffineMiddleFrequencyRegion X Y) := by
  rw [Set.disjoint_left]
  intro xi hlow hmid
  exact (not_lt_of_ge hlow) hmid.1

theorem disjoint_gmAffineLowFrequencyRegion_high
    {X Y : ℝ} (hXY : X ≤ Y) :
    Disjoint (gmAffineLowFrequencyRegion X)
      (gmAffineHighFrequencyRegion Y) := by
  rw [Set.disjoint_left]
  intro xi hlow hhigh
  exact (not_lt_of_ge (hlow.trans hXY)) hhigh

theorem disjoint_gmAffineMiddleFrequencyRegion_high
    (X Y : ℝ) :
    Disjoint (gmAffineMiddleFrequencyRegion X Y)
      (gmAffineHighFrequencyRegion Y) := by
  rw [Set.disjoint_left]
  intro xi hmid hhigh
  exact (not_lt_of_ge hmid.2) hhigh

theorem gmAffineLowFrequencyRegion_eq_Icc (X : ℝ) :
    gmAffineLowFrequencyRegion X = Set.Icc (-X) X := by
  ext xi
  simp only [gmAffineLowFrequencyRegion, Set.mem_setOf_eq, Set.mem_Icc,
    abs_le]

theorem gmAffineHighFrequencyRegion_eq_union
    {Y : ℝ} (hY : 0 ≤ Y) :
    gmAffineHighFrequencyRegion Y = Set.Iio (-Y) ∪ Set.Ioi Y := by
  ext xi
  simp only [gmAffineHighFrequencyRegion, Set.mem_setOf_eq, Set.mem_union,
    Set.mem_Iio, Set.mem_Ioi]
  by_cases hxi : 0 ≤ xi
  · rw [abs_of_nonneg hxi]
    constructor
    · exact fun h => Or.inr h
    · intro h
      rcases h with hleft | hright
      · exfalso
        linarith
      · exact hright
  · have hxi' : xi < 0 := lt_of_not_ge hxi
    rw [abs_of_neg hxi']
    constructor
    · exact fun h => Or.inl (by linarith)
    · intro h
      rcases h with hleft | hright
      · linarith
      · exfalso
        linarith

theorem volume_real_gmAffineLowFrequencyRegion
    {X : ℝ} (hX : 0 ≤ X) :
    volume.real (gmAffineLowFrequencyRegion X) = 2 * X := by
  rw [gmAffineLowFrequencyRegion_eq_Icc,
    Real.volume_real_Icc_of_le (by linarith)]
  ring

set_option maxHeartbeats 800000 in
/-- Exact integrable power tail on the symmetric Region III. -/
theorem integral_gmAffineHighFrequencyRegion_abs_rpow
    {a Y : ℝ} (ha : a < -1) (hY : 0 < Y) :
    (∫ xi in gmAffineHighFrequencyRegion Y, |xi| ^ a) =
      2 * (-Y ^ (a + 1) / (a + 1)) := by
  have hpos : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioi Y) :=
    integrableOn_Ioi_rpow_of_lt ha hY
  have hpos' : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioi (-(-Y))) := by
    simpa only [neg_neg] using hpos
  have hnegRaw : IntegrableOn (fun x : ℝ => (-x) ^ a) (Set.Iio (-Y)) :=
    hpos'.comp_neg_Iio
  have hneg : IntegrableOn (fun x : ℝ => |x| ^ a) (Set.Iio (-Y)) := by
    apply hnegRaw.congr_fun
    · intro x hx
      have hxneg : x < 0 := hx.trans (neg_neg_of_pos hY)
      change (-x) ^ a = |x| ^ a
      rw [abs_of_neg hxneg]
    · exact measurableSet_Iio
  have hposAbs : IntegrableOn (fun x : ℝ => |x| ^ a) (Set.Ioi Y) := by
    apply hpos.congr_fun
    · intro x hx
      change x ^ a = |x| ^ a
      rw [abs_of_pos (hY.trans hx)]
    · exact measurableSet_Ioi
  have hdisjoint : Disjoint (Set.Iio (-Y)) (Set.Ioi Y) := by
    rw [Set.disjoint_left]
    intro x hxneg hxpos
    change x < -Y at hxneg
    change Y < x at hxpos
    linarith
  rw [gmAffineHighFrequencyRegion_eq_union hY.le]
  rw [MeasureTheory.setIntegral_union hdisjoint measurableSet_Ioi hneg hposAbs]
  have hnegEq :
      (∫ x in Set.Iio (-Y), |x| ^ a) = ∫ x in Set.Ioi Y, x ^ a := by
    rw [← integral_Iic_eq_integral_Iio]
    rw [← integral_comp_neg_Ioi]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change |(-x)| ^ a = x ^ a
    rw [abs_neg, abs_of_pos (hY.trans hx)]
  have hposEq : (∫ x in Set.Ioi Y, |x| ^ a) = ∫ x in Set.Ioi Y, x ^ a := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change |x| ^ a = x ^ a
    rw [abs_of_pos (hY.trans hx)]
  rw [hnegEq, hposEq, integral_Ioi_rpow_of_lt ha hY]
  ring

theorem integrableOn_gmAffineHighFrequencyRegion_abs_rpow
    {a Y : ℝ} (ha : a < -1) (hY : 0 < Y) :
    IntegrableOn (fun xi : ℝ => |xi| ^ a)
      (gmAffineHighFrequencyRegion Y) := by
  have hpos : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioi Y) :=
    integrableOn_Ioi_rpow_of_lt ha hY
  have hpos' : IntegrableOn (fun x : ℝ => x ^ a) (Set.Ioi (-(-Y))) := by
    simpa only [neg_neg] using hpos
  have hnegRaw : IntegrableOn (fun x : ℝ => (-x) ^ a) (Set.Iio (-Y)) :=
    hpos'.comp_neg_Iio
  have hneg : IntegrableOn (fun x : ℝ => |x| ^ a) (Set.Iio (-Y)) := by
    apply hnegRaw.congr_fun
    · intro x hx
      have hxneg : x < 0 := hx.trans (neg_neg_of_pos hY)
      change (-x) ^ a = |x| ^ a
      rw [abs_of_neg hxneg]
    · exact measurableSet_Iio
  have hposAbs : IntegrableOn (fun x : ℝ => |x| ^ a) (Set.Ioi Y) := by
    apply hpos.congr_fun
    · intro x hx
      change x ^ a = |x| ^ a
      rw [abs_of_pos (hY.trans hx)]
    · exact measurableSet_Ioi
  rw [gmAffineHighFrequencyRegion_eq_union hY.le]
  exact hneg.union hposAbs

set_option maxHeartbeats 800000 in
/-- A `C/|xi|^n` pointwise estimate integrates explicitly over Region III.
This is the abstract integration step used to obtain (9.5). -/
theorem integral_gmAffineHighFrequencyRegion_sq_le
    {G : ℝ → ℂ} {C Y : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hY : 0 < Y) (hC : 0 ≤ C)
    (hGInt : IntegrableOn (fun xi : ℝ => ‖G xi‖ ^ 2)
      (gmAffineHighFrequencyRegion Y))
    (hG : ∀ xi ∈ gmAffineHighFrequencyRegion Y,
      ‖G xi‖ ≤ C / |xi| ^ n) :
    (∫ xi in gmAffineHighFrequencyRegion Y, ‖G xi‖ ^ 2) ≤
      C ^ 2 *
        (2 * (-Y ^ ((-(2 * (n : ℝ))) + 1) /
          ((-(2 * (n : ℝ))) + 1))) := by
  let a : ℝ := -(2 * (n : ℝ))
  have ha : a < -1 := by
    dsimp only [a]
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpowInt : IntegrableOn (fun xi : ℝ => |xi| ^ a)
      (gmAffineHighFrequencyRegion Y) :=
    integrableOn_gmAffineHighFrequencyRegion_abs_rpow ha hY
  have hmajorInt : IntegrableOn (fun xi : ℝ => C ^ 2 * |xi| ^ a)
      (gmAffineHighFrequencyRegion Y) := hpowInt.const_mul _
  have hpoint : ∀ xi ∈ gmAffineHighFrequencyRegion Y,
      ‖G xi‖ ^ 2 ≤ C ^ 2 * |xi| ^ a := by
    intro xi hxi
    have habs : 0 < |xi| := hY.trans hxi
    have hsq : ‖G xi‖ ^ 2 ≤ (C / |xi| ^ n) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (div_nonneg hC (pow_nonneg (abs_nonneg xi) n))).mpr (hG xi hxi)
    calc
      ‖G xi‖ ^ 2 ≤ (C / |xi| ^ n) ^ 2 := hsq
      _ = C ^ 2 * |xi| ^ a := by
        dsimp only [a]
        rw [Real.rpow_neg habs.le]
        have hp : (|xi| ^ n) ^ 2 = |xi| ^ (2 * (n : ℝ)) := by
          rw [← pow_mul, ← Real.rpow_natCast]
          congr 1
          norm_num
          ring
        rw [div_pow, div_eq_mul_inv, hp]
  have hmono := MeasureTheory.setIntegral_mono_on hGInt hmajorInt
    (measurableSet_gmAffineHighFrequencyRegion Y) hpoint
  calc
    (∫ xi in gmAffineHighFrequencyRegion Y, ‖G xi‖ ^ 2) ≤
        ∫ xi in gmAffineHighFrequencyRegion Y, C ^ 2 * |xi| ^ a := hmono
    _ = C ^ 2 * (∫ xi in gmAffineHighFrequencyRegion Y, |xi| ^ a) := by
      rw [MeasureTheory.integral_const_mul]
    _ = C ^ 2 *
        (2 * (-Y ^ ((-(2 * (n : ℝ))) + 1) /
          ((-(2 * (n : ℝ))) + 1))) := by
      rw [integral_gmAffineHighFrequencyRegion_abs_rpow ha hY]

/-- A pointwise Fourier bound on Region I integrates with exactly the
length `2X`; this is the measure-theoretic step in (9.6). -/
theorem integral_gmAffineLowFrequencyRegion_sq_le
    {G : ℝ → ℂ} {X B : ℝ} (hX : 0 ≤ X)
    (hB : ∀ xi ∈ gmAffineLowFrequencyRegion X, ‖G xi‖ ≤ B) :
    (∫ xi in gmAffineLowFrequencyRegion X, ‖G xi‖ ^ 2) ≤
      2 * X * B ^ 2 := by
  have hmeasure : volume (Set.Icc (-X) X) < ⊤ := measure_Icc_lt_top
  rw [← gmAffineLowFrequencyRegion_eq_Icc] at hmeasure
  have hnorm := norm_setIntegral_le_of_norm_le_const hmeasure
    (f := fun xi : ℝ => ‖G xi‖ ^ 2) (C := B ^ 2) (fun xi hxi => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (norm_nonneg _)
        ((norm_nonneg _).trans (hB xi hxi))).mpr (hB xi hxi))
  have hintegral :
      0 ≤ ∫ xi in gmAffineLowFrequencyRegion X, ‖G xi‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  rw [Real.norm_of_nonneg hintegral,
    volume_real_gmAffineLowFrequencyRegion hX] at hnorm
  nlinarith only [hnorm]

/-- The Fourier energy in (9.2) is integrable before any region is
estimated. -/
theorem integrable_gmAffineSmoothTransform_fourier_sq
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) :
    Integrable (fun xi : ℝ =>
      ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) := by
  let g := fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃)
  have hg : Integrable (fun xi : ℝ => ‖g xi‖ ^ (2 : ℝ)) := by
    simpa using (g.memLp (2 : ENNReal)).integrable_norm_rpow
      (by norm_num : (2 : ENNReal) ≠ 0) ENNReal.ofNat_ne_top
  simpa only [g, Real.rpow_two] using hg

/-- Exact decomposition of the Plancherel integral into regions I, II and
III of equation (9.4). -/
theorem integral_gmAffineSmoothTransform_fourier_sq_eq_regions
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ)
    {X Y : ℝ} (hXY : X ≤ Y) :
    (∫ xi : ℝ,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) =
      (∫ xi in gmAffineLowFrequencyRegion X,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) +
      (∫ xi in gmAffineMiddleFrequencyRegion X Y,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) +
      (∫ xi in gmAffineHighFrequencyRegion Y,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) := by
  let F : ℝ → ℝ := fun xi =>
    ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2
  have hF : Integrable F :=
    integrable_gmAffineSmoothTransform_fourier_sq f M₁ M₂ M₃
  have hmidHigh :
      ∫ xi in gmAffineMiddleFrequencyRegion X Y ∪
          gmAffineHighFrequencyRegion Y, F xi =
        (∫ xi in gmAffineMiddleFrequencyRegion X Y, F xi) +
          ∫ xi in gmAffineHighFrequencyRegion Y, F xi := by
    exact MeasureTheory.setIntegral_union
      (disjoint_gmAffineMiddleFrequencyRegion_high X Y)
      (measurableSet_gmAffineHighFrequencyRegion Y)
      (hF.integrableOn) (hF.integrableOn)
  have hlowRest :
      ∫ xi in gmAffineLowFrequencyRegion X ∪
          (gmAffineMiddleFrequencyRegion X Y ∪
            gmAffineHighFrequencyRegion Y), F xi =
        (∫ xi in gmAffineLowFrequencyRegion X, F xi) +
          ∫ xi in gmAffineMiddleFrequencyRegion X Y ∪
            gmAffineHighFrequencyRegion Y, F xi := by
    apply MeasureTheory.setIntegral_union
    · exact (disjoint_gmAffineLowFrequencyRegion_middle X Y).union_right
        (disjoint_gmAffineLowFrequencyRegion_high hXY)
    · exact (measurableSet_gmAffineMiddleFrequencyRegion X Y).union
        (measurableSet_gmAffineHighFrequencyRegion Y)
    · exact hF.integrableOn
    · exact hF.integrableOn
  change (∫ xi : ℝ, F xi) =
    (∫ xi in gmAffineLowFrequencyRegion X, F xi) +
      (∫ xi in gmAffineMiddleFrequencyRegion X Y, F xi) +
        ∫ xi in gmAffineHighFrequencyRegion Y, F xi
  rw [← MeasureTheory.setIntegral_univ]
  rw [← gmAffine_frequency_regions_union X Y]
  rw [hlowRest, hmidHigh]
  ring

theorem integrable_gmAffineSmoothTransformSum_sq
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    Integrable (fun u : ℝ => gmAffineSmoothTransformSum f M₁ M₂ M₃ u ^ 2) := by
  let g := gmAffineSmoothTransformSchwartz f M₁ M₂ M₃
  have hg : Integrable (fun u : ℝ => ‖g u‖ ^ (2 : ℝ)) := by
    simpa using (g.memLp (2 : ENNReal)).integrable_norm_rpow
      (by norm_num : (2 : ENNReal) ≠ 0) ENNReal.ofNat_ne_top
  apply hg.congr
  filter_upwards with u
  dsimp only [g]
  rw [gmAffineSmoothTransformSchwartz_apply f hM₁ hM₂ u]
  simp only [Complex.norm_real, Real.norm_eq_abs, Real.rpow_two, sq_abs]

/-- The single finite index set underlying the three nested sums in (9.1). -/
noncomputable def gmAffineIndexSet (M₁ M₂ M₃ : ℕ) : Finset (ℤ × (ℤ × ℤ)) :=
  (gmAffineSignedShell M₁).product
    ((gmAffinePositiveShell M₂).product (gmAffineCentralShell M₃))

theorem mem_gmAffineIndexSet {M₁ M₂ M₃ : ℕ} {p : ℤ × (ℤ × ℤ)} :
    p ∈ gmAffineIndexSet M₁ M₂ M₃ ↔
      p.1 ∈ gmAffineSignedShell M₁ ∧
      p.2.1 ∈ gmAffinePositiveShell M₂ ∧
      p.2.2 ∈ gmAffineCentralShell M₃ := by
  simp [gmAffineIndexSet]

theorem gmAffineTransformSum_eq_indexSum
    (f : ℝ → ℝ) (M₁ M₂ M₃ : ℕ) (u : ℝ) :
    gmAffineTransformSum f M₁ M₂ M₃ u =
      ∑ p ∈ gmAffineIndexSet M₁ M₂ M₃,
        gmAffineTerm f p.1 p.2.1 p.2.2 u := by
  rw [gmAffineTransformSum, gmAffineIndexSet]
  calc
    (∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          ∑ m₃ ∈ gmAffineCentralShell M₃, gmAffineTerm f m₁ m₂ m₃ u) =
        ∑ m₁ ∈ gmAffineSignedShell M₁,
          ∑ q ∈ (gmAffinePositiveShell M₂).product (gmAffineCentralShell M₃),
            gmAffineTerm f m₁ q.1 q.2 u := by
      apply Finset.sum_congr rfl
      intro m₁ hm₁
      exact (Finset.sum_product'
        (gmAffinePositiveShell M₂) (gmAffineCentralShell M₃)
        (fun m₂ m₃ => gmAffineTerm f m₁ m₂ m₃ u)).symm
    _ = ∑ p ∈ (gmAffineSignedShell M₁).product
          ((gmAffinePositiveShell M₂).product (gmAffineCentralShell M₃)),
            gmAffineTerm f p.1 p.2.1 p.2.2 u :=
      (Finset.sum_product' (gmAffineSignedShell M₁)
        ((gmAffinePositiveShell M₂).product (gmAffineCentralShell M₃))
        (fun m₁ q => gmAffineTerm f m₁ q.1 q.2 u)).symm

/-- The selected-scale integral whose finite supremum is denoted `J(f)` in
the paper. -/
noncomputable def gmAffineTransformIntegral
    (f : ℝ → ℝ) (M₁ M₂ M₃ : ℕ) : ℝ :=
  ∫ u : ℝ, gmAffineTransformSum f M₁ M₂ M₃ u ^ 2

/-- The complete source-entry inequality in equation (9.2): the sharp
selected-scale affine integral is dominated by the Plancherel mass of the
smooth majorant. -/
theorem gmAffineTransformIntegral_le_smooth_fourier
    (f : SchwartzMap ℝ ℝ) (hf : ∀ x, 0 ≤ f x)
    {M₁ M₂ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) :
    gmAffineTransformIntegral f M₁ M₂ M₃ ≤
      ∫ ξ : ℝ, ‖𝓕 (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) ξ‖ ^ 2 := by
  rw [← integral_gmAffineSmoothTransformSum_sq_eq_fourier f hM₁ hM₂]
  unfold gmAffineTransformIntegral
  apply integral_mono_of_nonneg
    (Eventually.of_forall fun _ => sq_nonneg _)
    (integrable_gmAffineSmoothTransformSum_sq f hM₁ hM₂)
  filter_upwards with u
  have hsharp : 0 ≤ gmAffineTransformSum f M₁ M₂ M₃ u := by
    unfold gmAffineTransformSum
    apply Finset.sum_nonneg
    intro m₁ hm₁
    apply Finset.sum_nonneg
    intro m₂ hm₂
    apply Finset.sum_nonneg
    intro m₃ hm₃
    exact hf _
  have hsmooth := gmAffineSmoothTransformSum_nonneg hf M₁ M₂ M₃ u
  exact (sq_le_sq₀ hsharp hsmooth).mpr
    (gmAffineTransformSum_le_smooth hf hM₃ u)

/-- Admissible positive subscale triples below the terminal scale `M`. -/
def gmAffineScaleTriples (M : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  ((Finset.Icc 1 M).product ((Finset.Icc 1 M).product (Finset.Icc 1 M)))

theorem mem_gmAffineScaleTriples {M M₁ M₂ M₃ : ℕ} :
    (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ↔
      1 ≤ M₁ ∧ M₁ ≤ M ∧ 1 ≤ M₂ ∧ M₂ ≤ M ∧ 1 ≤ M₃ ∧ M₃ ≤ M := by
  simp [gmAffineScaleTriples]
  aesop

/-- The exact finite set of values over which the paper takes the supremum
in its definition of `J(f)`. -/
noncomputable def gmAffineIntegralValues (f : ℝ → ℝ) (M : ℕ) : Finset ℝ :=
  (gmAffineScaleTriples M).image fun p =>
    gmAffineTransformIntegral f p.1 p.2.1 p.2.2

/-- A total version of the finite supremum `J(f)`.  For `M > 0` the value
set is nonempty, so the `0` branch is inactive. -/
noncomputable def gmAffineJ (f : ℝ → ℝ) (M : ℕ) : ℝ :=
  if h : (gmAffineIntegralValues f M).Nonempty then
    (gmAffineIntegralValues f M).max' h
  else 0

theorem gmAffineScaleTriples_nonempty {M : ℕ} (hM : 0 < M) :
    (gmAffineScaleTriples M).Nonempty := by
  refine ⟨(1, 1, 1), ?_⟩
  exact mem_gmAffineScaleTriples.mpr ⟨le_rfl, hM, le_rfl, hM, le_rfl, hM⟩

theorem gmAffineIntegralValues_nonempty
    (f : ℝ → ℝ) {M : ℕ} (hM : 0 < M) :
    (gmAffineIntegralValues f M).Nonempty := by
  obtain ⟨p, hp⟩ := gmAffineScaleTriples_nonempty hM
  exact ⟨gmAffineTransformIntegral f p.1 p.2.1 p.2.2,
    Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

theorem gmAffineTransformIntegral_le_J
    (f : ℝ → ℝ) {M M₁ M₂ M₃ : ℕ} (hM : 0 < M)
    (hscale : (M₁, M₂, M₃) ∈ gmAffineScaleTriples M) :
    gmAffineTransformIntegral f M₁ M₂ M₃ ≤ gmAffineJ f M := by
  let S := gmAffineIntegralValues f M
  have hS : S.Nonempty := gmAffineIntegralValues_nonempty f hM
  have hmem : gmAffineTransformIntegral f M₁ M₂ M₃ ∈ S := by
    exact Finset.mem_image.mpr ⟨(M₁, M₂, M₃), hscale, rfl⟩
  rw [gmAffineJ, dif_pos hS]
  exact Finset.le_max' S _ hmem

theorem exists_gmAffineTransformIntegral_eq_J
    (f : ℝ → ℝ) {M : ℕ} (hM : 0 < M) :
    ∃ M₁ M₂ M₃,
      (M₁, M₂, M₃) ∈ gmAffineScaleTriples M ∧
      gmAffineTransformIntegral f M₁ M₂ M₃ = gmAffineJ f M := by
  let S := gmAffineIntegralValues f M
  have hS : S.Nonempty := gmAffineIntegralValues_nonempty f hM
  have hmaxMem : S.max' hS ∈ S := Finset.max'_mem S hS
  obtain ⟨p, hp, hpEq⟩ := Finset.mem_image.mp hmaxMem
  refine ⟨p.1, p.2.1, p.2.2, hp, ?_⟩
  rw [gmAffineJ, dif_pos hS]
  exact hpEq

/-- The finite affine sum is nonnegative when the source function is. -/
theorem gmAffineTransformSum_nonneg
    {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (M₁ M₂ M₃ : ℕ) (u : ℝ) :
    0 ≤ gmAffineTransformSum f M₁ M₂ M₃ u := by
  unfold gmAffineTransformSum gmAffineTerm
  apply Finset.sum_nonneg
  intro m₁ hm₁
  apply Finset.sum_nonneg
  intro m₂ hm₂
  apply Finset.sum_nonneg
  intro m₃ hm₃
  exact hf _

/-- Continuity of the exact finite affine sum. -/
theorem continuous_gmAffineTransformSum
    {f : ℝ → ℝ} (hf : Continuous f) (M₁ M₂ M₃ : ℕ) :
    Continuous (gmAffineTransformSum f M₁ M₂ M₃) := by
  unfold gmAffineTransformSum gmAffineTerm
  fun_prop

/-- Measurability needed for the Section 9 Plancherel calculation. -/
theorem stronglyMeasurable_gmAffineTransformSum
    {f : ℝ → ℝ} (hf : Continuous f) (M₁ M₂ M₃ : ℕ) :
    StronglyMeasurable (gmAffineTransformSum f M₁ M₂ M₃) :=
  (continuous_gmAffineTransformSum hf M₁ M₂ M₃).stronglyMeasurable

/-- Exact affine change of variables for one squared summand. -/
theorem integral_gmAffineTerm_sq
    (f : ℝ → ℝ) {m₁ m₂ m₃ : ℤ} (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) :
    (∫ u : ℝ, gmAffineTerm f m₁ m₂ m₃ u ^ 2) =
      |(m₂ : ℝ) / (m₁ : ℝ)| * ∫ x : ℝ, f x ^ 2 := by
  let g : ℝ → ℝ := fun x => f x ^ 2
  let a : ℝ := (m₁ : ℝ) / (m₂ : ℝ)
  let b : ℝ := (m₃ : ℝ) / (m₂ : ℝ)
  have ha : a ≠ 0 := div_ne_zero (by exact_mod_cast hm₁) (by exact_mod_cast hm₂)
  have hform : ∀ u : ℝ,
      gmAffineTerm f m₁ m₂ m₃ u ^ 2 = g (a * u + b) := by
    intro u
    dsimp only [gmAffineTerm, g, a, b]
    congr 2
    field_simp [show (m₂ : ℝ) ≠ 0 by exact_mod_cast hm₂]
  simp_rw [hform]
  calc
    (∫ u : ℝ, g (a * u + b)) =
        |a⁻¹| * ∫ y : ℝ, g (y + b) := by
      simpa only [Function.comp_apply] using
        (MeasureTheory.Measure.integral_comp_mul_left
          (fun y : ℝ => g (y + b)) a)
    _ = |a⁻¹| * ∫ y : ℝ, g y := by
      rw [integral_add_right_eq_self]
    _ = |(m₂ : ℝ) / (m₁ : ℝ)| * ∫ x : ℝ, f x ^ 2 := by
      dsimp only [a, g]
      rw [inv_div]

/-- Integrability of one squared affine summand, obtained from the exact
translation and nonzero-dilation invariance of Lebesgue measure. -/
theorem integrable_gmAffineTerm_sq
    {f : ℝ → ℝ} (hf₂ : Integrable fun x : ℝ => f x ^ 2)
    {m₁ m₂ m₃ : ℤ} (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) :
    Integrable fun u : ℝ => gmAffineTerm f m₁ m₂ m₃ u ^ 2 := by
  let g : ℝ → ℝ := fun x => f x ^ 2
  let a : ℝ := (m₁ : ℝ) / (m₂ : ℝ)
  let b : ℝ := (m₃ : ℝ) / (m₂ : ℝ)
  have ha : a ≠ 0 := div_ne_zero (by exact_mod_cast hm₁) (by exact_mod_cast hm₂)
  have hg : Integrable g := hf₂
  have hga : Integrable fun u : ℝ => g (a * u + b) :=
    (hg.comp_add_right b).comp_mul_left' ha
  convert hga using 1
  ext u
  dsimp only [gmAffineTerm, g, a, b]
  congr 2
  field_simp [show (m₂ : ℝ) ≠ 0 by exact_mod_cast hm₂]

/-- Cauchy--Schwarz for the exact finite affine family. -/
theorem gmAffineTransformSum_sq_le
    (f : ℝ → ℝ) (M₁ M₂ M₃ : ℕ) (u : ℝ) :
    gmAffineTransformSum f M₁ M₂ M₃ u ^ 2 ≤
      (gmAffineIndexSet M₁ M₂ M₃).card *
        ∑ p ∈ gmAffineIndexSet M₁ M₂ M₃,
          gmAffineTerm f p.1 p.2.1 p.2.2 u ^ 2 := by
  rw [gmAffineTransformSum_eq_indexSum]
  exact sq_sum_le_card_mul_sum_sq

/-- The integrated finite Cauchy--Schwarz inequality.  This is the exact
crude estimate from which the Section 9 exponent iteration starts. -/
theorem gmAffineTransformIntegral_le_indexSum
    {f : ℝ → ℝ} (hf₂ : Integrable fun x : ℝ => f x ^ 2)
    {M₁ M₂ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    gmAffineTransformIntegral f M₁ M₂ M₃ ≤
      (gmAffineIndexSet M₁ M₂ M₃).card *
        ∑ p ∈ gmAffineIndexSet M₁ M₂ M₃,
          (|(p.2.1 : ℝ) / (p.1 : ℝ)| * ∫ x : ℝ, f x ^ 2) := by
  let S := gmAffineIndexSet M₁ M₂ M₃
  have hint : Integrable fun u : ℝ =>
      (S.card : ℝ) * ∑ p ∈ S, gmAffineTerm f p.1 p.2.1 p.2.2 u ^ 2 := by
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro p hp
    exact integrable_gmAffineTerm_sq hf₂
      (gmAffineSignedShell_ne_zero hM₁ (mem_gmAffineIndexSet.mp hp).1)
      (gmAffinePositiveShell_ne_zero hM₂ (mem_gmAffineIndexSet.mp hp).2.1)
  calc
    gmAffineTransformIntegral f M₁ M₂ M₃ =
        ∫ u : ℝ, gmAffineTransformSum f M₁ M₂ M₃ u ^ 2 := rfl
    _ ≤ ∫ u : ℝ, (S.card : ℝ) *
          ∑ p ∈ S, gmAffineTerm f p.1 p.2.1 p.2.2 u ^ 2 := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) hint
      exact Eventually.of_forall fun u => gmAffineTransformSum_sq_le f M₁ M₂ M₃ u
    _ = (gmAffineIndexSet M₁ M₂ M₃).card *
          ∑ p ∈ gmAffineIndexSet M₁ M₂ M₃,
            (|(p.2.1 : ℝ) / (p.1 : ℝ)| * ∫ x : ℝ, f x ^ 2) := by
      dsimp only [S]
      rw [integral_const_mul]
      rw [integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro p hp
        exact integral_gmAffineTerm_sq f
          (gmAffineSignedShell_ne_zero hM₁ (mem_gmAffineIndexSet.mp hp).1)
          (gmAffinePositiveShell_ne_zero hM₂ (mem_gmAffineIndexSet.mp hp).2.1)
      · intro p hp
        exact integrable_gmAffineTerm_sq hf₂
          (gmAffineSignedShell_ne_zero hM₁ (mem_gmAffineIndexSet.mp hp).1)
          (gmAffinePositiveShell_ne_zero hM₂ (mem_gmAffineIndexSet.mp hp).2.1)

theorem card_gmAffinePositiveShell (M : ℕ) :
    (gmAffinePositiveShell M).card = M + 1 := by
  rw [gmAffinePositiveShell, Int.card_Icc]
  have hcast : (((2 * (M : ℤ) + 1 - (M : ℤ)).toNat : ℕ) : ℤ) =
      2 * (M : ℤ) + 1 - (M : ℤ) := Int.toNat_of_nonneg (by omega)
  omega

theorem card_gmAffineCentralShell (M : ℕ) :
    (gmAffineCentralShell M).card = 16 * M + 1 := by
  rw [gmAffineCentralShell, Int.card_Icc]
  change ((8 * (M : ℤ)) + 1 - (-(8 * (M : ℤ)))).toNat = 16 * M + 1
  have hcast : ((((8 * (M : ℤ)) + 1 - (-(8 * (M : ℤ)))).toNat : ℕ) : ℤ) =
      (8 * (M : ℤ)) + 1 - (-(8 * (M : ℤ))) := Int.toNat_of_nonneg (by omega)
  omega

theorem card_gmAffineSignedShell_le (M : ℕ) :
    (gmAffineSignedShell M).card ≤ 2 * (M + 1) := by
  rw [gmAffineSignedShell]
  calc
    ((Finset.Icc (-(2 * M : ℕ) : ℤ) (-(M : ℕ) : ℤ)) ∪
        Finset.Icc (M : ℤ) (2 * M : ℤ)).card ≤
        (Finset.Icc (-(2 * M : ℕ) : ℤ) (-(M : ℕ) : ℤ)).card +
          (Finset.Icc (M : ℤ) (2 * M : ℤ)).card := Finset.card_union_le _ _
    _ = 2 * (M + 1) := by
      simp [Int.card_Icc]
      omega

theorem card_gmAffineIndexSet_le (M₁ M₂ M₃ : ℕ) :
    (gmAffineIndexSet M₁ M₂ M₃).card ≤
      (2 * (M₁ + 1)) * (M₂ + 1) * (16 * M₃ + 1) := by
  rw [gmAffineIndexSet]
  rw [show ((gmAffineSignedShell M₁).product
      ((gmAffinePositiveShell M₂).product (gmAffineCentralShell M₃))).card =
      (gmAffineSignedShell M₁).card *
        ((gmAffinePositiveShell M₂).product (gmAffineCentralShell M₃)).card from
    Finset.card_product _ _]
  rw [show ((gmAffinePositiveShell M₂).product (gmAffineCentralShell M₃)).card =
      (gmAffinePositiveShell M₂).card * (gmAffineCentralShell M₃).card from
    Finset.card_product _ _]
  rw [card_gmAffinePositiveShell, card_gmAffineCentralShell]
  simpa only [mul_assoc] using Nat.mul_le_mul_right (16 * M₃ + 1)
    (Nat.mul_le_mul_right (M₂ + 1) (card_gmAffineSignedShell_le M₁))

theorem gmAffineSignedShell_scale_le_abs
    {M : ℕ} {m : ℤ} (hm : m ∈ gmAffineSignedShell M) :
    (M : ℝ) ≤ |(m : ℝ)| := by
  rcases mem_gmAffineSignedShell.mp hm with hmneg | hmpos
  · rw [abs_of_nonpos]
    · have hInt : (M : ℤ) ≤ -m := by omega
      exact_mod_cast hInt
    · exact_mod_cast (hmneg.2.trans (neg_nonpos.mpr (Int.natCast_nonneg M)))
  · rw [abs_of_nonneg]
    · exact_mod_cast hmpos.1
    · exact_mod_cast (Int.natCast_nonneg M |>.trans hmpos.1)

theorem abs_gmAffinePositiveShell_le_scale
    {M : ℕ} {m : ℤ} (hm : m ∈ gmAffinePositiveShell M) :
    |(m : ℝ)| ≤ 2 * M := by
  rcases mem_gmAffinePositiveShell.mp hm with ⟨hmLower, hmUpper⟩
  rw [abs_of_nonneg]
  · exact_mod_cast hmUpper
  · exact_mod_cast (Int.natCast_nonneg M |>.trans hmLower)

theorem abs_gmAffineSignedShell_le_scale
    {M : ℕ} {m : ℤ} (hm : m ∈ gmAffineSignedShell M) :
    |(m : ℝ)| ≤ 2 * M := by
  rcases mem_gmAffineSignedShell.mp hm with hmneg | hmpos
  · rw [abs_of_nonpos]
    · have hInt : -m ≤ (2 * M : ℤ) := by omega
      exact_mod_cast hInt
    · exact_mod_cast (hmneg.2.trans (neg_nonpos.mpr (Int.natCast_nonneg M)))
  · rw [abs_of_nonneg]
    · exact_mod_cast hmpos.2
    · exact_mod_cast (Int.natCast_nonneg M |>.trans hmpos.1)

theorem gmAffinePositiveShell_scale_le_abs
    {M : ℕ} {m : ℤ} (hm : m ∈ gmAffinePositiveShell M) :
    (M : ℝ) ≤ |(m : ℝ)| := by
  rcases mem_gmAffinePositiveShell.mp hm with ⟨hmLower, hmUpper⟩
  rw [abs_of_nonneg]
  · exact_mod_cast hmLower
  · exact_mod_cast (Int.natCast_nonneg M |>.trans hmLower)

/-- The denominator shell cancels the apparent extra factor in the crude
Cauchy bound, giving precisely the scale ratio used in Section 9. -/
theorem abs_affine_ratio_le
    {M₁ M₂ : ℕ} (hM₁ : 0 < M₁) {m₁ m₂ : ℤ}
    (hm₁ : m₁ ∈ gmAffineSignedShell M₁)
    (hm₂ : m₂ ∈ gmAffinePositiveShell M₂) :
    |(m₂ : ℝ) / (m₁ : ℝ)| ≤ (2 * M₂ : ℝ) / M₁ := by
  rw [abs_div]
  have hscalePos : (0 : ℝ) < M₁ := by exact_mod_cast hM₁
  exact div_le_div₀ (by positivity) (abs_gmAffinePositiveShell_le_scale hm₂)
    hscalePos (gmAffineSignedShell_scale_le_abs hm₁)

/-- The complementary lower scale ratio used to transfer Fourier decay
from `f` to every affine summand. -/
theorem affine_ratio_lower_bound
    {M₁ M₂ : ℕ} (hM₁ : 0 < M₁) {m₁ m₂ : ℤ}
    (hm₁ : m₁ ∈ gmAffineSignedShell M₁)
    (hm₂ : m₂ ∈ gmAffinePositiveShell M₂) :
    (M₂ : ℝ) / (2 * M₁) ≤ |(m₂ : ℝ) / (m₁ : ℝ)| := by
  rw [abs_div]
  have hden : 0 < (2 * M₁ : ℝ) := by positivity
  have hm₁pos : 0 < |(m₁ : ℝ)| := abs_pos.mpr (by
    exact_mod_cast gmAffineSignedShell_ne_zero hM₁ hm₁)
  rw [div_le_div_iff₀ hden hm₁pos]
  have hnum := gmAffinePositiveShell_scale_le_abs hm₂
  have hdenUpper := abs_gmAffineSignedShell_le_scale hm₁
  nlinarith only [hnum, hdenUpper, abs_nonneg (m₂ : ℝ),
    abs_nonneg (m₁ : ℝ)]

/-- Quantitative Fourier decay after the affine scale change.  The
denominator records the exact lower shell ratio rather than hiding it in
Vinogradov notation. -/
theorem norm_fourier_gmAffineComplexify_affine_le
    (n : ℕ) (f : SchwartzMap ℝ ℝ)
    {M₁ M₂ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    {m₁ m₂ : ℤ} (hm₁ : m₁ ∈ gmAffineSignedShell M₁)
    (hm₂ : m₂ ∈ gmAffinePositiveShell M₂)
    {xi : ℝ} (hxi : xi ≠ 0) :
    ‖fourier (gmAffineComplexify f)
        (((m₂ : ℝ) / (m₁ : ℝ)) * xi)‖ ≤
      SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) /
        (((M₂ : ℝ) / (2 * M₁)) * |xi|) ^ n := by
  have hc : 0 < (M₂ : ℝ) / (2 * M₁) := by positivity
  have hxiAbs : 0 < |xi| := abs_pos.mpr hxi
  have hfreq :
      ((M₂ : ℝ) / (2 * M₁)) * |xi| ≤
        |(m₂ : ℝ) / (m₁ : ℝ)| * |xi| := by
    exact mul_le_mul_of_nonneg_right
      (affine_ratio_lower_bound hM₁ hm₁ hm₂) (abs_nonneg xi)
  have hdecay := SchwartzMap.le_seminorm' ℝ n 0
    (fourier (gmAffineComplexify f))
      (((m₂ : ℝ) / (m₁ : ℝ)) * xi)
  rw [iteratedDeriv_zero, abs_mul] at hdecay
  have hpow :
      (((M₂ : ℝ) / (2 * M₁)) * |xi|) ^ n ≤
        (|(m₂ : ℝ) / (m₁ : ℝ)| * |xi|) ^ n := by
    gcongr
  have hweighted :
      (((M₂ : ℝ) / (2 * M₁)) * |xi|) ^ n *
          ‖fourier (gmAffineComplexify f)
            (((m₂ : ℝ) / (m₁ : ℝ)) * xi)‖ ≤
        SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans hdecay
  rw [le_div_iff₀ (pow_pos (mul_pos hc hxiAbs) n)]
  simpa only [mul_comm] using hweighted

theorem norm_gmAffineCentralPoissonKernel_le
    {M : ℕ} (hM : 0 < M) (y : ℝ) :
    ‖gmAffineCentralPoissonKernel M hM y‖ ≤
      (8 * M : ℝ) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual := by
  simpa using gmAffineCentralPoissonKernel_polynomial_decay 0 M hM y

theorem norm_sum_gmAffineCentralPoissonKernel_near_le
    {M : ℕ} (hM : 0 < M) (alpha Q : ℝ) :
    ‖∑ ell ∈ gmAffinePoissonNearSet M alpha Q,
        gmAffineCentralPoissonKernel M hM (alpha + ell)‖ ≤
      ((gmAffinePoissonNearSet M alpha Q).card : ℝ) *
        ((8 * M : ℝ) *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) := by
  calc
    ‖∑ ell ∈ gmAffinePoissonNearSet M alpha Q,
        gmAffineCentralPoissonKernel M hM (alpha + ell)‖ ≤
      ∑ ell ∈ gmAffinePoissonNearSet M alpha Q,
        ‖gmAffineCentralPoissonKernel M hM (alpha + ell)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ell ∈ gmAffinePoissonNearSet M alpha Q,
        ((8 * M : ℝ) *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact norm_gmAffineCentralPoissonKernel_le hM (alpha + ell)
    _ = ((gmAffinePoissonNearSet M alpha Q).card : ℝ) *
        ((8 * M : ℝ) *
          SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) := by
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Uniform bound for the retained part of (9.3), before the Region-I
choice `Q = T^η`. -/
theorem norm_gmAffinePoissonMainFourier_le
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 0 < Q) (xi : ℝ) :
    ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ ≤
      ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) *
        SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
        ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
          ((8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)) := by
  have hFourier (x : ℝ) :
      ‖fourier (gmAffineComplexify f) x‖ ≤
        SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) := by
    simpa using
      (SchwartzMap.le_seminorm' ℝ 0 0 (fourier (gmAffineComplexify f)) x)
  unfold gmAffinePoissonMainFourier
  calc
    ‖∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
            fourier (gmAffineComplexify f)
              (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
            (∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
              gmAffineCentralPoissonKernel M₃ hM₃
                (xi / (m₁ : ℝ) + ell))‖ ≤
        ∑ m₁ ∈ gmAffineSignedShell M₁,
          ‖∑ m₂ ∈ gmAffinePositiveShell M₂,
            (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
              fourier (gmAffineComplexify f)
                (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
              (∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
                gmAffineCentralPoissonKernel M₃ hM₃
                  (xi / (m₁ : ℝ) + ell))‖ := norm_sum_le _ _
    _ ≤ ∑ m₁ ∈ gmAffineSignedShell M₁,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            ‖(((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
              fourier (gmAffineComplexify f)
                (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
              (∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
                gmAffineCentralPoissonKernel M₃ hM₃
                  (xi / (m₁ : ℝ) + ell))‖ := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      exact norm_sum_le _ _
    _ ≤ ∑ _m₁ ∈ gmAffineSignedShell M₁,
          ∑ _m₂ ∈ gmAffinePositiveShell M₂,
            ((2 * M₂ : ℝ) / M₁) *
              SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
              ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
                ((8 * M₃ : ℝ) *
                  SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)) := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      apply Finset.sum_le_sum
      intro m₂ hm₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
      have hnear := norm_sum_gmAffineCentralPoissonKernel_near_le hM₃
        (xi / (m₁ : ℝ)) Q
      have hcard := card_gmAffinePoissonNearSet_real_le hM₃ hQ
        (alpha := xi / (m₁ : ℝ))
      have hkernelNonneg :
          0 ≤ (8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual := by positivity
      have hnear' :
          ‖∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
              gmAffineCentralPoissonKernel M₃ hM₃
                (xi / (m₁ : ℝ) + ell)‖ ≤
            (2 * (Q / (8 * M₃ : ℝ)) + 5) *
              ((8 * M₃ : ℝ) *
                SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual) :=
        hnear.trans (mul_le_mul_of_nonneg_right hcard hkernelNonneg)
      exact mul_le_mul
        (mul_le_mul (abs_affine_ratio_le hM₁ hm₁ hm₂)
          (hFourier (((m₂ : ℝ) / (m₁ : ℝ)) * xi))
          (norm_nonneg _) (by positivity))
        hnear' (norm_nonneg _) (by positivity)
    _ = ((gmAffineSignedShell M₁).card : ℝ) *
          ((gmAffinePositiveShell M₂).card : ℝ) *
          ((2 * M₂ : ℝ) / M₁) *
          SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
          ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
            ((8 * M₃ : ℝ) *
              SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Uniform pointwise estimate for the complete omitted part of (9.3).
The two finite shell cardinalities and the exact scale ratio remain
visible; the last factor is the absolutely summable Poisson tail. -/
theorem norm_gmAffinePoissonFarFourier_le
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 0 < Q) (xi : ℝ) :
    ‖gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q xi‖ ≤
      ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) *
        SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
        ((4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
              Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
          2 * ((8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
              Q ^ (n + 2))) := by
  have hFourier (x : ℝ) :
      ‖fourier (gmAffineComplexify f) x‖ ≤
        SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) := by
    simpa using
      (SchwartzMap.le_seminorm' ℝ 0 0 (fourier (gmAffineComplexify f)) x)
  have htail (alpha : ℝ) :
      ‖gmAffinePoissonFarSeries M₃ hM₃ alpha Q‖ ≤
        (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
              Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
          2 * ((8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
              Q ^ (n + 2)) :=
    norm_gmAffinePoissonFarSeries_le n hM₃ hQ
  unfold gmAffinePoissonFarFourier
  calc
    ‖∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
            fourier (gmAffineComplexify f)
              (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
            gmAffinePoissonFarSeries M₃ hM₃ (xi / (m₁ : ℝ)) Q‖ ≤
        ∑ m₁ ∈ gmAffineSignedShell M₁,
          ‖∑ m₂ ∈ gmAffinePositiveShell M₂,
            (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
              fourier (gmAffineComplexify f)
                (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
              gmAffinePoissonFarSeries M₃ hM₃ (xi / (m₁ : ℝ)) Q‖ := by
      exact norm_sum_le _ _
    _ ≤
        ∑ m₁ ∈ gmAffineSignedShell M₁,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            ‖(((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
              fourier (gmAffineComplexify f)
                (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
              gmAffinePoissonFarSeries M₃ hM₃ (xi / (m₁ : ℝ)) Q‖ := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      exact norm_sum_le _ _
    _ ≤ ∑ _m₁ ∈ gmAffineSignedShell M₁,
          ∑ _m₂ ∈ gmAffinePositiveShell M₂,
            ((2 * M₂ : ℝ) / M₁) *
              SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
              ((4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
                    Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
                2 * ((8 * M₃ : ℝ) *
                  SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
                    Q ^ (n + 2))) := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      apply Finset.sum_le_sum
      intro m₂ hm₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_abs]
      exact mul_le_mul
        (mul_le_mul (abs_affine_ratio_le hM₁ hm₁ hm₂)
          (hFourier (((m₂ : ℝ) / (m₁ : ℝ)) * xi))
          (norm_nonneg _) (by positivity))
        (htail (xi / (m₁ : ℝ))) (norm_nonneg _) (by positivity)
    _ = ((gmAffineSignedShell M₁).card : ℝ) *
          ((gmAffinePositiveShell M₂).card : ℝ) *
          ((2 * M₂ : ℝ) / M₁) *
          SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
          ((4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
                Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
            2 * ((8 * M₃ : ℝ) *
              SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
                Q ^ (n + 2))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The uniform retained-mode envelope appearing in the Region-I bound. -/
noncomputable def gmAffinePoissonMainEnvelope
    (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (Q : ℝ) : ℝ :=
  ((gmAffineSignedShell M₁).card : ℝ) *
    ((gmAffinePositiveShell M₂).card : ℝ) *
    ((2 * M₂ : ℝ) / M₁) *
    SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
    ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
      ((8 * M₃ : ℝ) *
        SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual))

/-- The uniform complete omitted-frequency envelope in (9.3). -/
noncomputable def gmAffinePoissonFarEnvelope
    (n : ℕ) (f : SchwartzMap ℝ ℝ) (M₁ M₂ M₃ : ℕ) (Q : ℝ) : ℝ :=
  ((gmAffineSignedShell M₁).card : ℝ) *
    ((gmAffinePositiveShell M₂).card : ℝ) *
    ((2 * M₂ : ℝ) / M₁) *
    SchwartzMap.seminorm ℝ 0 0 (fourier (gmAffineComplexify f)) *
    ((4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
      2 * ((8 * M₃ : ℝ) *
        SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ (n + 2)))

/-- The retained Fourier sum with an arbitrary uniform bound for the
scaled transform of `f`.  This is the reusable form needed in Region III,
where the bound carries a negative power of `|xi|`. -/
theorem norm_gmAffinePoissonMainFourier_le_of_fourier_le
    (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q D xi : ℝ} (hQ : 0 < Q)
    (hD : ∀ m₁ ∈ gmAffineSignedShell M₁,
      ∀ m₂ ∈ gmAffinePositiveShell M₂,
        ‖fourier (gmAffineComplexify f)
          (((m₂ : ℝ) / (m₁ : ℝ)) * xi)‖ ≤ D) :
    ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ ≤
      ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) * D *
        ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
          ((8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)) := by
  unfold gmAffinePoissonMainFourier
  calc
    ‖∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
            fourier (gmAffineComplexify f)
              (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
            (∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
              gmAffineCentralPoissonKernel M₃ hM₃
                (xi / (m₁ : ℝ) + ell))‖ ≤
        ∑ m₁ ∈ gmAffineSignedShell M₁,
          ‖∑ m₂ ∈ gmAffinePositiveShell M₂,
            (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
              fourier (gmAffineComplexify f)
                (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
              (∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
                gmAffineCentralPoissonKernel M₃ hM₃
                  (xi / (m₁ : ℝ) + ell))‖ := norm_sum_le _ _
    _ ≤ ∑ m₁ ∈ gmAffineSignedShell M₁,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            ‖(((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
              fourier (gmAffineComplexify f)
                (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
              (∑ ell ∈ gmAffinePoissonNearSet M₃ (xi / (m₁ : ℝ)) Q,
                gmAffineCentralPoissonKernel M₃ hM₃
                  (xi / (m₁ : ℝ) + ell))‖ := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      exact norm_sum_le _ _
    _ ≤ ∑ _m₁ ∈ gmAffineSignedShell M₁,
          ∑ _m₂ ∈ gmAffinePositiveShell M₂,
            ((2 * M₂ : ℝ) / M₁) * D *
              ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
                ((8 * M₃ : ℝ) *
                  SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)) := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      apply Finset.sum_le_sum
      intro m₂ hm₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
      have hnear := norm_sum_gmAffineCentralPoissonKernel_near_le hM₃
        (xi / (m₁ : ℝ)) Q
      have hcard := card_gmAffinePoissonNearSet_real_le hM₃ hQ
        (alpha := xi / (m₁ : ℝ))
      have hkernelNonneg :
          0 ≤ (8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual := by positivity
      have hnear' := hnear.trans
        (mul_le_mul_of_nonneg_right hcard hkernelNonneg)
      exact mul_le_mul
        (mul_le_mul (abs_affine_ratio_le hM₁ hm₁ hm₂)
          (hD m₁ hm₁ m₂ hm₂) (norm_nonneg _) (by positivity))
        hnear' (norm_nonneg _) (mul_nonneg (by positivity)
          ((norm_nonneg _).trans (hD m₁ hm₁ m₂ hm₂)))
    _ = ((gmAffineSignedShell M₁).card : ℝ) *
          ((gmAffinePositiveShell M₂).card : ℝ) *
          ((2 * M₂ : ℝ) / M₁) * D *
          ((2 * (Q / (8 * M₃ : ℝ)) + 5) *
            ((8 * M₃ : ℝ) *
              SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The omitted Fourier sum with the same arbitrary uniform bound for the
scaled transform of `f`. -/
theorem norm_gmAffinePoissonFarFourier_le_of_fourier_le
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q D xi : ℝ} (hQ : 0 < Q)
    (hD : ∀ m₁ ∈ gmAffineSignedShell M₁,
      ∀ m₂ ∈ gmAffinePositiveShell M₂,
        ‖fourier (gmAffineComplexify f)
          (((m₂ : ℝ) / (m₁ : ℝ)) * xi)‖ ≤ D) :
    ‖gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q xi‖ ≤
      ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) * D *
        ((4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
              Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
          2 * ((8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
              Q ^ (n + 2))) := by
  have htail (alpha : ℝ) :
      ‖gmAffinePoissonFarSeries M₃ hM₃ alpha Q‖ ≤
        (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
              Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
          2 * ((8 * M₃ : ℝ) *
            SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
              Q ^ (n + 2)) :=
    norm_gmAffinePoissonFarSeries_le n hM₃ hQ
  unfold gmAffinePoissonFarFourier
  calc
    ‖∑ m₁ ∈ gmAffineSignedShell M₁,
        ∑ m₂ ∈ gmAffinePositiveShell M₂,
          (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
            fourier (gmAffineComplexify f)
              (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
            gmAffinePoissonFarSeries M₃ hM₃ (xi / (m₁ : ℝ)) Q‖ ≤
        ∑ m₁ ∈ gmAffineSignedShell M₁,
          ‖∑ m₂ ∈ gmAffinePositiveShell M₂,
            (((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
              fourier (gmAffineComplexify f)
                (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
              gmAffinePoissonFarSeries M₃ hM₃ (xi / (m₁ : ℝ)) Q‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m₁ ∈ gmAffineSignedShell M₁,
          ∑ m₂ ∈ gmAffinePositiveShell M₂,
            ‖(((|(m₂ : ℝ) / (m₁ : ℝ)| : ℝ) : ℂ) *
              fourier (gmAffineComplexify f)
                (((m₂ : ℝ) / (m₁ : ℝ)) * xi)) *
              gmAffinePoissonFarSeries M₃ hM₃ (xi / (m₁ : ℝ)) Q‖ := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      exact norm_sum_le _ _
    _ ≤ ∑ _m₁ ∈ gmAffineSignedShell M₁,
          ∑ _m₂ ∈ gmAffinePositiveShell M₂,
            ((2 * M₂ : ℝ) / M₁) * D *
              ((4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
                    Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
                2 * ((8 * M₃ : ℝ) *
                  SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
                    Q ^ (n + 2))) := by
      apply Finset.sum_le_sum
      intro m₁ hm₁
      apply Finset.sum_le_sum
      intro m₂ hm₂
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
      exact mul_le_mul
        (mul_le_mul (abs_affine_ratio_le hM₁ hm₁ hm₂)
          (hD m₁ hm₁ m₂ hm₂) (norm_nonneg _) (by positivity))
        (htail (xi / (m₁ : ℝ))) (norm_nonneg _)
        (mul_nonneg (by positivity)
          ((norm_nonneg _).trans (hD m₁ hm₁ m₂ hm₂)))
    _ = ((gmAffineSignedShell M₁).card : ℝ) *
          ((gmAffinePositiveShell M₂).card : ℝ) *
          ((2 * M₂ : ℝ) / M₁) * D *
          ((4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
                Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
            2 * ((8 * M₃ : ℝ) *
              SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
                Q ^ (n + 2))) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

noncomputable def gmAffinePoissonNearKernelEnvelope
    (M : ℕ) (Q : ℝ) : ℝ :=
  (2 * (Q / (8 * M : ℝ)) + 5) *
    ((8 * M : ℝ) * SchwartzMap.seminorm ℝ 0 0 gmAffineLocalBumpDual)

noncomputable def gmAffinePoissonTailKernelEnvelope
    (n M : ℕ) (Q : ℝ) : ℝ :=
  (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
      Q ^ n) * (∑' j : ℤ, gmIntDecayProfile 2 j) +
    2 * ((8 * M : ℝ) *
      SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        Q ^ (n + 2))

theorem gmAffinePoissonNearKernelEnvelope_nonneg
    {M : ℕ} (hM : 0 < M) {Q : ℝ} (hQ : 0 < Q) :
    0 ≤ gmAffinePoissonNearKernelEnvelope M Q := by
  unfold gmAffinePoissonNearKernelEnvelope
  positivity

theorem gmAffinePoissonTailKernelEnvelope_nonneg
    (n : ℕ) {M : ℕ} (hM : 0 < M) {Q : ℝ} (hQ : 0 < Q) :
    0 ≤ gmAffinePoissonTailKernelEnvelope n M Q := by
  have hprofile : 0 ≤ ∑' j : ℤ, gmIntDecayProfile 2 j := by
    apply tsum_nonneg
    intro j
    unfold gmIntDecayProfile
    split_ifs <;> positivity
  unfold gmAffinePoissonTailKernelEnvelope
  positivity

/-- The coefficient of `|xi|^{-n}` in the Region-III estimate. -/
noncomputable def gmAffineFourierDecayEnvelope
    (n : ℕ) (f : SchwartzMap ℝ ℝ)
    (M₁ M₂ M₃ : ℕ) (Q : ℝ) : ℝ :=
  (((gmAffineSignedShell M₁).card : ℝ) *
      ((gmAffinePositiveShell M₂).card : ℝ) *
      ((2 * M₂ : ℝ) / M₁)) *
    (SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) /
      ((M₂ : ℝ) / (2 * M₁)) ^ n) *
    (gmAffinePoissonNearKernelEnvelope M₃ Q +
      gmAffinePoissonTailKernelEnvelope n M₃ Q)

theorem gmAffineFourierDecayEnvelope_nonneg
    (n : ℕ) (f : SchwartzMap ℝ ℝ)
    {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 0 < Q) :
    0 ≤ gmAffineFourierDecayEnvelope n f M₁ M₂ M₃ Q := by
  unfold gmAffineFourierDecayEnvelope
  have hc : 0 < (M₂ : ℝ) / (2 * M₁) := by positivity
  have hnear := gmAffinePoissonNearKernelEnvelope_nonneg hM₃ hQ
  have htail := gmAffinePoissonTailKernelEnvelope_nonneg n hM₃ hQ
  positivity

/-- Arbitrary-order Region-III pointwise decay obtained from the complete
Poisson identity and the source Fourier decay of `f`. -/
theorem norm_gmAffineSmoothTransformSchwartz_fourier_decay
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) (hxi : xi ≠ 0) :
    ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ≤
      ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) *
        (SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) /
          (((M₂ : ℝ) / (2 * M₁)) * |xi|) ^ n) *
        (gmAffinePoissonNearKernelEnvelope M₃ Q +
          gmAffinePoissonTailKernelEnvelope n M₃ Q) := by
  let D : ℝ :=
    SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) /
      (((M₂ : ℝ) / (2 * M₁)) * |xi|) ^ n
  have hD : ∀ m₁ ∈ gmAffineSignedShell M₁,
      ∀ m₂ ∈ gmAffinePositiveShell M₂,
        ‖fourier (gmAffineComplexify f)
          (((m₂ : ℝ) / (m₁ : ℝ)) * xi)‖ ≤ D := by
    intro m₁ hm₁ m₂ hm₂
    exact norm_fourier_gmAffineComplexify_affine_le
      n f hM₁ hM₂ hm₁ hm₂ hxi
  rw [gmAffineSmoothTransformSchwartz_fourier_eq_main_add_far
    n f hM₁ hM₂ hM₃ hQ xi]
  refine (norm_add_le _ _).trans ?_
  have hmain := norm_gmAffinePoissonMainFourier_le_of_fourier_le
    f hM₁ hM₂ hM₃ hQ hD
  have hfar := norm_gmAffinePoissonFarFourier_le_of_fourier_le
    n f hM₁ hM₂ hM₃ hQ hD
  calc
    ‖gmAffinePoissonMainFourier f M₁ M₂ M₃ hM₃ Q xi‖ +
        ‖gmAffinePoissonFarFourier f M₁ M₂ M₃ hM₃ Q xi‖ ≤
      (((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) * D *
        gmAffinePoissonNearKernelEnvelope M₃ Q) +
      (((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) * D *
        gmAffinePoissonTailKernelEnvelope n M₃ Q) := by
        exact add_le_add (by simpa only [gmAffinePoissonNearKernelEnvelope] using hmain)
          (by simpa only [gmAffinePoissonTailKernelEnvelope] using hfar)
    _ = ((gmAffineSignedShell M₁).card : ℝ) *
        ((gmAffinePositiveShell M₂).card : ℝ) *
        ((2 * M₂ : ℝ) / M₁) *
        (SchwartzMap.seminorm ℝ n 0 (fourier (gmAffineComplexify f)) /
          (((M₂ : ℝ) / (2 * M₁)) * |xi|) ^ n) *
        (gmAffinePoissonNearKernelEnvelope M₃ Q +
          gmAffinePoissonTailKernelEnvelope n M₃ Q) := by
      dsimp only [D]
      ring

theorem norm_gmAffineSmoothTransformSchwartz_fourier_le_decayEnvelope
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q xi : ℝ} (hQ : 0 < Q) (hxi : xi ≠ 0) :
    ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ≤
      gmAffineFourierDecayEnvelope n f M₁ M₂ M₃ Q / |xi| ^ n := by
  have hdecay := norm_gmAffineSmoothTransformSchwartz_fourier_decay
    n f hM₁ hM₂ hM₃ hQ hxi
  have hc : (M₂ : ℝ) / (2 * M₁) ≠ 0 := by positivity
  have hxiAbs : |xi| ≠ 0 := abs_ne_zero.mpr hxi
  refine hdecay.trans_eq ?_
  unfold gmAffineFourierDecayEnvelope
  rw [mul_pow]
  field_simp

/-- Concrete Region-III estimate.  Taking `Y=T^6` and sufficiently large
`n` gives the `O(T^{-100})` contribution in equation (9.5). -/
theorem integral_gmAffineHighFrequencyRegion_fourier_sq_le
    (n : ℕ) (hn : 1 ≤ n) (f : SchwartzMap ℝ ℝ)
    {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q Y : ℝ} (hQ : 0 < Q) (hY : 0 < Y) :
    (∫ xi in gmAffineHighFrequencyRegion Y,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
      (gmAffineFourierDecayEnvelope n f M₁ M₂ M₃ Q) ^ 2 *
        (2 * (-Y ^ ((-(2 * (n : ℝ))) + 1) /
          ((-(2 * (n : ℝ))) + 1))) := by
  apply integral_gmAffineHighFrequencyRegion_sq_le hn hY
    (gmAffineFourierDecayEnvelope_nonneg n f hM₁ hM₂ hM₃ hQ)
  · exact (integrable_gmAffineSmoothTransform_fourier_sq
      f M₁ M₂ M₃).integrableOn
  · intro xi hxi
    have hxi0 : xi ≠ 0 := by
      intro hzero
      subst xi
      simp only [gmAffineHighFrequencyRegion, Set.mem_setOf_eq, abs_zero] at hxi
      exact (not_lt_of_ge hY.le) hxi
    exact norm_gmAffineSmoothTransformSchwartz_fourier_le_decayEnvelope
      n f hM₁ hM₂ hM₃ hQ hxi0

/-! ### The second Poisson summation in Region II -/

/-- A real-scale dilation of the fixed Section 9 cutoff. -/
noncomputable def gmAffineScaledBumpFunction (S : ℝ) (x : ℝ) : ℂ :=
  (gmCubicLocalBump (x / S) : ℂ)

theorem contDiff_gmAffineScaledBumpFunction (S : ℝ) :
    ContDiff ℝ ∞ (gmAffineScaledBumpFunction S) := by
  unfold gmAffineScaledBumpFunction gmCubicLocalBump
  apply Complex.ofRealCLM.contDiff.comp
  apply dfiUnitRedundantBump.contDiff.comp
  fun_prop

theorem hasCompactSupport_gmAffineScaledBumpFunction
    {S : ℝ} (hS : 0 < S) :
    HasCompactSupport (gmAffineScaledBumpFunction S) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-2 * S) (2 * S)))
  intro x hx
  have hxOutside : x < -2 * S ∨ 2 * S < x := by
    simpa only [Set.mem_Icc, not_and_or, not_le] using hx
  have habs : 2 ≤ |x / S| := by
    rw [abs_div, abs_of_pos hS, le_div_iff₀ hS]
    rcases hxOutside with hleft | hright
    · have hxneg : x < 0 := by linarith
      rw [abs_of_neg hxneg]
      linarith
    · have hxpos : 0 < x := (by positivity : 0 ≤ 2 * S).trans_lt hright
      rw [abs_of_pos hxpos]
      linarith
  simp only [gmAffineScaledBumpFunction,
    gmCubicLocalBump_eq_zero_of_two_le_abs habs, Complex.ofReal_zero]

noncomputable def gmAffineScaledBumpSchwartz
    (S : ℝ) (hS : 0 < S) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_gmAffineScaledBumpFunction hS).toSchwartzMap
    (contDiff_gmAffineScaledBumpFunction S)

@[simp]
theorem gmAffineScaledBumpSchwartz_apply
    (S : ℝ) (hS : 0 < S) (x : ℝ) :
    gmAffineScaledBumpSchwartz S hS x =
      (gmCubicLocalBump (x / S) : ℂ) := rfl

/-- The dual kernel for the second Poisson summation. -/
noncomputable def gmAffineScaledBumpDual
    (S : ℝ) (hS : 0 < S) : SchwartzMap ℝ ℂ :=
  fourierInv (gmAffineScaledBumpSchwartz S hS)

/-- Exact real-scale dilation of the dual kernel. -/
theorem gmAffineScaledBumpDual_eq_scaled
    (S : ℝ) (hS : 0 < S) (y : ℝ) :
    gmAffineScaledBumpDual S hS y =
      (S : ℂ) * gmAffineLocalBumpDual (S * y) := by
  rw [gmAffineScaledBumpDual, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  rw [gmAffineLocalBumpDual, SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  simp only [Real.inner_apply, smul_eq_mul, gmAffineScaledBumpSchwartz_apply,
    gmAffineLocalBumpSchwartz_apply]
  let q : ℝ → ℂ := fun z =>
    Complex.exp ((((2 * Real.pi * (z * (S * y)) : ℝ) : ℂ) * I)) *
      (gmCubicLocalBump z : ℂ)
  calc
    (∫ x : ℝ, Complex.exp ((((2 * Real.pi * (x * y) : ℝ) : ℂ) * I)) *
        (gmCubicLocalBump (x / S) : ℂ)) =
        ∫ x : ℝ, q (x / S) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [q]
      have hphase : (x / S) * (S * y) = x * y := by
        field_simp [hS.ne']
      rw [hphase]
    _ = S • ∫ z : ℝ, q z := by
      have hChange := Measure.integral_comp_div q S
      rw [abs_of_pos hS] at hChange
      exact hChange
    _ = (S : ℂ) * ∫ z : ℝ,
        Complex.exp ((((2 * Real.pi * (z * (S * y)) : ℝ) : ℂ) * I)) *
          (gmCubicLocalBump z : ℂ) := by
      change (S : ℂ) * ∫ z : ℝ, q z = _
      rfl

/-- Exact second Poisson formula in the paper's normalization
`S=T/M₂`. -/
theorem gmAffineScaledBump_poisson
    (S : ℝ) (hS : 0 < S) (alpha : ℝ) :
    (∑' ell : ℤ, (gmCubicLocalBump ((ell : ℝ) / S) : ℂ) *
        Complex.exp ((((2 * Real.pi * (ell : ℝ) * alpha : ℝ) : ℂ) * I))) =
      ∑' j : ℤ, gmAffineScaledBumpDual S hS (alpha + j) := by
  have hPoisson :=
    SchwartzMap.tsum_eq_tsum_fourier (gmAffineScaledBumpDual S hS) alpha
  rw [gmAffineScaledBumpDual, fourier_fourierInv_eq] at hPoisson
  rw [gmAffineScaledBumpDual]
  rw [hPoisson]
  apply tsum_congr
  intro ell
  simp only [gmAffineScaledBumpSchwartz_apply, _root_.fourier_coe_apply]
  congr 2
  push_cast
  ring

/-! ### The second Poisson formula in the middle-frequency region -/

/-- The affine displacement occurring in Guth--Maynard (9.7).  The sign is
chosen so that the source phase is `e(-ell * displacement)` and the dual
lattice is literally `j - displacement`, as in the paper. -/
def gmAffineMiddleDisplacement
    (m₂ m₂' : ℤ) (u u' : ℝ) : ℝ :=
  (m₂ : ℝ) * u - (m₂' : ℝ) * u'

/-- The `Z₂` lattice sum in equation (9.7), with the paper's smooth
frequency cutoff at scale `T/M₂`. -/
noncomputable def gmAffineMiddleZ₂
    (T : ℝ) (M₂ : ℕ) (m₂ m₂' : ℤ) (u u' : ℝ) : ℂ :=
  ∑' ell : ℤ,
    (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
      Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
        gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)

/-- Exact second Poisson summation for equation (9.7).  No frequency is
dropped: the right side is the complete integer dual lattice. -/
theorem gmAffineMiddleZ₂_poisson
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (m₂ m₂' : ℤ) (u u' : ℝ) :
    gmAffineMiddleZ₂ T M₂ m₂ m₂' u u' =
      ∑' j : ℤ, gmAffineScaledBumpDual (T / M₂) (by positivity)
        ((j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u') := by
  let S : ℝ := T / M₂
  have hS : 0 < S := by dsimp only [S]; positivity
  have hPoisson := gmAffineScaledBump_poisson S hS
    (-gmAffineMiddleDisplacement m₂ m₂' u u')
  unfold gmAffineMiddleZ₂
  calc
    (∑' ell : ℤ,
        (gmCubicLocalBump (((M₂ : ℝ) * (ell : ℝ)) / T) : ℂ) *
          Complex.exp (((-(2 * Real.pi * (ell : ℝ) *
            gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)) =
        ∑' ell : ℤ, (gmCubicLocalBump ((ell : ℝ) / S) : ℂ) *
          Complex.exp ((((2 * Real.pi * (ell : ℝ) *
            (-gmAffineMiddleDisplacement m₂ m₂' u u') : ℝ) : ℂ) * I)) := by
      apply tsum_congr
      intro ell
      congr 2
      · dsimp only [S]
        field_simp [hT.ne', show (M₂ : ℝ) ≠ 0 by positivity]
      · push_cast
        ring
    _ = ∑' j : ℤ, gmAffineScaledBumpDual S hS
          (-gmAffineMiddleDisplacement m₂ m₂' u u' + j) := hPoisson
    _ = ∑' j : ℤ, gmAffineScaledBumpDual (T / M₂) (by positivity)
          ((j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u') := by
      apply tsum_congr
      intro j
      congr 1
      ring

/-- The source cutoff is exactly a real-scale dilation; this is the algebra
which identifies the paper's `psi₂(M₂ ell/T)` with the Poisson scale
`S=T/M₂`. -/
theorem gmAffineMiddle_cutoff_eq_scaled
    {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    (ell : ℤ) :
    ((M₂ : ℝ) * (ell : ℝ)) / T = (ell : ℝ) / (T / M₂) := by
  have hM₂r : (M₂ : ℝ) ≠ 0 := by positivity
  field_simp [hT.ne', hM₂r]

/-- Arbitrary-order decay of the second-Poisson kernel, uniformly in its
positive real dilation. -/
theorem gmAffineScaledBumpDual_polynomial_decay
    (n : ℕ) {S : ℝ} (hS : 0 < S) (y : ℝ) :
    |S * y| ^ n * ‖gmAffineScaledBumpDual S hS y‖ ≤
      S * SchwartzMap.seminorm ℝ n 0 gmAffineLocalBumpDual := by
  rw [gmAffineScaledBumpDual_eq_scaled]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  have hdecay := gmAffineLocalBumpDual_polynomial_decay n (S * y)
  calc
    |S * y| ^ n *
        (S * ‖gmAffineLocalBumpDual (S * y)‖) =
        S * (|S * y| ^ n * ‖gmAffineLocalBumpDual (S * y)‖) := by ring
    _ ≤ S * SchwartzMap.seminorm ℝ n 0 gmAffineLocalBumpDual :=
      mul_le_mul_of_nonneg_left hdecay hS.le

/-- Exact finite dual window retained after the second Poisson summation. -/
noncomputable def gmAffineScaledNearSet
    (S alpha Q : ℝ) : Finset ℤ :=
  let R : ℤ := ⌈Q / S + 1⌉
  (Finset.Icc (-R - ⌊alpha⌋) (R - ⌊alpha⌋)).filter
    (fun j : ℤ => |S * (alpha + j)| < Q)

theorem mem_gmAffineScaledNearSet_of_lt
    {S : ℝ} (hS : 0 < S) {alpha Q : ℝ} {j : ℤ}
    (hnear : |S * (alpha + j)| < Q) :
    j ∈ gmAffineScaledNearSet S alpha Q := by
  let k : ℤ := j + ⌊alpha⌋
  let R : ℤ := ⌈Q / S + 1⌉
  have hy : alpha + (j : ℝ) = Int.fract alpha + (k : ℝ) := by
    simpa only [k] using add_int_eq_fract_add_translated alpha j
  have hyabs : |alpha + (j : ℝ)| < Q / S := by
    rw [abs_mul, abs_of_pos hS] at hnear
    exact (lt_div_iff₀ hS).mpr (by simpa only [mul_comm] using hnear)
  have hfractAbs : |Int.fract alpha| < 1 := by
    rw [abs_of_nonneg (Int.fract_nonneg alpha)]
    exact Int.fract_lt_one alpha
  have hkReal : |(k : ℝ)| < Q / S + 1 := by
    have hkEq : (k : ℝ) = (alpha + (j : ℝ)) - Int.fract alpha := by
      rw [hy]
      ring
    rw [hkEq]
    exact (abs_sub _ _).trans_lt (add_lt_add hyabs hfractAbs)
  have hkUpperReal : (k : ℝ) ≤ (R : ℝ) :=
    (le_abs_self (k : ℝ)).trans
      ((le_of_lt hkReal).trans (Int.le_ceil (Q / S + 1)))
  have hkLowerReal : -(R : ℝ) ≤ (k : ℝ) := by
    have hneg : -(R : ℝ) ≤ -|(k : ℝ)| :=
      neg_le_neg ((le_of_lt hkReal).trans (Int.le_ceil (Q / S + 1)))
    exact hneg.trans (neg_abs_le (k : ℝ))
  have hkUpper : k ≤ R := by exact_mod_cast hkUpperReal
  have hkLower : -R ≤ k := by exact_mod_cast hkLowerReal
  unfold gmAffineScaledNearSet
  dsimp only
  rw [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · dsimp only [R, k] at hkUpper hkLower ⊢
    constructor <;> omega
  · exact hnear

theorem card_gmAffineScaledNearSet_le
    (S alpha Q : ℝ) :
    (gmAffineScaledNearSet S alpha Q).card ≤
      (2 * ⌈Q / S + 1⌉ + 1).toNat := by
  let R : ℤ := ⌈Q / S + 1⌉
  calc
    (gmAffineScaledNearSet S alpha Q).card ≤
        (Finset.Icc (-R - ⌊alpha⌋) (R - ⌊alpha⌋)).card := by
      unfold gmAffineScaledNearSet
      dsimp only [R]
      exact Finset.card_filter_le _ _
    _ = (2 * R + 1).toNat := by
      rw [Int.card_Icc]
      congr 1
      ring

/-- The exact retained term for the second Poisson expansion. -/
noncomputable def gmAffineScaledNearTerm
    (S : ℝ) (hS : 0 < S) (alpha Q : ℝ) (j : ℤ) : ℂ :=
  if |S * (alpha + j)| < Q then
    gmAffineScaledBumpDual S hS (alpha + j)
  else 0

/-- The exact omitted term for the second Poisson expansion. -/
noncomputable def gmAffineScaledFarTerm
    (S : ℝ) (hS : 0 < S) (alpha Q : ℝ) (j : ℤ) : ℂ :=
  if Q ≤ |S * (alpha + j)| then
    gmAffineScaledBumpDual S hS (alpha + j)
  else 0

theorem gmAffineScaledBumpDual_eq_near_add_far
    {S : ℝ} (hS : 0 < S) (alpha Q : ℝ) (j : ℤ) :
    gmAffineScaledBumpDual S hS (alpha + j) =
      gmAffineScaledNearTerm S hS alpha Q j +
        gmAffineScaledFarTerm S hS alpha Q j := by
  unfold gmAffineScaledNearTerm gmAffineScaledFarTerm
  by_cases hnear : |S * (alpha + j)| < Q
  · rw [if_pos hnear, if_neg (not_le.mpr hnear)]
    simp
  · rw [if_neg hnear, if_pos (le_of_not_gt hnear)]
    simp

theorem gmAffineScaledNearTerm_eq_zero_of_not_mem
    {S : ℝ} (hS : 0 < S) {alpha Q : ℝ} {j : ℤ}
    (hj : j ∉ gmAffineScaledNearSet S alpha Q) :
    gmAffineScaledNearTerm S hS alpha Q j = 0 := by
  unfold gmAffineScaledNearTerm
  split_ifs with hnear
  · exact False.elim (hj (mem_gmAffineScaledNearSet_of_lt hS hnear))
  · rfl

theorem hasFiniteSupport_gmAffineScaledNearTerm
    {S : ℝ} (hS : 0 < S) (alpha Q : ℝ) :
    Function.HasFiniteSupport (gmAffineScaledNearTerm S hS alpha Q) := by
  apply Set.Finite.subset (gmAffineScaledNearSet S alpha Q).finite_toSet
  intro j hj
  simp only [Function.mem_support, ne_eq] at hj
  by_contra hmem
  exact hj (gmAffineScaledNearTerm_eq_zero_of_not_mem hS hmem)

theorem summable_gmAffineScaledNearTerm
    {S : ℝ} (hS : 0 < S) (alpha Q : ℝ) :
    Summable (gmAffineScaledNearTerm S hS alpha Q) :=
  summable_of_hasFiniteSupport
    (hasFiniteSupport_gmAffineScaledNearTerm hS alpha Q)

theorem tsum_gmAffineScaledNearTerm_eq_sum
    {S : ℝ} (hS : 0 < S) (alpha Q : ℝ) :
    (∑' j : ℤ, gmAffineScaledNearTerm S hS alpha Q j) =
      ∑ j ∈ gmAffineScaledNearSet S alpha Q,
        gmAffineScaledBumpDual S hS (alpha + j) := by
  rw [tsum_eq_sum (s := gmAffineScaledNearSet S alpha Q)]
  · apply Finset.sum_congr rfl
    intro j hj
    unfold gmAffineScaledNearTerm
    rw [if_pos (Finset.mem_filter.mp hj).2]
  · intro j hj
    exact gmAffineScaledNearTerm_eq_zero_of_not_mem hS hj

@[simp]
theorem norm_gmAffineScaledFarTerm
    (S : ℝ) (hS : 0 < S) (alpha Q : ℝ) (j : ℤ) :
    ‖gmAffineScaledFarTerm S hS alpha Q j‖ =
      if Q ≤ |S * (alpha + j)| then
        ‖gmAffineScaledBumpDual S hS (alpha + j)‖ else 0 := by
  unfold gmAffineScaledFarTerm
  split_ifs <;> simp

/-- A summable quadratic-profile majorant for the complete omitted lattice
after the second Poisson summation. -/
noncomputable def gmAffineScaledFarMajorant
    (n : ℕ) (S alpha Q : ℝ) (j : ℤ) : ℝ :=
  (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
      (S * Q ^ n)) *
      gmIntDecayProfile 2 (j + ⌊alpha⌋) +
    (if j + ⌊alpha⌋ = 0 then
      S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        Q ^ (n + 2) else 0) +
    (if j + ⌊alpha⌋ = -1 then
      S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        Q ^ (n + 2) else 0)

theorem norm_gmAffineScaledFarTerm_le_profile
    (n : ℕ) {S : ℝ} (hS : 0 < S)
    {alpha Q : ℝ} (hQ : 0 < Q) (j : ℤ)
    (hk0 : j + ⌊alpha⌋ ≠ 0) (hkneg : j + ⌊alpha⌋ ≠ -1) :
    ‖gmAffineScaledFarTerm S hS alpha Q j‖ ≤
      (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        (S * Q ^ n)) *
        gmIntDecayProfile 2 (j + ⌊alpha⌋) := by
  rw [norm_gmAffineScaledFarTerm]
  split_ifs with hfar
  · let k : ℤ := j + ⌊alpha⌋
    let C : ℝ := SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual
    have hy : alpha + (j : ℝ) = Int.fract alpha + (k : ℝ) := by
      simpa only [k] using add_int_eq_fract_add_translated alpha j
    have hkhalf : |(k : ℝ)| / 2 ≤ |alpha + (j : ℝ)| := by
      rw [hy]
      exact half_abs_intCast_le_abs_fract_add alpha k hk0 hkneg
    have hkabs : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk0)
    have hSy : 0 < |S * (alpha + (j : ℝ))| := by
      have : 0 < |alpha + (j : ℝ)| := lt_of_lt_of_le (by positivity) hkhalf
      rw [abs_mul, abs_of_pos hS]
      positivity
    have hQpow : Q ^ n ≤ |S * (alpha + (j : ℝ))| ^ n :=
      pow_le_pow_left₀ hQ.le hfar n
    have hkpow : S ^ 2 * (|(k : ℝ)| / 2) ^ 2 ≤
        |S * (alpha + (j : ℝ))| ^ 2 := by
      calc
        S ^ 2 * (|(k : ℝ)| / 2) ^ 2 =
            (S * (|(k : ℝ)| / 2)) ^ 2 := by ring
        _ ≤ (S * |alpha + (j : ℝ)|) ^ 2 := by
          exact pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left hkhalf hS.le) 2
        _ = |S * (alpha + (j : ℝ))| ^ 2 := by
          rw [abs_mul, abs_of_pos hS]
    have hdecay := gmAffineScaledBumpDual_polynomial_decay
      (n + 2) hS (alpha + (j : ℝ))
    have hfactor :
        Q ^ n * (S ^ 2 * (|(k : ℝ)| / 2) ^ 2) ≤
          |S * (alpha + (j : ℝ))| ^ (n + 2) := by
      rw [pow_add]
      exact mul_le_mul hQpow hkpow (by positivity) (by positivity)
    have hbound :
        ‖gmAffineScaledBumpDual S hS (alpha + (j : ℝ))‖ ≤
          (S * C) /
            (Q ^ n * (S ^ 2 * (|(k : ℝ)| / 2) ^ 2)) := by
      rw [le_div_iff₀ (mul_pos (pow_pos hQ n)
        (mul_pos (pow_pos hS 2) (pow_pos (by positivity : 0 < |(k : ℝ)| / 2) 2)))]
      calc
        ‖gmAffineScaledBumpDual S hS (alpha + (j : ℝ))‖ *
              (Q ^ n * (S ^ 2 * (|(k : ℝ)| / 2) ^ 2)) ≤
            ‖gmAffineScaledBumpDual S hS (alpha + (j : ℝ))‖ *
              |S * (alpha + (j : ℝ))| ^ (n + 2) := by gcongr
        _ = |S * (alpha + (j : ℝ))| ^ (n + 2) *
              ‖gmAffineScaledBumpDual S hS (alpha + (j : ℝ))‖ := by ring
        _ ≤ S * C := by simpa only [C] using hdecay
    have hprofile : gmIntDecayProfile 2 k = 1 / |(k : ℝ)| ^ 2 := by
      simp [gmIntDecayProfile, show k ≠ 0 from hk0]
    rw [show j + ⌊alpha⌋ = k by rfl, hprofile]
    calc
      ‖gmAffineScaledBumpDual S hS (alpha + (j : ℝ))‖ ≤
          (S * C) / (Q ^ n * (S ^ 2 * (|(k : ℝ)| / 2) ^ 2)) := hbound
      _ = (4 * C / (S * Q ^ n)) * (1 / |(k : ℝ)| ^ 2) := by
        field_simp [hS.ne', hkabs.ne', hQ.ne']
        ring
      _ = (4 * C / (S * Q ^ n)) * (1 / |(k : ℝ)| ^ 2) := rfl
  · exact mul_nonneg (by positivity) (by
      unfold gmIntDecayProfile
      split_ifs <;> positivity)

theorem norm_gmAffineScaledFarTerm_le_exception
    (n : ℕ) {S : ℝ} (hS : 0 < S) {alpha Q : ℝ} (hQ : 0 < Q)
    (j : ℤ) :
    ‖gmAffineScaledFarTerm S hS alpha Q j‖ ≤
      S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        Q ^ (n + 2) := by
  rw [norm_gmAffineScaledFarTerm]
  split_ifs with hfar
  · rw [le_div_iff₀ (pow_pos hQ (n + 2))]
    calc
      ‖gmAffineScaledBumpDual S hS (alpha + (j : ℝ))‖ * Q ^ (n + 2) ≤
          ‖gmAffineScaledBumpDual S hS (alpha + (j : ℝ))‖ *
            |S * (alpha + (j : ℝ))| ^ (n + 2) := by gcongr
      _ = |S * (alpha + (j : ℝ))| ^ (n + 2) *
            ‖gmAffineScaledBumpDual S hS (alpha + (j : ℝ))‖ := by ring
      _ ≤ S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual :=
        gmAffineScaledBumpDual_polynomial_decay (n + 2) hS _
  · positivity

theorem norm_gmAffineScaledFarTerm_le_majorant
    (n : ℕ) {S : ℝ} (hS : 0 < S)
    {alpha Q : ℝ} (hQ : 0 < Q) (j : ℤ) :
    ‖gmAffineScaledFarTerm S hS alpha Q j‖ ≤
      gmAffineScaledFarMajorant n S alpha Q j := by
  let k : ℤ := j + ⌊alpha⌋
  let D : ℝ := S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
    Q ^ (n + 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  by_cases hk0 : k = 0
  · have hex := norm_gmAffineScaledFarTerm_le_exception n hS
      (alpha := alpha) hQ j
    unfold gmAffineScaledFarMajorant
    rw [show j + ⌊alpha⌋ = 0 from hk0]
    simpa [gmIntDecayProfile] using hex
  · by_cases hkneg : k = -1
    · have hex := norm_gmAffineScaledFarTerm_le_exception n hS
        (alpha := alpha) hQ j
      unfold gmAffineScaledFarMajorant
      rw [show j + ⌊alpha⌋ = -1 from hkneg]
      have hmain0 : 0 ≤
          4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
            (S * Q ^ n) := by
        positivity
      simpa [gmIntDecayProfile] using
        hex.trans (le_add_of_nonneg_left hmain0)
    · have hmain := norm_gmAffineScaledFarTerm_le_profile n hS hQ j hk0 hkneg
      unfold gmAffineScaledFarMajorant
      rw [if_neg hk0, if_neg hkneg, add_zero, add_zero]
      exact hmain

theorem summable_gmAffineScaledFarMajorant
    (n : ℕ) (S alpha Q : ℝ) :
    Summable (gmAffineScaledFarMajorant n S alpha Q) := by
  unfold gmAffineScaledFarMajorant
  have hmain := (summable_gmIntDecayProfile_floorTranslate alpha).mul_left
    (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
      (S * Q ^ n))
  have hzero : Summable (fun j : ℤ =>
      if j + ⌊alpha⌋ = 0 then
        S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ (n + 2) else 0) := by
    apply (hasSum_single (-⌊alpha⌋) (fun j hj => ?_)).summable
    rw [if_neg]
    intro heq
    apply hj
    omega
  have hneg : Summable (fun j : ℤ =>
      if j + ⌊alpha⌋ = -1 then
        S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ (n + 2) else 0) := by
    apply (hasSum_single (-1 - ⌊alpha⌋) (fun j hj => ?_)).summable
    rw [if_neg]
    intro heq
    apply hj
    omega
  exact (hmain.add hzero).add hneg

theorem tsum_gmAffineScaledFarMajorant
    (n : ℕ) (S alpha Q : ℝ) :
    (∑' j : ℤ, gmAffineScaledFarMajorant n S alpha Q j) =
      (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        (S * Q ^ n)) *
          (∑' k : ℤ, gmIntDecayProfile 2 k) +
        2 * (S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ (n + 2)) := by
  let A : ℝ := 4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
    (S * Q ^ n)
  let D : ℝ := S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
    Q ^ (n + 2)
  let F : ℤ → ℝ := fun j => A * gmIntDecayProfile 2 (j + ⌊alpha⌋)
  let Z : ℤ → ℝ := fun j => if j + ⌊alpha⌋ = 0 then D else 0
  let L : ℤ → ℝ := fun j => if j + ⌊alpha⌋ = -1 then D else 0
  have hF : Summable F :=
    (summable_gmIntDecayProfile_floorTranslate alpha).mul_left A
  have hZ : Summable Z := by
    apply (hasSum_single (-⌊alpha⌋) (fun j hj => ?_)).summable
    dsimp only [Z]
    rw [if_neg]
    intro heq
    apply hj
    omega
  have hL : Summable L := by
    apply (hasSum_single (-1 - ⌊alpha⌋) (fun j hj => ?_)).summable
    dsimp only [L]
    rw [if_neg]
    intro heq
    apply hj
    omega
  have hZsum : (∑' j : ℤ, Z j) = D := by
    calc
      (∑' j : ℤ, Z j) = ∑' j : ℤ, if j = -⌊alpha⌋ then D else 0 := by
        apply tsum_congr
        intro j
        dsimp only [Z]
        by_cases h : j + ⌊alpha⌋ = 0
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      _ = D := tsum_ite_eq (-⌊alpha⌋) (fun _ : ℤ => D)
  have hLsum : (∑' j : ℤ, L j) = D := by
    calc
      (∑' j : ℤ, L j) = ∑' j : ℤ, if j = -1 - ⌊alpha⌋ then D else 0 := by
        apply tsum_congr
        intro j
        dsimp only [L]
        by_cases h : j + ⌊alpha⌋ = -1
        · rw [if_pos h, if_pos (by omega)]
        · rw [if_neg h, if_neg (by omega)]
      _ = D := tsum_ite_eq (-1 - ⌊alpha⌋) (fun _ : ℤ => D)
  change tsum (fun j : ℤ => (F j + Z j) + L j) = _
  rw [(hF.add hZ).tsum_add hL, hF.tsum_add hZ, hZsum, hLsum]
  rw [show (∑' j : ℤ, F j) = A * (∑' k : ℤ, gmIntDecayProfile 2 k) by
    dsimp only [F]
    rw [tsum_mul_left, tsum_gmIntDecayProfile_floorTranslate]]
  dsimp only [A, D]
  ring

theorem summable_gmAffineScaledFarTerm
    (n : ℕ) {S : ℝ} (hS : 0 < S)
    {alpha Q : ℝ} (hQ : 0 < Q) :
    Summable (gmAffineScaledFarTerm S hS alpha Q) := by
  apply summable_norm_iff.mp
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun j => norm_gmAffineScaledFarTerm_le_majorant n hS hQ j)
  exact summable_gmAffineScaledFarMajorant n S alpha Q

noncomputable def gmAffineScaledFarSeries
    (S : ℝ) (hS : 0 < S) (alpha Q : ℝ) : ℂ :=
  ∑' j : ℤ, gmAffineScaledFarTerm S hS alpha Q j

set_option maxHeartbeats 800000 in
theorem norm_gmAffineScaledFarSeries_le
    (n : ℕ) {S : ℝ} (hS : 0 < S)
    {alpha Q : ℝ} (hQ : 0 < Q) :
    ‖gmAffineScaledFarSeries S hS alpha Q‖ ≤
      (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        (S * Q ^ n)) *
          (∑' k : ℤ, gmIntDecayProfile 2 k) +
        2 * (S * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
          Q ^ (n + 2)) := by
  unfold gmAffineScaledFarSeries
  have hsum := summable_gmAffineScaledFarTerm n hS (alpha := alpha) hQ
  exact (norm_tsum_le_tsum_norm (summable_norm_iff.mpr hsum)).trans
    ((hsum.norm.tsum_le_tsum
      (fun j => norm_gmAffineScaledFarTerm_le_majorant n hS hQ j)
      (summable_gmAffineScaledFarMajorant n S alpha Q)).trans_eq
        (tsum_gmAffineScaledFarMajorant n S alpha Q))

/-- Exact finite retained/omitted decomposition of the second Poisson
lattice. -/
theorem tsum_gmAffineScaledBumpDual_eq_near_add_far
    (n : ℕ) {S : ℝ} (hS : 0 < S)
    {alpha Q : ℝ} (hQ : 0 < Q) :
    (∑' j : ℤ, gmAffineScaledBumpDual S hS (alpha + j)) =
      (∑ j ∈ gmAffineScaledNearSet S alpha Q,
        gmAffineScaledBumpDual S hS (alpha + j)) +
          gmAffineScaledFarSeries S hS alpha Q := by
  have hnear := summable_gmAffineScaledNearTerm hS alpha Q
  have hfar := summable_gmAffineScaledFarTerm n hS (alpha := alpha) hQ
  calc
    (∑' j : ℤ, gmAffineScaledBumpDual S hS (alpha + j)) =
        ∑' j : ℤ, (gmAffineScaledNearTerm S hS alpha Q j +
          gmAffineScaledFarTerm S hS alpha Q j) := by
      apply tsum_congr
      intro j
      exact gmAffineScaledBumpDual_eq_near_add_far hS alpha Q j
    _ = (∑' j : ℤ, gmAffineScaledNearTerm S hS alpha Q j) +
          ∑' j : ℤ, gmAffineScaledFarTerm S hS alpha Q j :=
      hnear.tsum_add hfar
    _ = (∑ j ∈ gmAffineScaledNearSet S alpha Q,
          gmAffineScaledBumpDual S hS (alpha + j)) +
          gmAffineScaledFarSeries S hS alpha Q := by
      rw [tsum_gmAffineScaledNearTerm_eq_sum]
      rfl

/-- Equation (9.7)'s second Poisson sum, split into its exact finite
stationary window and the complete omitted series. -/
theorem gmAffineMiddleZ₂_eq_near_add_far
    (n : ℕ) {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    {Q : ℝ} (hQ : 0 < Q)
    (m₂ m₂' : ℤ) (u u' : ℝ) :
    gmAffineMiddleZ₂ T M₂ m₂ m₂' u u' =
      (∑ j ∈ gmAffineScaledNearSet (T / M₂)
          (-gmAffineMiddleDisplacement m₂ m₂' u u') Q,
        gmAffineScaledBumpDual (T / M₂) (by positivity)
          ((j : ℝ) - gmAffineMiddleDisplacement m₂ m₂' u u')) +
        gmAffineScaledFarSeries (T / M₂) (by positivity)
          (-gmAffineMiddleDisplacement m₂ m₂' u u') Q := by
  let S : ℝ := T / M₂
  have hS : 0 < S := by dsimp only [S]; positivity
  rw [gmAffineMiddleZ₂_poisson hT hM₂]
  have hsplit := tsum_gmAffineScaledBumpDual_eq_near_add_far
    n hS (alpha := -gmAffineMiddleDisplacement m₂ m₂' u u') hQ
  simpa only [S, sub_eq_add_neg, neg_add_rev, neg_neg, add_comm] using hsplit

/-- Uniform arbitrary-order bound for the complete omitted dual lattice in
the middle-frequency argument.  Choosing `Q=T^η` and `n` after the
epsilon budget yields the paper's `O(T⁻¹⁰⁰)`. -/
theorem norm_gmAffineMiddleZ₂_farSeries_le
    (n : ℕ) {T : ℝ} (hT : 0 < T) {M₂ : ℕ} (hM₂ : 0 < M₂)
    {Q : ℝ} (hQ : 0 < Q)
    (m₂ m₂' : ℤ) (u u' : ℝ) :
    ‖gmAffineScaledFarSeries (T / M₂) (by positivity)
        (-gmAffineMiddleDisplacement m₂ m₂' u u') Q‖ ≤
      (4 * SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
        ((T / M₂) * Q ^ n)) *
          (∑' k : ℤ, gmIntDecayProfile 2 k) +
        2 * ((T / M₂) *
          SchwartzMap.seminorm ℝ (n + 2) 0 gmAffineLocalBumpDual /
            Q ^ (n + 2)) := by
  have hS : 0 < T / (M₂ : ℝ) := by positivity
  exact norm_gmAffineScaledFarSeries_le n hS hQ

/-- The compact `tau`-integral `Z₁` in equation (9.7), with the same fixed
local bump used throughout the source-facing Section 9 argument. -/
noncomputable def gmAffineMiddleTauPhase
    (A : ℝ) (m₂ m₂' : ℤ) (u u' tau : ℝ) : ℝ :=
  2 * Real.pi * tau *
    (((m₂' : ℝ) / A) * u' - ((m₂ : ℝ) / A) * u)

noncomputable def gmAffineMiddleZ₁
    (A : ℝ) (m₂ m₂' : ℤ) (u u' : ℝ) : ℂ :=
  ∫ tau : ℝ, (gmCubicLocalBump tau : ℂ) *
    Complex.exp ((gmAffineMiddleTauPhase A m₂ m₂' u u' tau : ℂ) * I)

theorem integrable_gmAffineMiddleZ₁_integrand
    (A : ℝ) (m₂ m₂' : ℤ) (u u' : ℝ) :
    Integrable (fun tau : ℝ => (gmCubicLocalBump tau : ℂ) *
      Complex.exp ((gmAffineMiddleTauPhase A m₂ m₂' u u' tau : ℂ) * I)) := by
  have hb : Integrable (fun tau : ℝ => (gmCubicLocalBump tau : ℂ)) := by
    simpa only [gmAffineLocalBumpSchwartz_apply] using gmAffineLocalBumpSchwartz.integrable
  apply hb.norm.mono'
  · change AEStronglyMeasurable (fun tau : ℝ =>
        gmAffineLocalBumpSchwartz tau *
          Complex.exp ((gmAffineMiddleTauPhase A m₂ m₂' u u' tau : ℂ) * I))
    exact (gmAffineLocalBumpSchwartz.continuous.mul (by
      unfold gmAffineMiddleTauPhase
      fun_prop)).aestronglyMeasurable
  · filter_upwards with tau
    rw [norm_mul, Complex.norm_exp]
    simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (gmCubicLocalBump_nonneg tau)]
    exact le_rfl

theorem integral_gmCubicLocalBump_le_four :
    (∫ tau : ℝ, gmCubicLocalBump tau) ≤ 4 := by
  have hb : Integrable gmCubicLocalBump := by
    have hc : Integrable (fun tau : ℝ => (gmCubicLocalBump tau : ℂ)) := by
      simpa only [gmAffineLocalBumpSchwartz_apply] using gmAffineLocalBumpSchwartz.integrable
    exact (Complex.reCLM.integrable_comp hc)
  have hsupp : ∀ tau : ℝ, tau ∉ Set.Icc (-2 : ℝ) 2 → gmCubicLocalBump tau = 0 := by
    intro tau htau
    apply gmCubicLocalBump_eq_zero_of_two_le_abs
    rw [Set.mem_Icc, not_and_or, not_le] at htau
    rcases htau with hleft | hright
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact (lt_of_not_ge hright).le
  calc
    (∫ tau : ℝ, gmCubicLocalBump tau) =
        ∫ tau in Set.Icc (-2 : ℝ) 2, gmCubicLocalBump tau := by
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with tau
      by_cases htau : tau ∈ Set.Icc (-2 : ℝ) 2
      · rw [Set.indicator_of_mem htau]
      · rw [Set.indicator_of_notMem htau, hsupp tau htau]
    _ ≤ ∫ _tau in Set.Icc (-2 : ℝ) 2, (1 : ℝ) := by
      apply MeasureTheory.setIntegral_mono_on hb.integrableOn
        (continuousOn_const.integrableOn_compact isCompact_Icc) measurableSet_Icc
      intro tau _
      exact gmCubicLocalBump_le_one tau
    _ = 4 := by norm_num

/-- The paper's trivial estimate `|Z₁| ≪ 1`, with an explicit universal
constant for the fixed cutoff. -/
theorem norm_gmAffineMiddleZ₁_le_four
    (A : ℝ) (m₂ m₂' : ℤ) (u u' : ℝ) :
    ‖gmAffineMiddleZ₁ A m₂ m₂' u u'‖ ≤ 4 := by
  unfold gmAffineMiddleZ₁
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    (∫ tau : ℝ, ‖(gmCubicLocalBump tau : ℂ) *
        Complex.exp ((gmAffineMiddleTauPhase A m₂ m₂' u u' tau : ℂ) * I)‖) =
        ∫ tau : ℝ, gmCubicLocalBump tau := by
      apply integral_congr_ae
      filter_upwards with tau
      rw [norm_mul, Complex.norm_exp]
      simp only [mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (gmCubicLocalBump_nonneg tau)]
    _ ≤ 4 := integral_gmCubicLocalBump_le_four

/-! ### The source smoothing operator `f_tilde` -/

/-- The normalized width-`1/T` Schwartz kernel `T psi(Tx)` from Lemma 9.2. -/
noncomputable def gmAffineSmoothingKernel
    (T : ℝ) (hT : 0 < T) : SchwartzMap ℝ ℂ :=
  (T : ℂ) • gmAffineScaledBumpSchwartz (1 / T) (by positivity)

@[simp]
theorem gmAffineSmoothingKernel_apply
    (T : ℝ) (hT : 0 < T) (x : ℝ) :
    gmAffineSmoothingKernel T hT x =
      (T * gmCubicLocalBump (T * x) : ℝ) := by
  rw [gmAffineSmoothingKernel, SchwartzMap.smul_apply,
    gmAffineScaledBumpSchwartz_apply]
  push_cast
  congr 1
  field_simp [hT.ne']

/-- Guth--Maynard's `f_tilde`, realized inside Schwartz space.  Taking the
real part is definitionally harmless because both input functions are real. -/
noncomputable def gmAffineTildeSchwartz
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) : SchwartzMap ℝ ℝ :=
  (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
    (gmAffineSmoothingKernel T hT) (gmAffineComplexify f)).postcompCLM Complex.reCLM

theorem integrable_gmAffineSmoothingConvolution_integrand
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) (u : ℝ) :
    Integrable (fun t : ℝ =>
      (ContinuousLinearMap.mul ℂ ℂ) (gmAffineSmoothingKernel T hT t)
        (gmAffineComplexify f (u - t))) := by
  let C : ℝ := SchwartzMap.seminorm ℝ 0 0 (gmAffineComplexify f)
  have hmajor : Integrable (fun t : ℝ => C * ‖gmAffineSmoothingKernel T hT t‖) :=
    (gmAffineSmoothingKernel T hT).integrable.norm.const_mul C
  apply hmajor.mono'
  · exact ((gmAffineSmoothingKernel T hT).continuous.mul
      ((gmAffineComplexify f).continuous.comp
        (continuous_const.sub continuous_id))).aestronglyMeasurable
  · filter_upwards with t
    change ‖gmAffineSmoothingKernel T hT t * gmAffineComplexify f (u - t)‖ ≤ _
    rw [norm_mul]
    have hfbound : ‖gmAffineComplexify f (u - t)‖ ≤ C := by
      simpa only [C] using
        (SchwartzMap.norm_le_seminorm ℝ (gmAffineComplexify f) (u - t))
    simpa only [mul_comm] using
      (mul_le_mul_of_nonneg_left hfbound
        (norm_nonneg (gmAffineSmoothingKernel T hT t)))

/-- Literal integral formula for the Schwartz convolution defining
`f_tilde`. -/
theorem gmAffineTildeSchwartz_apply
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) (u : ℝ) :
    gmAffineTildeSchwartz T hT f u =
      ∫ u' : ℝ, T * gmCubicLocalBump (T * u') * f (u - u') := by
  rw [gmAffineTildeSchwartz, SchwartzMap.postcompCLM_apply,
    SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
  have hint := integrable_gmAffineSmoothingConvolution_integrand T hT f u
  let g : ℝ → ℂ := fun t =>
    (ContinuousLinearMap.mul ℂ ℂ) (gmAffineSmoothingKernel T hT t)
      (gmAffineComplexify f (u - t))
  change Complex.re (∫ t : ℝ, g t) = _
  calc
    Complex.re (∫ t : ℝ, g t) = ∫ t : ℝ, Complex.re (g t) :=
      (integral_re hint).symm
    _ = ∫ u' : ℝ, T * gmCubicLocalBump (T * u') * f (u - u') := by
      apply integral_congr_ae
      filter_upwards with u'
      dsimp only [g]
      rw [gmAffineSmoothingKernel_apply, gmAffineComplexify_apply]
      simp

/-- The real-valued smoothing operation loses no information when it is
complexified: it is exactly the Schwartz convolution used by Fourier
analysis. -/
theorem gmAffineComplexify_tilde_eq_convolution
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ) :
    gmAffineComplexify (gmAffineTildeSchwartz T hT f) =
      SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
        (gmAffineSmoothingKernel T hT) (gmAffineComplexify f) := by
  ext u
  rw [gmAffineComplexify_apply, gmAffineTildeSchwartz,
    SchwartzMap.postcompCLM_apply, SchwartzMap.convolution_apply,
    MeasureTheory.convolution_def]
  let g : ℝ → ℂ := fun t =>
    (ContinuousLinearMap.mul ℂ ℂ) (gmAffineSmoothingKernel T hT t)
      (gmAffineComplexify f (u - t))
  have hint : Integrable g := by
    simpa only [g] using
      integrable_gmAffineSmoothingConvolution_integrand T hT f u
  have hImIntegral : (∫ t : ℝ, Complex.im (g t)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with t
    dsimp only [g]
    rw [gmAffineSmoothingKernel_apply, gmAffineComplexify_apply]
    simp
  have hIm : Complex.im (∫ t : ℝ, g t) = 0 := by
    exact (integral_im hint).symm.trans hImIntegral
  change ((Complex.re (∫ t : ℝ, g t) : ℝ) : ℂ) = ∫ t : ℝ, g t
  apply Complex.ext <;> simp [hIm]

theorem gmAffineTildeSchwartz_nonneg
    (T : ℝ) (hT : 0 < T) (f : SchwartzMap ℝ ℝ)
    (hf : ∀ u, 0 ≤ f u) (u : ℝ) :
    0 ≤ gmAffineTildeSchwartz T hT f u := by
  rw [gmAffineTildeSchwartz_apply]
  apply integral_nonneg
  intro t
  exact mul_nonneg
    (mul_nonneg hT.le (gmCubicLocalBump_nonneg (T * t))) (hf (u - t))

theorem integral_gmAffineSmoothingKernelReal_eq
    (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ, T * gmCubicLocalBump (T * x)) =
      ∫ y : ℝ, gmCubicLocalBump y := by
  calc
    (∫ x : ℝ, T * gmCubicLocalBump (T * x)) =
        T * ∫ x : ℝ, gmCubicLocalBump (T * x) := by
      rw [integral_const_mul]
    _ = T * (|T⁻¹| * ∫ y : ℝ, gmCubicLocalBump y) := by
      rw [MeasureTheory.Measure.integral_comp_mul_left]
      simp only [smul_eq_mul]
    _ = ∫ y : ℝ, gmCubicLocalBump y := by
      rw [abs_of_pos (inv_pos.mpr hT)]
      rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]

theorem integral_gmAffineSmoothingKernelReal_le_four
    (T : ℝ) (hT : 0 < T) :
    (∫ x : ℝ, T * gmCubicLocalBump (T * x)) ≤ 4 := by
  rw [integral_gmAffineSmoothingKernelReal_eq T hT]
  exact integral_gmCubicLocalBump_le_four

/-- Pointwise Region-I control obtained from the exact retained/omitted
Poisson identity.  In particular, no omitted frequency has been replaced
by a separate assumption. -/
theorem norm_gmAffineSmoothTransformSchwartz_fourier_le_envelopes
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q : ℝ} (hQ : 0 < Q) (xi : ℝ) :
    ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ≤
      gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q +
        gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q := by
  rw [gmAffineSmoothTransformSchwartz_fourier_eq_main_add_far
    n f hM₁ hM₂ hM₃ hQ xi]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [gmAffinePoissonMainEnvelope] using
      norm_gmAffinePoissonMainFourier_le f hM₁ hM₂ hM₃ hQ xi
  · simpa only [gmAffinePoissonFarEnvelope] using
      norm_gmAffinePoissonFarFourier_le n f hM₁ hM₂ hM₃ hQ xi

/-- Integrated Region-I estimate, the exact finite-envelope form of
equation (9.6). -/
theorem integral_gmAffineLowFrequencyRegion_fourier_sq_le
    (n : ℕ) (f : SchwartzMap ℝ ℝ) {M₁ M₂ M₃ : ℕ}
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    {Q X : ℝ} (hQ : 0 < Q) (hX : 0 ≤ X) :
    (∫ xi in gmAffineLowFrequencyRegion X,
        ‖fourier (gmAffineSmoothTransformSchwartz f M₁ M₂ M₃) xi‖ ^ 2) ≤
      2 * X *
        (gmAffinePoissonMainEnvelope f M₁ M₂ M₃ Q +
          gmAffinePoissonFarEnvelope n f M₁ M₂ M₃ Q) ^ 2 := by
  apply integral_gmAffineLowFrequencyRegion_sq_le hX
  intro xi hxi
  exact norm_gmAffineSmoothTransformSchwartz_fourier_le_envelopes
    n f hM₁ hM₂ hM₃ hQ xi

theorem gmAffineTransformIntegral_le_crude_scales
    {f : ℝ → ℝ} (hf₂ : Integrable fun x : ℝ => f x ^ 2)
    {M₁ M₂ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) :
    gmAffineTransformIntegral f M₁ M₂ M₃ ≤
      ((gmAffineIndexSet M₁ M₂ M₃).card : ℝ) ^ 2 *
        ((2 * M₂ : ℝ) / M₁) * ∫ x : ℝ, f x ^ 2 := by
  have hI : 0 ≤ ∫ x : ℝ, f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine (gmAffineTransformIntegral_le_indexSum hf₂ hM₁ hM₂).trans ?_
  let S := gmAffineIndexSet M₁ M₂ M₃
  have hsum :
      (∑ p ∈ S, (|(p.2.1 : ℝ) / (p.1 : ℝ)| * ∫ x : ℝ, f x ^ 2)) ≤
        (S.card : ℝ) * (((2 * M₂ : ℝ) / M₁) * ∫ x : ℝ, f x ^ 2) := by
    calc
      (∑ p ∈ S, (|(p.2.1 : ℝ) / (p.1 : ℝ)| * ∫ x : ℝ, f x ^ 2)) ≤
          ∑ p ∈ S, (((2 * M₂ : ℝ) / M₁) * ∫ x : ℝ, f x ^ 2) := by
        apply Finset.sum_le_sum
        intro p hp
        gcongr
        exact abs_affine_ratio_le hM₁ (mem_gmAffineIndexSet.mp hp).1
          (mem_gmAffineIndexSet.mp hp).2.1
      _ = (S.card : ℝ) * (((2 * M₂ : ℝ) / M₁) * ∫ x : ℝ, f x ^ 2) := by
        simp
  dsimp only [S] at hsum
  calc
    ((gmAffineIndexSet M₁ M₂ M₃).card : ℝ) *
        ∑ p ∈ gmAffineIndexSet M₁ M₂ M₃,
          (|(p.2.1 : ℝ) / (p.1 : ℝ)| * ∫ x : ℝ, f x ^ 2) ≤
        ((gmAffineIndexSet M₁ M₂ M₃).card : ℝ) *
          (((gmAffineIndexSet M₁ M₂ M₃).card : ℝ) *
            (((2 * M₂ : ℝ) / M₁) * ∫ x : ℝ, f x ^ 2)) := by
      gcongr
    _ = ((gmAffineIndexSet M₁ M₂ M₃).card : ℝ) ^ 2 *
          ((2 * M₂ : ℝ) / M₁) * ∫ x : ℝ, f x ^ 2 := by ring

theorem card_gmAffineIndexSet_le_scaleProduct
    {M₁ M₂ M₃ : ℕ} (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃) :
    (gmAffineIndexSet M₁ M₂ M₃).card ≤ 136 * M₁ * M₂ * M₃ := by
  refine (card_gmAffineIndexSet_le M₁ M₂ M₃).trans ?_
  calc
    2 * (M₁ + 1) * (M₂ + 1) * (16 * M₃ + 1) ≤
        2 * (2 * M₁) * (2 * M₂) * (17 * M₃) := by
      gcongr <;> omega
    _ = 136 * M₁ * M₂ * M₃ := by ring

/-- The source crude estimate `J(f) ≪ M⁶ ∫f²`, retaining an explicit
absolute constant.  This is the base case for the Section 9 iteration. -/
theorem gmAffineTransformIntegral_le_crude
    {f : ℝ → ℝ} (hf₂ : Integrable fun x : ℝ => f x ^ 2)
    {M M₁ M₂ M₃ : ℕ} (hscale : (M₁, M₂, M₃) ∈ gmAffineScaleTriples M) :
    gmAffineTransformIntegral f M₁ M₂ M₃ ≤
      36992 * (M : ℝ) ^ 6 * ∫ x : ℝ, f x ^ 2 := by
  rcases mem_gmAffineScaleTriples.mp hscale with
    ⟨hM₁, hM₁M, hM₂, hM₂M, hM₃, hM₃M⟩
  have hM₁pos : 0 < M₁ := hM₁
  have hM₂pos : 0 < M₂ := hM₂
  have hM₃pos : 0 < M₃ := hM₃
  have hI : 0 ≤ ∫ x : ℝ, f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hcardNat := card_gmAffineIndexSet_le_scaleProduct hM₁pos hM₂pos hM₃pos
  have hcard : ((gmAffineIndexSet M₁ M₂ M₃).card : ℝ) ≤
      136 * M₁ * M₂ * M₃ := by exact_mod_cast hcardNat
  have hM₁r : (0 : ℝ) < M₁ := by exact_mod_cast hM₁pos
  have hscaleReal :
      (M₁ : ℝ) * (M₂ : ℝ) ^ 3 * (M₃ : ℝ) ^ 2 ≤ (M : ℝ) ^ 6 := by
    have h₁ : (M₁ : ℝ) ≤ M := by exact_mod_cast hM₁M
    have h₂ : (M₂ : ℝ) ≤ M := by exact_mod_cast hM₂M
    have h₃ : (M₃ : ℝ) ≤ M := by exact_mod_cast hM₃M
    have hMnonneg : (0 : ℝ) ≤ M := by positivity
    calc
      (M₁ : ℝ) * (M₂ : ℝ) ^ 3 * (M₃ : ℝ) ^ 2 ≤
          (M : ℝ) * (M : ℝ) ^ 3 * (M : ℝ) ^ 2 := by
        gcongr
      _ = (M : ℝ) ^ 6 := by ring
  refine (gmAffineTransformIntegral_le_crude_scales hf₂ hM₁pos hM₂pos).trans ?_
  calc
    ((gmAffineIndexSet M₁ M₂ M₃).card : ℝ) ^ 2 *
        ((2 * M₂ : ℝ) / M₁) * ∫ x : ℝ, f x ^ 2 ≤
        (136 * (M₁ : ℝ) * M₂ * M₃) ^ 2 *
          ((2 * M₂ : ℝ) / M₁) * ∫ x : ℝ, f x ^ 2 := by
      gcongr
    _ = 36992 * ((M₁ : ℝ) * (M₂ : ℝ) ^ 3 * (M₃ : ℝ) ^ 2) *
          ∫ x : ℝ, f x ^ 2 := by
      field_simp [hM₁r.ne']
      ring
    _ ≤ 36992 * (M : ℝ) ^ 6 * ∫ x : ℝ, f x ^ 2 := by
      gcongr

theorem gmAffineJ_le_crude
    {f : ℝ → ℝ} (hf₂ : Integrable fun x : ℝ => f x ^ 2)
    {M : ℕ} (hM : 0 < M) :
    gmAffineJ f M ≤ 36992 * (M : ℝ) ^ 6 * ∫ x : ℝ, f x ^ 2 := by
  obtain ⟨M₁, M₂, M₃, hscale, hEq⟩ := exists_gmAffineTransformIntegral_eq_J f hM
  rw [← hEq]
  exact gmAffineTransformIntegral_le_crude hf₂ hscale

end RiemannZeta.GuthMaynard
