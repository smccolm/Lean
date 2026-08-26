import RiemannZeta.GuthMaynard.LargeValuesS3
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Fourier.PoissonSummation

open Complex Finset Filter MeasureTheory Real Set
open scoped FourierTransform Topology

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
  change f (((m₁ : ℝ) / (m₂ : ℝ)) * u + (m₃ : ℝ) / (m₂ : ℝ)) = _
  congr 1
  field_simp [show (m₂ : ℝ) ≠ 0 by exact_mod_cast hm₂]

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
