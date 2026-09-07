import GafniTao.HeathBrownAtkinsonEquation719Uniform

/-!
# Summing Ivić equation (7.19) on a separated height family

This is the finite harmonic summation used in Ivić's Lemma 7.1.  It keeps
the quadratic square-root-gap contribution distinct from the linear
reciprocal-gap contribution.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

def heathBrownAtkinsonEquation719FirstCoefficient
    (T : ℝ) (K : ℕ) : ℝ :=
  900 * Real.sqrt T / heathBrownAtkinsonQuarterScale (T / 2) K

def heathBrownAtkinsonEquation719ReciprocalCoefficient
    (T : ℝ) (K : ℕ) : ℝ :=
  28 * Real.sqrt (T * (K + 1 : ℕ))

theorem heathBrownAtkinsonEquation719FirstCoefficient_nonneg
    {T : ℝ} {K : ℕ} (hT : 0 < T) :
    0 ≤ heathBrownAtkinsonEquation719FirstCoefficient T K := by
  unfold heathBrownAtkinsonEquation719FirstCoefficient
  exact div_nonneg (by positivity)
    (heathBrownAtkinsonQuarterScale_pos (half_pos hT)).le

theorem heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg
    {T : ℝ} {K : ℕ} (hT : 0 < T) :
    0 ≤ heathBrownAtkinsonEquation719ReciprocalCoefficient T K := by
  unfold heathBrownAtkinsonEquation719ReciprocalCoefficient
  positivity

/-- Every gap in a dyadic height box lies below the natural ceiling of the
box height. -/
theorem abs_sub_le_natCeil_of_mem_dyadic
    {T t u : ℝ} (hT : 0 < T)
    (ht : t ∈ Set.Icc (T / 2) T) (hu : u ∈ Set.Icc (T / 2) T) :
    |u - t| ≤ ((⌈T⌉₊ : ℕ) : ℝ) := by
  have hgap : |u - t| ≤ T := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
  exact hgap.trans (Nat.le_ceil T)

/-- Exact identification of the reciprocal-gap row with the near-distance
filter used by the frozen harmonic lemma. -/
theorem sum_ite_inv_abs_sub_eq_near_filter
    {T t : ℝ} (W : Finset ℝ) (hT : 0 < T) (ht : t ∈ W)
    (hRange : ∀ x ∈ W, x ∈ Set.Icc (T / 2) T) :
    (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) =
      ∑ u ∈ {u ∈ W | u ≠ t ∧ |u - t| ≤ ((⌈T⌉₊ : ℕ) : ℝ)},
        1 / |u - t| := by
  have hfilter : {u ∈ W | u ≠ t} =
      {u ∈ W | u ≠ t ∧ |u - t| ≤ ((⌈T⌉₊ : ℕ) : ℝ)} := by
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hu, hne⟩
      exact ⟨hu, hne, abs_sub_le_natCeil_of_mem_dyadic hT
        (hRange t ht) (hRange u hu)⟩
    · rintro ⟨hu, hne, _⟩
      exact ⟨hu, hne⟩
  rw [← hfilter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hut : u = t
  · simp [hut]
  · simp [hut, abs_sub_comm]

/-- The reciprocal-gap row is harmonic, not linear, in the size of the
height interval. -/
theorem sum_ite_inv_abs_sub_le_harmonic
    {T t : ℝ} (W : Finset ℝ) (hT : 0 < T) (ht : t ∈ W)
    (hSep : IsSeparated 1 W)
    (hRange : ∀ x ∈ W, x ∈ Set.Icc (T / 2) T) :
    (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) ≤
      2 * (((harmonic ⌈T⌉₊ : ℚ) : ℝ)) := by
  rw [sum_ite_inv_abs_sub_eq_near_filter W hT ht hRange]
  exact sum_inv_distance_near_le_harmonic ⌈T⌉₊ W t hSep ht

/-- Pointwise uniform version of equation (7.19), split into a constant
first term and a reciprocal kernel. -/
theorem norm_heathBrownAtkinsonGram_le_equation719_split
    {K : ℕ} {T t u : ℝ}
    (hT : 0 < T) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (ht : t ∈ Set.Icc (T / 2) T)
    (hu : u ∈ Set.Icc (T / 2) T) (htu : t ≠ u) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      heathBrownAtkinsonEquation719FirstCoefficient T K +
        heathBrownAtkinsonEquation719ReciprocalCoefficient T K /
          |t - u| := by
  have hsource := norm_heathBrownAtkinsonGram_le_equation719_uniform
    hT hK hblock ht hu htu
  have hgap : |t - u| ≤ T := by
    rw [abs_le]
    constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
  have hsqrt : Real.sqrt |t - u| ≤ Real.sqrt T := Real.sqrt_le_sqrt hgap
  have hq : 0 < heathBrownAtkinsonQuarterScale (T / 2) K :=
    heathBrownAtkinsonQuarterScale_pos (half_pos hT)
  have hfirst :
      900 * Real.sqrt |t - u| /
          heathBrownAtkinsonQuarterScale (T / 2) K ≤
        heathBrownAtkinsonEquation719FirstCoefficient T K := by
    unfold heathBrownAtkinsonEquation719FirstCoefficient
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hq.le
  unfold heathBrownAtkinsonEquation719FirstCoefficient at hfirst
  unfold heathBrownAtkinsonEquation719UniformMajorant at hsource
  unfold heathBrownAtkinsonEquation719FirstCoefficient
    heathBrownAtkinsonEquation719ReciprocalCoefficient
  exact hsource.trans (add_le_add hfirst le_rfl)

/-- One row of off-diagonal Atkinson Gram entries. -/
theorem sum_offDiagonal_norm_heathBrownAtkinsonGram_le_equation719
    {K : ℕ} {T t : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (ht : t ∈ W) (hSep : IsSeparated 1 W)
    (hRange : ∀ x ∈ W, x ∈ Set.Icc (T / 2) T) :
    (∑ u ∈ W, if u = t then 0 else
        ‖heathBrownAtkinsonGram K t u‖) ≤
      (W.card : ℝ) * heathBrownAtkinsonEquation719FirstCoefficient T K +
        heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
          (2 * (((harmonic ⌈T⌉₊ : ℚ) : ℝ))) := by
  have hpoint : ∀ u ∈ W,
      (if u = t then 0 else ‖heathBrownAtkinsonGram K t u‖) ≤
        heathBrownAtkinsonEquation719FirstCoefficient T K +
          heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
            (if u = t then 0 else 1 / |t - u|) := by
    intro u hu
    by_cases hut : u = t
    · simp [hut, heathBrownAtkinsonEquation719FirstCoefficient_nonneg hT]
    · simp only [if_neg hut]
      have h := norm_heathBrownAtkinsonGram_le_equation719_split
        hT hK hblock (hRange t ht) (hRange u hu) (Ne.symm hut)
      simpa only [div_eq_mul_inv, one_mul] using h
  calc
    (∑ u ∈ W, if u = t then 0 else
        ‖heathBrownAtkinsonGram K t u‖) ≤
        ∑ u ∈ W,
          (heathBrownAtkinsonEquation719FirstCoefficient T K +
            heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
              (if u = t then 0 else 1 / |t - u|)) := by
      exact Finset.sum_le_sum fun u hu => hpoint u hu
    _ = (W.card : ℝ) * heathBrownAtkinsonEquation719FirstCoefficient T K +
        heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
          (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (W.card : ℝ) * heathBrownAtkinsonEquation719FirstCoefficient T K +
        heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
          (2 * (((harmonic ⌈T⌉₊ : ℚ) : ℝ))) := by
      have hrec :
          heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
              (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) ≤
            heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
              (2 * (((harmonic ⌈T⌉₊ : ℚ) : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (sum_ite_inv_abs_sub_le_harmonic W hT ht hSep hRange)
          (heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg hT)
      exact add_le_add le_rfl hrec


end

end GafniTao
