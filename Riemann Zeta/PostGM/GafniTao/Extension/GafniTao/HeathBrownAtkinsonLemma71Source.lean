import GafniTao.HeathBrownAtkinsonPrefixAggregate
import GafniTao.HeathBrownScaledSeparation
import GafniTao.HeathBrownAtkinsonEquation719Sum

/-!
# Source-shaped aggregate form of Ivić Lemma 7.1

Unlike the earlier unit-spacing terminal helper, this file retains the two
physical ordinate parameters in the source: a lower separation `G` and an
upper diameter `J`.  It applies Bombieri--Halász to the aggregate first
moment, uniformly for every literal prefix of the Atkinson sum.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

/-- The equation-(7.19) B-process coefficient after using the upper gap `J`,
without replacing it by the ambient height `T`. -/
def heathBrownAtkinsonSourceFirstCoefficient
    (T J : ℝ) (K : ℕ) : ℝ :=
  900 * Real.sqrt J / heathBrownAtkinsonQuarterScale (T / 2) K

theorem heathBrownAtkinsonSourceFirstCoefficient_nonneg
    {T J : ℝ} {K : ℕ} (hT : 0 < T) :
    0 ≤ heathBrownAtkinsonSourceFirstCoefficient T J K := by
  unfold heathBrownAtkinsonSourceFirstCoefficient
  exact div_nonneg (by positivity)
    (heathBrownAtkinsonQuarterScale_pos (half_pos hT)).le

/-- Every noncentral point in a `G`-separated family of diameter at most `J`
lies in the scaled harmonic window of radius `ceil(J/G) * G`. -/
theorem sum_ite_inv_abs_sub_le_scaled_harmonic
    {G J t : ℝ} (W : Finset ℝ) (hG : 0 < G)
    (ht : t ∈ W) (hSep : IsSeparated G W)
    (hDiameter : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ J) :
    (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) ≤
      (2 / G) * (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)) := by
  have hJCeil : J ≤ ((⌈J / G⌉₊ : ℕ) : ℝ) * G := by
    have hceil : J / G ≤ ((⌈J / G⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    exact (div_le_iff₀ hG).1 hceil
  have hfilter : {u ∈ W | u ≠ t} =
      {u ∈ W | u ≠ t ∧
        |u - t| ≤ ((⌈J / G⌉₊ : ℕ) : ℝ) * G} := by
    ext u
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hu, hne⟩
      exact ⟨hu, hne, (hDiameter u hu t ht).trans hJCeil⟩
    · rintro ⟨hu, hne, _⟩
      exact ⟨hu, hne⟩
  have hsource := sum_inv_distance_scaled_near_le_harmonic
    G ⌈J / G⌉₊ W t hG hSep ht
  calc
    (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) =
        ∑ u ∈ {u ∈ W | u ≠ t}, 1 / |u - t| := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hut : u = t
      · simp [hut]
      · simp [hut, abs_sub_comm]
    _ = ∑ u ∈ {u ∈ W | u ≠ t ∧
          |u - t| ≤ ((⌈J / G⌉₊ : ℕ) : ℝ) * G}, 1 / |u - t| := by
      rw [← hfilter]
    _ ≤ (2 / G) * (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)) := hsource

/-- Pointwise equation-(7.19) estimate using the actual maximum gap `J`. -/
theorem norm_heathBrownAtkinsonGram_le_equation719_source_split
    {K : ℕ} {T J t u : ℝ}
    (hT : 0 < T) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (ht : t ∈ Set.Icc (T / 2) T)
    (hu : u ∈ Set.Icc (T / 2) T) (htu : t ≠ u)
    (hgap : |t - u| ≤ J) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      heathBrownAtkinsonSourceFirstCoefficient T J K +
        heathBrownAtkinsonEquation719ReciprocalCoefficient T K /
          |t - u| := by
  have hsource := norm_heathBrownAtkinsonGram_le_equation719_uniform
    hT hK hblock ht hu htu
  have hsqrt : Real.sqrt |t - u| ≤ Real.sqrt J := Real.sqrt_le_sqrt hgap
  have hq : 0 < heathBrownAtkinsonQuarterScale (T / 2) K :=
    heathBrownAtkinsonQuarterScale_pos (half_pos hT)
  have hfirst :
      900 * Real.sqrt |t - u| /
          heathBrownAtkinsonQuarterScale (T / 2) K ≤
        heathBrownAtkinsonSourceFirstCoefficient T J K := by
    unfold heathBrownAtkinsonSourceFirstCoefficient
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) hq.le
  unfold heathBrownAtkinsonEquation719UniformMajorant at hsource
  unfold heathBrownAtkinsonSourceFirstCoefficient
    heathBrownAtkinsonEquation719ReciprocalCoefficient
  exact hsource.trans (add_le_add hfirst le_rfl)

/-- The complete source row majorant: diagonal, upper-gap B-process term,
and lower-spacing harmonic term remain separately visible. -/
def heathBrownAtkinsonSourceRowMajorant
    (T G J : ℝ) (K R : ℕ) : ℝ :=
  (K : ℝ) + (R : ℝ) * heathBrownAtkinsonSourceFirstCoefficient T J K +
    heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
      ((2 / G) * (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)))

theorem heathBrownAtkinsonSourceRowMajorant_nonneg
    {T G J : ℝ} {K R : ℕ} (hT : 0 < T) (hG : 0 < G)
    :
    0 ≤ heathBrownAtkinsonSourceRowMajorant T G J K R := by
  unfold heathBrownAtkinsonSourceRowMajorant
  have hhQ : 0 ≤ harmonic ⌈J / G⌉₊ := by
    rw [harmonic_eq_sum_Icc]
    positivity
  have hh : 0 ≤ (((harmonic ⌈J / G⌉₊ : ℚ) : ℝ)) := by
    exact_mod_cast hhQ
  have hfirst := heathBrownAtkinsonSourceFirstCoefficient_nonneg
    (J := J) (K := K) hT
  have hrec := heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg
    (K := K) hT
  have htwoG : 0 ≤ 2 / G := div_nonneg (by norm_num) hG.le
  exact add_nonneg
    (add_nonneg (by positivity) (mul_nonneg (by positivity) hfirst))
    (mul_nonneg hrec (mul_nonneg htwoG hh))

/-- One exact Gram row in the source's `G`-separated, `J`-bounded family. -/
theorem sum_norm_heathBrownAtkinsonGram_row_le_source
    {K : ℕ} {T G J t : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hG : 0 < G) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (ht : t ∈ W) (hSep : IsSeparated G W)
    (hRange : ∀ x ∈ W, x ∈ Set.Icc (T / 2) T)
    (hDiameter : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ J) :
    (∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
      heathBrownAtkinsonSourceRowMajorant T G J K W.card := by
  have hfirst := heathBrownAtkinsonSourceFirstCoefficient_nonneg
    (J := J) (K := K) hT
  have hpoint : ∀ u ∈ W,
      ‖heathBrownAtkinsonGram K t u‖ ≤
        (if u = t then (K : ℝ) else 0) +
          heathBrownAtkinsonSourceFirstCoefficient T J K +
          heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
            (if u = t then 0 else 1 / |t - u|) := by
    intro u hu
    by_cases hut : u = t
    · subst u
      rw [norm_heathBrownAtkinsonGram_self]
      simpa using (le_add_of_nonneg_right hfirst :
        (K : ℝ) ≤ (K : ℝ) +
          heathBrownAtkinsonSourceFirstCoefficient T J K)
    · simp only [if_neg hut, zero_add]
      have h := norm_heathBrownAtkinsonGram_le_equation719_source_split
        hT hK hblock (hRange t ht) (hRange u hu) (Ne.symm hut)
        (hDiameter t ht u hu)
      simpa only [div_eq_mul_inv, one_mul] using h
  calc
    (∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
        ∑ u ∈ W,
          ((if u = t then (K : ℝ) else 0) +
            heathBrownAtkinsonSourceFirstCoefficient T J K +
            heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
              (if u = t then 0 else 1 / |t - u|)) := by
      exact Finset.sum_le_sum fun u hu => hpoint u hu
    _ = (K : ℝ) + (W.card : ℝ) *
          heathBrownAtkinsonSourceFirstCoefficient T J K +
        heathBrownAtkinsonEquation719ReciprocalCoefficient T K *
          (∑ u ∈ W, if u = t then 0 else 1 / |t - u|) := by
      simp_rw [Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq', if_pos ht]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ heathBrownAtkinsonSourceRowMajorant T G J K W.card := by
      unfold heathBrownAtkinsonSourceRowMajorant
      have hrec := mul_le_mul_of_nonneg_left
        (sum_ite_inv_abs_sub_le_scaled_harmonic W hG ht hSep hDiameter)
        (heathBrownAtkinsonEquation719ReciprocalCoefficient_nonneg
          (K := K) hT)
      linarith

/-- Aggregate Bombieri--Halász conclusion underlying Ivić Lemma 7.1, valid
uniformly for every literal prefix `j ≤ K`. -/
theorem heathBrownAtkinson_lemma71_source_squared
    {K j : ℕ} {T G J : ℝ} {W : Finset ℝ}
    (hT : 0 < T) (hG : 0 < G) (hK : 0 < K)
    (hj : j ≤ K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (hSep : IsSeparated G W)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hDiameter : ∀ t ∈ W, ∀ u ∈ W, |t - u| ≤ J) :
    (∑ t ∈ W, ‖heathBrownAtkinsonSum (j : ℝ) K t‖) ^ (2 : ℕ) ≤
      heathBrownAtkinsonEnergy K * (W.card : ℝ) *
        heathBrownAtkinsonSourceRowMajorant T G J K W.card := by
  have hGram := heathBrownAtkinson_prefix_aggregate_halasz_gram
    (W := W) hj
  have hrows :
      (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
        (W.card : ℝ) *
          heathBrownAtkinsonSourceRowMajorant T G J K W.card := by
    calc
      _ ≤ ∑ _t ∈ W,
          heathBrownAtkinsonSourceRowMajorant T G J K W.card := by
        exact Finset.sum_le_sum fun t ht =>
          sum_norm_heathBrownAtkinsonGram_row_le_source
            hT hG hK hblock ht hSep hRange hDiameter
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hmul := mul_le_mul_of_nonneg_left hrows
    (heathBrownAtkinsonEnergy_nonneg K)
  exact hGram.trans (by
    calc
      heathBrownAtkinsonEnergy K *
          (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
          heathBrownAtkinsonEnergy K *
            ((W.card : ℝ) *
              heathBrownAtkinsonSourceRowMajorant T G J K W.card) := hmul
      _ = _ := by ring)


end

end GafniTao
