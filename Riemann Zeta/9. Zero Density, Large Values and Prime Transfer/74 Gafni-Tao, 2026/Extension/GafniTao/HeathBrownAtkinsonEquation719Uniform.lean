import GafniTao.HeathBrownAtkinsonEquation719
import RiemannZeta.GuthMaynard.ClassicalLargeValues

/-!
# Uniform dyadic form of Ivić (7.19)

This file converts the ordered exact estimate to the symmetric form used in
the Bombieri--Halász summation.  The height interval is kept half-closed only
at later consumers; the estimate itself is valid on the closed dyadic box.
-/

open Complex Finset Set
open scoped BigOperators

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem heathBrownAtkinsonQuarterScale_mono
    {a b : ℝ} {K : ℕ} (hab : a ≤ b) :
    heathBrownAtkinsonQuarterScale a K ≤
      heathBrownAtkinsonQuarterScale b K := by
  unfold heathBrownAtkinsonQuarterScale
  gcongr

/-- The source-shaped majorant after replacing both heights by their common
dyadic scale `T`. -/
def heathBrownAtkinsonEquation719UniformMajorant
    (T : ℝ) (K : ℕ) (d : ℝ) : ℝ :=
  900 * Real.sqrt d / heathBrownAtkinsonQuarterScale (T / 2) K +
    28 * Real.sqrt (T * (K + 1 : ℕ)) / d

theorem heathBrownAtkinsonEquation719UniformMajorant_nonneg
    {T d : ℝ} {K : ℕ} (hT : 0 < T) (hd : 0 < d) :
    0 ≤ heathBrownAtkinsonEquation719UniformMajorant T K d := by
  unfold heathBrownAtkinsonEquation719UniformMajorant
  have hq : 0 < heathBrownAtkinsonQuarterScale (T / 2) K :=
    heathBrownAtkinsonQuarterScale_pos (half_pos hT)
  exact add_nonneg (div_nonneg (by positivity) hq.le)
    (div_nonneg (by positivity) hd.le)

/-- Uniform ordered form on a dyadic height box. -/
theorem norm_heathBrownAtkinsonGram_le_equation719_uniform_of_lt
    {K : ℕ} {T t u : ℝ}
    (hT : 0 < T) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (ht : t ∈ Set.Icc (T / 2) T)
    (hu : u ∈ Set.Icc (T / 2) T) (hut : u < t) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      heathBrownAtkinsonEquation719UniformMajorant T K (t - u) := by
  have huPos : 0 < u := lt_of_lt_of_le (half_pos hT) hu.1
  have hgap : 0 < t - u := sub_pos.mpr hut
  have htTwo : t ≤ 2 * u := by linarith [ht.2, hu.1]
  have hsource := norm_heathBrownAtkinsonGram_le_equation719
    huPos hut hK (hblock.trans hu.1) htTwo
  have hquarter := heathBrownAtkinsonQuarterScale_mono (K := K) hu.1
  have hquarterHalf : 0 < heathBrownAtkinsonQuarterScale (T / 2) K :=
    heathBrownAtkinsonQuarterScale_pos (half_pos hT)
  have hfirst :
      900 * Real.sqrt (t - u) / heathBrownAtkinsonQuarterScale u K ≤
        900 * Real.sqrt (t - u) /
          heathBrownAtkinsonQuarterScale (T / 2) K := by
    exact div_le_div_of_nonneg_left (by positivity) hquarterHalf hquarter
  have hmul : u * ((K + 1 : ℕ) : ℝ) ≤
      T * ((K + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hu.2 (by positivity)
  have hsqrtMul : Real.sqrt (u * (K + 1 : ℕ)) ≤
      Real.sqrt (T * (K + 1 : ℕ)) := Real.sqrt_le_sqrt hmul
  have hsecond :
      28 * Real.sqrt (u * (K + 1 : ℕ)) / (t - u) ≤
        28 * Real.sqrt (T * (K + 1 : ℕ)) / (t - u) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrtMul
      (by norm_num : (0 : ℝ) ≤ 28)) hgap.le
  unfold heathBrownAtkinsonEquation719UniformMajorant
  nlinarith [hsource, hfirst, hsecond]

/-- Symmetric dyadic form of Ivić (7.19). -/
theorem norm_heathBrownAtkinsonGram_le_equation719_uniform
    {K : ℕ} {T t u : ℝ}
    (hT : 0 < T) (hK : 0 < K)
    (hblock : (((2 * K + 2 : ℕ) : ℝ)) ≤ T / 2)
    (ht : t ∈ Set.Icc (T / 2) T)
    (hu : u ∈ Set.Icc (T / 2) T) (htu : t ≠ u) :
    ‖heathBrownAtkinsonGram K t u‖ ≤
      heathBrownAtkinsonEquation719UniformMajorant T K |t - u| := by
  rcases lt_or_gt_of_ne htu with hlt | hgt
  · have h := norm_heathBrownAtkinsonGram_le_equation719_uniform_of_lt
      hT hK hblock hu ht hlt
    rw [heathBrownAtkinsonGram_swap, norm_star] at h
    simpa only [abs_of_neg (sub_neg.mpr hlt), neg_sub] using h
  · have h := norm_heathBrownAtkinsonGram_le_equation719_uniform_of_lt
      hT hK hblock ht hu hgt
    simpa only [abs_of_pos (sub_pos.mpr hgt)] using h


end

end GafniTao
