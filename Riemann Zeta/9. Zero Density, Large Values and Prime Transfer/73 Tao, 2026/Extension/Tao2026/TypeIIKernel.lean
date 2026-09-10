import Tao2026.TypeIIReduction
import Tao2026.ShortIntervalDecomposition

/-!
# Type II distance-kernel combinatorics

The off-diagonal estimate in the pinned source is summed as a function of
`|n-n'|`.  This module supplies the exact finite regrouping by natural
distance and the sharp two-point bound for each distance fiber.  No
exponential-sum estimate is assumed.
-/

open Finset
open scoped BigOperators

namespace Tao2026

/-- Members of a finite support lying at a fixed natural distance from a
chosen center. -/
def natDistFiber (S : Finset ℕ) (center d : ℕ) : Finset ℕ :=
  S.filter (fun n => Nat.dist n center = d)

theorem mem_natDistFiber {S : Finset ℕ} {center d n : ℕ} :
    n ∈ natDistFiber S center d ↔ n ∈ S ∧ Nat.dist n center = d := by
  simp [natDistFiber]

/-- On the natural line, a fixed distance from one center has at most two
solutions, independently of the ambient finite support. -/
theorem card_natDistFiber_le_two (S : Finset ℕ) (center d : ℕ) :
    (natDistFiber S center d).card ≤ 2 := by
  have hsub : natDistFiber S center d ⊆ {center + d, center - d} := by
    intro n hn
    rw [mem_natDistFiber] at hn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases le_total n center with hnc | hcn
    · right
      rw [Nat.dist_eq_sub_of_le hnc] at hn
      omega
    · left
      rw [Nat.dist_eq_sub_of_le_right hcn] at hn
      omega
  calc
    (natDistFiber S center d).card ≤ ({center + d, center - d} : Finset ℕ).card :=
      Finset.card_le_card hsub
    _ ≤ ({center - d} : Finset ℕ).card + 1 :=
      Finset.card_insert_le _ _
    _ = 2 := by simp

/-- Exact regrouping of a finite sum by distance, provided `D` bounds all
distances occurring on the support. -/
theorem sum_eq_sum_natDistFibers
    {A : Type*} [AddCommMonoid A] (S : Finset ℕ) (center D : ℕ)
    (f : ℕ → A) (hD : ∀ n ∈ S, Nat.dist n center ≤ D) :
    ∑ n ∈ S, f (Nat.dist n center) =
      ∑ d ∈ Finset.range (D + 1),
        (natDistFiber S center d).card • f d := by
  calc
    ∑ n ∈ S, f (Nat.dist n center) =
        ∑ d ∈ Finset.range (D + 1),
          ∑ n ∈ natDistFiber S center d, f (Nat.dist n center) := by
      simpa only [natDistFiber] using
        (Finset.sum_fiberwise_of_maps_to
          (fun n hn => Finset.mem_range.mpr (Nat.lt_succ_of_le (hD n hn)))
          (fun n => f (Nat.dist n center))).symm
    _ = ∑ d ∈ Finset.range (D + 1),
        (natDistFiber S center d).card • f d := by
      apply Finset.sum_congr rfl
      intro d _hd
      calc
        ∑ n ∈ natDistFiber S center d, f (Nat.dist n center) =
            ∑ _n ∈ natDistFiber S center d, f d := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [(mem_natDistFiber.mp hn).2]
        _ = (natDistFiber S center d).card • f d := by
          rw [Finset.sum_const]

/-- Regrouping by distance costs at most the sharp multiplicity factor two
for any nonnegative real kernel. -/
theorem sum_natDistKernel_le_two_mul_sum
    (S : Finset ℕ) (center D : ℕ) (f : ℕ → ℝ)
    (hf : ∀ d, 0 ≤ f d) (hD : ∀ n ∈ S, Nat.dist n center ≤ D) :
    ∑ n ∈ S, f (Nat.dist n center) ≤
      2 * ∑ d ∈ Finset.range (D + 1), f d := by
  rw [sum_eq_sum_natDistFibers S center D f hD]
  calc
    ∑ d ∈ Finset.range (D + 1),
        (natDistFiber S center d).card • f d ≤
        ∑ d ∈ Finset.range (D + 1), 2 * f d := by
      apply Finset.sum_le_sum
      intro d _hd
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_natDistFiber_le_two S center d) (hf d)
    _ = 2 * ∑ d ∈ Finset.range (D + 1), f d := by
      rw [Finset.mul_sum]

/-- After erasing the center, the zero-distance fiber is empty. -/
@[simp]
theorem natDistFiber_erase_center_zero (S : Finset ℕ) (center : ℕ) :
    natDistFiber (S.erase center) center 0 = ∅ := by
  ext n
  rw [mem_natDistFiber, Finset.mem_erase]
  constructor
  · rintro ⟨⟨hne, _hnS⟩, hdist⟩
    exact (hne (Nat.eq_of_dist_eq_zero hdist)).elim
  · intro hn
    simp at hn

/-- The off-diagonal distance regrouping starts at distance one. Consequently
the sharp multiplicity-two loss applies only to the positive-distance sum. -/
theorem sum_natDistKernel_erase_le_two_mul_sum_pos
    (S : Finset ℕ) (center D : ℕ) (f : ℕ → ℝ)
    (hf : ∀ d, 0 ≤ f d) (hD : ∀ n ∈ S, Nat.dist n center ≤ D) :
    ∑ n ∈ S.erase center, f (Nat.dist n center) ≤
      2 * ∑ k ∈ Finset.range D, f (k + 1) := by
  have hDerase : ∀ n ∈ S.erase center, Nat.dist n center ≤ D := by
    intro n hn
    exact hD n (Finset.mem_of_mem_erase hn)
  rw [sum_eq_sum_natDistFibers (S.erase center) center D f hDerase]
  rw [Finset.sum_range_succ']
  simp only [natDistFiber_erase_center_zero, Finset.card_empty, zero_nsmul,
    add_zero]
  calc
    ∑ k ∈ Finset.range D,
        (natDistFiber (S.erase center) center (k + 1)).card • f (k + 1) ≤
        ∑ k ∈ Finset.range D, 2 * f (k + 1) := by
      apply Finset.sum_le_sum
      intro k _hk
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_natDistFiber_le_two (S.erase center) center (k + 1))
        (hf (k + 1))
    _ = 2 * ∑ k ∈ Finset.range D, f (k + 1) := by
      rw [Finset.mul_sum]

/-- The one-dimensional decay kernel occurring after the source's Type II
correlation estimate. -/
noncomputable def typeIIDecayKernel (R F c : ℝ) (d : ℕ) : ℝ :=
  (1 + (d : ℝ) * F / R) ^ (-c)

/-- Real-variable extension of `typeIIDecayKernel`, used for the integral
comparison. -/
noncomputable def typeIIDecayKernelReal (R F c x : ℝ) : ℝ :=
  (1 + x * F / R) ^ (-c)

theorem typeIIDecayKernel_eq_real (R F c : ℝ) (d : ℕ) :
    typeIIDecayKernel R F c d = typeIIDecayKernelReal R F c d :=
  rfl

theorem typeIIDecayKernel_nonneg {R F : ℝ} (c : ℝ) (d : ℕ)
    (hR : 0 < R) (hF : 0 ≤ F) :
    0 ≤ typeIIDecayKernel R F c d := by
  apply Real.rpow_nonneg
  have hterm : 0 ≤ (d : ℝ) * F / R :=
    div_nonneg (mul_nonneg (by positivity) hF) hR.le
  have hone : (1 : ℝ) ≤ 1 + (d : ℝ) * F / R := le_add_of_nonneg_right hterm
  exact zero_le_one.trans hone

/-- At source distance at most three, the tiny `1/1024` exponent leaves a
uniformly positive kernel.  This is the quantitative input for handling
nearby Type II correlations by the trivial sum bound instead of imposing a
false large-transformed-scale hypothesis. -/
theorem one_div_four_le_typeIIDecayKernel_of_scaledDistance_le_three
    {R F : ℝ} (d : ℕ) (hR : 0 < R) (hF : 0 ≤ F)
    (hnear : (d : ℝ) * F / R ≤ 3) :
    1 / 4 ≤ typeIIDecayKernel R F (1 / 1024 : ℝ) d := by
  let x : ℝ := (d : ℝ) * F / R
  have hx0 : 0 ≤ x := by unfold x; positivity
  have hx3 : x ≤ 3 := by simpa only [x] using hnear
  have hbaseOne : (1 : ℝ) ≤ 1 + x := by linarith
  have hbaseFour : 1 + x ≤ (4 : ℝ) := by linarith
  have hinv : 1 / (4 : ℝ) ≤ 1 / (1 + x) :=
    one_div_le_one_div_of_le (by positivity) hbaseFour
  have hrpow : (1 + x) ^ (-1 : ℝ) ≤
      (1 + x) ^ (-(1 / 1024 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hbaseOne (by norm_num)
  calc
    1 / 4 ≤ 1 / (1 + x) := hinv
    _ = (1 + x) ^ (-1 : ℝ) := by
      simp only [one_div, Real.rpow_neg_one]
    _ ≤ (1 + x) ^ (-(1 / 1024 : ℝ)) := hrpow
    _ = typeIIDecayKernel R F (1 / 1024 : ℝ) d := by
      rfl

@[simp]
theorem typeIIDecayKernel_zero (R F c : ℝ) :
    typeIIDecayKernel R F c 0 = 1 := by
  simp [typeIIDecayKernel]

/-- The source decay kernel is antitone in the natural distance. -/
theorem antitone_typeIIDecayKernel
    {R F c : ℝ} (hR : 0 < R) (hF : 0 ≤ F) (hc : 0 ≤ c) :
    Antitone (typeIIDecayKernel R F c) := by
  intro d e hde
  apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hc)
  · have : 0 ≤ (d : ℝ) * F / R := div_nonneg (mul_nonneg (by positivity) hF) hR.le
    exact zero_lt_one.trans_le (le_add_of_nonneg_right this)
  · have : 0 ≤ (e : ℝ) * F / R := div_nonneg (mul_nonneg (by positivity) hF) hR.le
    exact zero_lt_one.trans_le (le_add_of_nonneg_right this)
  · have hcast : (d : ℝ) ≤ e := by exact_mod_cast hde
    simpa [add_comm] using add_le_add_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcast hF) hR.le) 1

/-- The real extension is antitone on the nonnegative half-line. -/
theorem antitoneOn_typeIIDecayKernelReal
    {R F c : ℝ} (hR : 0 < R) (hF : 0 ≤ F) (hc : 0 ≤ c) :
    AntitoneOn (typeIIDecayKernelReal R F c) (Set.Ici 0) := by
  intro x hx y hy hxy
  apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (neg_nonpos.mpr hc)
  · have hterm : 0 ≤ x * F / R :=
      div_nonneg (mul_nonneg hx hF) hR.le
    exact zero_lt_one.trans_le (le_add_of_nonneg_right hterm)
  · have hterm : 0 ≤ y * F / R :=
      div_nonneg (mul_nonneg hy hF) hR.le
    exact zero_lt_one.trans_le (le_add_of_nonneg_right hterm)
  · simpa [typeIIDecayKernelReal, add_comm] using add_le_add_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hxy hF) hR.le) 1

/-- First quantitative reduction of the discrete decay sum: its nonzero
terms are bounded by the corresponding real integral. -/
theorem sum_typeIIDecayKernel_le_one_add_integral
    {R F c : ℝ} (D : ℕ) (hR : 0 < R) (hF : 0 ≤ F) (hc : 0 ≤ c) :
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
      1 + ∫ x in (0 : ℝ)..D, typeIIDecayKernelReal R F c x := by
  have hanti : AntitoneOn (typeIIDecayKernelReal R F c)
      (Set.Icc (0 : ℝ) D) :=
    (antitoneOn_typeIIDecayKernelReal hR hF hc).mono Set.Icc_subset_Ici_self
  have hanti' : AntitoneOn (typeIIDecayKernelReal R F c)
      (Set.Icc (0 : ℝ) (0 + (D : ℝ))) := by
    simpa using hanti
  have hint := hanti'.sum_le_integral
  rw [Finset.sum_range_succ']
  rw [typeIIDecayKernel_zero]
  calc
    (∑ k ∈ Finset.range D, typeIIDecayKernel R F c (k + 1)) + 1 =
        1 + ∑ k ∈ Finset.range D, typeIIDecayKernel R F c (k + 1) :=
      add_comm _ _
    _ ≤ 1 + ∫ x in (0 : ℝ)..D, typeIIDecayKernelReal R F c x := by
      apply add_le_add_right
      simpa only [typeIIDecayKernel_eq_real, Nat.cast_zero, zero_add,
        Nat.cast_add, Nat.cast_one] using hint

/-- The positive-distance kernel sum has no endpoint term and is bounded
directly by the matching integral. -/
theorem sum_typeIIDecayKernel_pos_le_integral
    {R F c : ℝ} (D : ℕ) (hR : 0 < R) (hF : 0 ≤ F) (hc : 0 ≤ c) :
    ∑ k ∈ Finset.range D, typeIIDecayKernel R F c (k + 1) ≤
      ∫ x in (0 : ℝ)..D, typeIIDecayKernelReal R F c x := by
  have hanti : AntitoneOn (typeIIDecayKernelReal R F c)
      (Set.Icc (0 : ℝ) D) :=
    (antitoneOn_typeIIDecayKernelReal hR hF hc).mono Set.Icc_subset_Ici_self
  have hanti' : AntitoneOn (typeIIDecayKernelReal R F c)
      (Set.Icc (0 : ℝ) (0 + (D : ℝ))) := by
    simpa using hanti
  simpa only [typeIIDecayKernel_eq_real, Nat.cast_zero, zero_add,
    Nat.cast_add, Nat.cast_one] using hanti'.sum_le_integral

/-- Closed-form antiderivative used to evaluate the Type II decay-kernel
integral when `F>0` and `c≠1`. -/
noncomputable def typeIIDecayAntiderivative (R F c x : ℝ) : ℝ :=
  (1 + x * F / R) ^ (1 - c) / ((F / R) * (1 - c))

theorem hasDerivAt_typeIIDecayAntiderivative
    {R F c x : ℝ} (hR : 0 < R) (hF : 0 < F) (hc : c ≠ 1)
    (hx : 0 ≤ x) :
    HasDerivAt (typeIIDecayAntiderivative R F c)
      (typeIIDecayKernelReal R F c x) x := by
  have hinner : HasDerivAt (fun y : ℝ => 1 + y * F / R) (F / R) x := by
    convert (hasDerivAt_const x 1).add
      (((hasDerivAt_id x).mul_const F).div_const R) using 1
    all_goals ring
  have hbasePos : 0 < 1 + x * F / R := by
    have hterm : 0 ≤ x * F / R :=
      div_nonneg (mul_nonneg hx hF.le) hR.le
    exact zero_lt_one.trans_le (le_add_of_nonneg_right hterm)
  have hp := hinner.rpow_const (p := 1 - c) (Or.inl hbasePos.ne')
  convert hp.div_const ((F / R) * (1 - c)) using 1
  rw [show (1 - c) - 1 = -c by ring]
  dsimp only [typeIIDecayKernelReal]
  field_simp [hR.ne', hF.ne', sub_ne_zero.mpr hc]

/-- Exact evaluation of the decay-kernel integral by the preceding
antiderivative. -/
theorem integral_typeIIDecayKernelReal
    {R F c D : ℝ} (hR : 0 < R) (hF : 0 < F)
    (hc0 : 0 ≤ c) (hc : c < 1) (hD : 0 ≤ D) :
    ∫ x in (0 : ℝ)..D, typeIIDecayKernelReal R F c x =
      typeIIDecayAntiderivative R F c D -
        typeIIDecayAntiderivative R F c 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hD
  · intro x hx
    exact (hasDerivAt_typeIIDecayAntiderivative hR hF hc.ne hx.1).continuousAt.continuousWithinAt
  · intro x hx
    exact hasDerivAt_typeIIDecayAntiderivative hR hF hc.ne hx.1.le
  · have hanti : AntitoneOn (typeIIDecayKernelReal R F c)
        (Set.uIcc 0 D) := by
      rw [Set.uIcc_of_le hD]
      exact (antitoneOn_typeIIDecayKernelReal hR hF.le hc0).mono
        Set.Icc_subset_Ici_self
    exact hanti.intervalIntegrable

/-- Closed-form upper bound for the finite distance-kernel sum. -/
theorem sum_typeIIDecayKernel_le_antiderivative
    {R F c : ℝ} (D : ℕ) (hR : 0 < R) (hF : 0 < F)
    (hc0 : 0 ≤ c) (hc : c < 1) :
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
      1 + (typeIIDecayAntiderivative R F c D -
        typeIIDecayAntiderivative R F c 0) := by
  calc
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
        1 + ∫ x in (0 : ℝ)..D, typeIIDecayKernelReal R F c x :=
      sum_typeIIDecayKernel_le_one_add_integral D hR hF.le hc0
    _ = _ := by
      rw [integral_typeIIDecayKernelReal hR hF hc0 hc (Nat.cast_nonneg D)]

theorem typeIIDecayAntiderivative_zero_nonneg
    {R F c : ℝ} (hR : 0 < R) (hF : 0 < F) (hc : c < 1) :
    0 ≤ typeIIDecayAntiderivative R F c 0 := by
  unfold typeIIDecayAntiderivative
  apply div_nonneg
  · positivity
  · exact mul_nonneg (div_nonneg hF.le hR.le) (sub_nonneg.mpr hc.le)

/-- The lower endpoint in the exact antiderivative formula is nonnegative,
so it can be discarded in an upper bound. -/
theorem sum_typeIIDecayKernel_le_one_add_antiderivative
    {R F c : ℝ} (D : ℕ) (hR : 0 < R) (hF : 0 < F)
    (hc0 : 0 ≤ c) (hc : c < 1) :
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
      1 + typeIIDecayAntiderivative R F c D := by
  calc
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
        1 + (typeIIDecayAntiderivative R F c D -
          typeIIDecayAntiderivative R F c 0) :=
      sum_typeIIDecayKernel_le_antiderivative D hR hF hc0 hc
    _ ≤ 1 + typeIIDecayAntiderivative R F c D := by
      linarith [typeIIDecayAntiderivative_zero_nonneg hR hF hc]

/-- Algebraic normalization of the antiderivative coefficient. -/
theorem typeIIDecayAntiderivative_eq_scale
    {R F c x : ℝ} (hR : R ≠ 0) (hF : F ≠ 0) (hc : c ≠ 1) :
    typeIIDecayAntiderivative R F c x =
      R / (F * (1 - c)) * (1 + x * F / R) ^ (1 - c) := by
  unfold typeIIDecayAntiderivative
  field_simp [hR, hF, sub_ne_zero.mpr hc]

/-- If the distance range is at most `R` and `F≥1`, the antiderivative is
controlled by the source-scale power `(2F)^(1-c)`. -/
theorem typeIIDecayAntiderivative_le_two_mul_frequency
    {R F c : ℝ} (D : ℕ) (hR : 0 < R) (hF : 1 ≤ F)
    (hc : c < 1) (hD : (D : ℝ) ≤ R) :
    typeIIDecayAntiderivative R F c D ≤
      R / (F * (1 - c)) * (2 * F) ^ (1 - c) := by
  rw [typeIIDecayAntiderivative_eq_scale hR.ne' (zero_lt_one.trans_le hF).ne' hc.ne]
  have hratio : (D : ℝ) * F / R ≤ F := by
    calc
      (D : ℝ) * F / R ≤ R * F / R :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hD (zero_le_one.trans hF)) hR.le
      _ = F := by field_simp [hR.ne']
  have hbase : 1 + (D : ℝ) * F / R ≤ 2 * F := by
    linarith
  have hpow : (1 + (D : ℝ) * F / R) ^ (1 - c) ≤
      (2 * F) ^ (1 - c) :=
    Real.rpow_le_rpow (by positivity) hbase (sub_nonneg.mpr hc.le)
  exact mul_le_mul_of_nonneg_left hpow
    (div_nonneg hR.le
      (mul_nonneg (zero_le_one.trans hF) (sub_nonneg.mpr hc.le)))

/-- Exact normalization of the preceding majorant to `R * F^(-c)`, with
an explicit constant depending only on `c`. -/
theorem typeIIDecay_scale_identity
    {R F c : ℝ} (hF : 0 < F) :
    R / (F * (1 - c)) * (2 * F) ^ (1 - c) =
      (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c) := by
  calc
    R / (F * (1 - c)) * (2 * F) ^ (1 - c) =
        (2 ^ (1 - c) / (1 - c)) * R * (F ^ (1 - c) / F) := by
      rw [Real.mul_rpow (by norm_num) hF.le]
      field_simp [hF.ne']
    _ = (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c) := by
      rw [← Real.rpow_sub_one hF.ne' (1 - c)]
      congr 2
      ring

/-- The actual off-diagonal kernel sum has the pure source scale without any
endpoint hypothesis: erasing the center removes distance zero before the
sum--integral comparison. -/
theorem sum_typeIIDecayKernel_erase_le_sourceScale
    (S : Finset ℕ) (center D : ℕ) {R F c : ℝ}
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hDnat : ∀ n ∈ S, Nat.dist n center ≤ D) (hD : (D : ℝ) ≤ R) :
    ∑ n ∈ S.erase center,
        typeIIDecayKernel R F c (Nat.dist n center) ≤
      2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) := by
  have hFpos : 0 < F := zero_lt_one.trans_le hF
  calc
    ∑ n ∈ S.erase center,
        typeIIDecayKernel R F c (Nat.dist n center) ≤
        2 * ∑ k ∈ Finset.range D, typeIIDecayKernel R F c (k + 1) :=
      sum_natDistKernel_erase_le_two_mul_sum_pos S center D
        (typeIIDecayKernel R F c)
        (fun d => typeIIDecayKernel_nonneg c d hR hFpos.le) hDnat
    _ ≤ 2 * (∫ x in (0 : ℝ)..D, typeIIDecayKernelReal R F c x) :=
      mul_le_mul_of_nonneg_left
        (sum_typeIIDecayKernel_pos_le_integral D hR hFpos.le hc0) (by norm_num)
    _ = 2 * (typeIIDecayAntiderivative R F c D -
        typeIIDecayAntiderivative R F c 0) := by
      rw [integral_typeIIDecayKernelReal hR hFpos hc0 hc (Nat.cast_nonneg D)]
    _ ≤ 2 * typeIIDecayAntiderivative R F c D := by
      have hzero := typeIIDecayAntiderivative_zero_nonneg hR hFpos hc
      linarith
    _ ≤ 2 * (R / (F * (1 - c)) * (2 * F) ^ (1 - c)) := by
      gcongr
      exact typeIIDecayAntiderivative_le_two_mul_frequency D hR hF hc hD
    _ = 2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) := by
      rw [typeIIDecay_scale_identity hFpos]

/-- The finite source kernel sum has the required `R * F^(-c)` scale, up to
the endpoint `1` and an explicit constant depending only on `c`. -/
theorem sum_typeIIDecayKernel_le_one_add_sourceScale
    {R F c : ℝ} (D : ℕ) (hR : 0 < R) (hF : 1 ≤ F)
    (hc0 : 0 ≤ c) (hc : c < 1) (hD : (D : ℝ) ≤ R) :
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
      1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c) := by
  calc
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
        1 + typeIIDecayAntiderivative R F c D :=
      sum_typeIIDecayKernel_le_one_add_antiderivative D hR
        (zero_lt_one.trans_le hF) hc0 hc
    _ ≤ 1 + R / (F * (1 - c)) * (2 * F) ^ (1 - c) :=
      add_le_add_right
        (typeIIDecayAntiderivative_le_two_mul_frequency D hR hF hc hD) 1
    _ = _ := by rw [typeIIDecay_scale_identity (zero_lt_one.trans_le hF)]

/-- The distance-zero term is present in every nonempty initial kernel sum.
Consequently, a pure `R * F^(-c)` majorant must itself dominate `1`. -/
theorem one_le_sum_typeIIDecayKernel
    {R F c : ℝ} (D : ℕ) (hR : 0 < R) (hF : 0 ≤ F) :
    1 ≤ ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d := by
  calc
    1 = typeIIDecayKernel R F c 0 := (typeIIDecayKernel_zero R F c).symm
    _ ≤ ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d := by
      exact Finset.single_le_sum
        (s := Finset.range (D + 1)) (f := typeIIDecayKernel R F c)
        (fun d _ => typeIIDecayKernel_nonneg c d hR hF) (by simp)

/-- Unconditional finite-support version of the decay estimate.  The additive
`1` is forced by the distance-zero term and is retained explicitly. -/
theorem sum_typeIIDecayKernel_natDist_le_one_add_sourceScale
    (S : Finset ℕ) (center D : ℕ) {R F c : ℝ}
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hDnat : ∀ n ∈ S, Nat.dist n center ≤ D) (hD : (D : ℝ) ≤ R) :
    ∑ n ∈ S, typeIIDecayKernel R F c (Nat.dist n center) ≤
      2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) := by
  calc
    ∑ n ∈ S, typeIIDecayKernel R F c (Nat.dist n center) ≤
        2 * ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d :=
      sum_natDistKernel_le_two_mul_sum S center D
        (typeIIDecayKernel R F c)
        (fun d => typeIIDecayKernel_nonneg c d hR (zero_le_one.trans hF)) hDnat
    _ ≤ 2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) :=
      mul_le_mul_of_nonneg_left
        (sum_typeIIDecayKernel_le_one_add_sourceScale D hR hF hc0 hc hD)
        (by norm_num)

/-- Any proposed pure source-scale upper bound necessarily dominates the
distance-zero endpoint. -/
theorem one_le_sourceScale_of_sum_typeIIDecayKernel_le
    {R F c C : ℝ} (D : ℕ) (hR : 0 < R) (hF : 0 ≤ F)
    (hbound : ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
      C * R * F ^ (-c)) :
    1 ≤ C * R * F ^ (-c) :=
  (one_le_sum_typeIIDecayKernel D hR hF).trans hbound

/-- Once the zero-distance endpoint is no larger than the source scale, the
finite kernel sum has a pure `R * F^(-c)` bound with an explicit constant. -/
theorem sum_typeIIDecayKernel_le_sourceScale
    {R F c : ℝ} (D : ℕ) (hR : 0 < R) (hF : 1 ≤ F)
    (hc0 : 0 ≤ c) (hc : c < 1) (hD : (D : ℝ) ≤ R)
    (hscale : 1 ≤ R * F ^ (-c)) :
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
      (1 + 2 ^ (1 - c) / (1 - c)) * R * F ^ (-c) := by
  let K : ℝ := 2 ^ (1 - c) / (1 - c)
  have hK : 0 ≤ K :=
    div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hc.le)
  calc
    ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d ≤
        1 + K * R * F ^ (-c) := by
      simpa [K] using
        sum_typeIIDecayKernel_le_one_add_sourceScale D hR hF hc0 hc hD
    _ ≤ (1 + K) * R * F ^ (-c) := by
      have hnonneg : 0 ≤ K * (R * F ^ (-c) - 1) :=
        mul_nonneg hK (sub_nonneg.mpr hscale)
      nlinarith
    _ = (1 + 2 ^ (1 - c) / (1 - c)) * R * F ^ (-c) := by
      rfl

/-- Full finite-support form of the source's one-dimensional correlation
kernel estimate.  Regrouping by natural distance contributes only the sharp
factor two, and the remaining kernel sum is on the `R * F^(-c)` scale. -/
theorem sum_typeIIDecayKernel_natDist_le_sourceScale
    (S : Finset ℕ) (center D : ℕ) {R F c : ℝ}
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hDnat : ∀ n ∈ S, Nat.dist n center ≤ D) (hD : (D : ℝ) ≤ R)
    (hscale : 1 ≤ R * F ^ (-c)) :
    ∑ n ∈ S, typeIIDecayKernel R F c (Nat.dist n center) ≤
      2 * ((1 + 2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) := by
  calc
    ∑ n ∈ S, typeIIDecayKernel R F c (Nat.dist n center) ≤
        2 * ∑ d ∈ Finset.range (D + 1), typeIIDecayKernel R F c d :=
      sum_natDistKernel_le_two_mul_sum S center D
        (typeIIDecayKernel R F c)
        (fun d => typeIIDecayKernel_nonneg c d hR (zero_le_one.trans hF)) hDnat
    _ ≤ 2 * ((1 + 2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) :=
      mul_le_mul_of_nonneg_left
        (sum_typeIIDecayKernel_le_sourceScale D hR hF hc0 hc hD hscale)
        (by norm_num)

/-- A source-shaped pointwise correlation estimate is summed without replacing
the decay kernel by a uniform worst-case bound.  The additive error is counted
exactly over the ordered off-diagonal pairs. -/
theorem sum_norm_typeIIProductRestrictedCorrelationSum_offDiagonal_le_decayKernel
    (I K S : Finset ℕ) (N M : ℝ) (j D : ℕ) {Q A E R F c : ℝ}
    (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hDnat : ∀ n ∈ S, ∀ n' ∈ S, Nat.dist n' n ≤ D)
    (hD : (D : ℝ) ≤ R)
    (hX : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
      (S.card : ℝ) *
        (Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          ((S.card - 1 : ℕ) : ℝ) * E)) := by
  have hinner : ∀ n ∈ S,
      ∑ n' ∈ S.erase n,
          ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          ((S.card - 1 : ℕ) : ℝ) * E) := by
    intro n hn
    calc
      ∑ n' ∈ S.erase n,
          ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
          ∑ n' ∈ S.erase n,
          Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E) := by
        apply Finset.sum_le_sum
        intro n' hn'
        have hn'data := Finset.mem_erase.mp hn'
        exact hX n hn n' hn'data.2 hn'data.1.symm
      _ = Q * (A * (∑ n' ∈ S.erase n,
            typeIIDecayKernel R F c (Nat.dist n' n)) +
          (((S.erase n).card : ℕ) : ℝ) * E) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
      _ ≤ Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          (((S.erase n).card : ℕ) : ℝ) * E) := by
        apply mul_le_mul_of_nonneg_left _ hQ
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_left
          (sum_typeIIDecayKernel_natDist_le_one_add_sourceScale
            (S.erase n) n D hR hF hc0 hc
            (fun n' hn' => hDnat n hn n' (Finset.mem_of_mem_erase hn')) hD) hA
      _ = Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          ((S.card - 1 : ℕ) : ℝ) * E) := by
        rw [Finset.card_erase_of_mem hn]
  calc
    ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        ∑ _n ∈ S,
          Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            ((S.card - 1 : ℕ) : ℝ) * E) :=
      Finset.sum_le_sum hinner
    _ = _ := by simp

/-- Strengthened off-diagonal correlation sum. Because the center is erased
before the kernel is summed, the decay term has the pure `R * F^(-c)` source
scale with no endpoint-absorption hypothesis. -/
theorem sum_norm_typeIIProductRestrictedCorrelationSum_offDiagonal_le_sourceScale
    (I K S : Finset ℕ) (N M : ℝ) (j D : ℕ) {Q A E R F c : ℝ}
    (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hDnat : ∀ n ∈ S, ∀ n' ∈ S, Nat.dist n' n ≤ D)
    (hD : (D : ℝ) ≤ R)
    (hX : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
      (S.card : ℝ) *
        (Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          ((S.card - 1 : ℕ) : ℝ) * E)) := by
  have hinner : ∀ n ∈ S,
      ∑ n' ∈ S.erase n,
          ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          ((S.card - 1 : ℕ) : ℝ) * E) := by
    intro n hn
    calc
      ∑ n' ∈ S.erase n,
          ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
          ∑ n' ∈ S.erase n,
          Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E) := by
        apply Finset.sum_le_sum
        intro n' hn'
        have hn'data := Finset.mem_erase.mp hn'
        exact hX n hn n' hn'data.2 hn'data.1.symm
      _ = Q * (A * (∑ n' ∈ S.erase n,
            typeIIDecayKernel R F c (Nat.dist n' n)) +
          (((S.erase n).card : ℕ) : ℝ) * E) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
      _ ≤ Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          (((S.erase n).card : ℕ) : ℝ) * E) := by
        apply mul_le_mul_of_nonneg_left _ hQ
        apply add_le_add_left
        exact mul_le_mul_of_nonneg_left
          (sum_typeIIDecayKernel_erase_le_sourceScale
            S n D hR hF hc0 hc (hDnat n hn) hD) hA
      _ = Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          ((S.card - 1 : ℕ) : ℝ) * E) := by
        rw [Finset.card_erase_of_mem hn]
  calc
    ∑ n ∈ S, ∑ n' ∈ S.erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        ∑ _n ∈ S,
          Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            ((S.card - 1 : ℕ) : ℝ) * E) :=
      Finset.sum_le_sum hinner
    _ = _ := by simp

/-- The complete product-restricted Type II finite reduction with a
source-shaped decay estimate substituted for every off-diagonal correlation.
No uniform worst-case replacement and no unjustified endpoint absorption are
used. -/
theorem sum_typeIIProductRestrictedInnerSum_norm_sq_le_of_decayKernel
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j D : ℕ)
    {L Q A E R F c : ℝ}
    (hK : ∀ m ∈ K, m ≠ 0) (hS : ∀ n ∈ S, n ≠ 0)
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hDnat : ∀ n ∈ S, ∀ n' ∈ S, Nat.dist n' n ≤ D)
    (hD : (D : ℝ) ≤ R)
    (hX : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ((S.card : ℝ) *
          (Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            ((S.card - 1 : ℕ) : ℝ) * E))) := by
  calc
    ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 ≤
        (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
          L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
            ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ :=
      sum_typeIIProductRestrictedInnerSum_norm_sq_le
        I K S γ N M j hK hS hL hγ
    _ ≤ (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ((S.card : ℝ) *
          (Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            ((S.card - 1 : ℕ) : ℝ) * E))) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left
          (sum_norm_typeIIProductRestrictedCorrelationSum_offDiagonal_le_decayKernel
            I K S N M j D hQ hA hR hF hc0 hc hDnat hD hX)
          (sq_nonneg L))
        ((K.card : ℝ) * (S.card : ℝ) * L ^ 2)

/-- Complete product-restricted Type II reduction with the strengthened pure
off-diagonal source scale. The diagonal remains explicit in the first term,
so no zero-distance endpoint is duplicated in the correlation term. -/
theorem sum_typeIIProductRestrictedInnerSum_norm_sq_le_sourceScale
    (I K S : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j D : ℕ)
    {L Q A E R F c : ℝ}
    (hK : ∀ m ∈ K, m ≠ 0) (hS : ∀ n ∈ S, n ≠ 0)
    (hL : 0 ≤ L) (hγ : ∀ n ∈ S, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hDnat : ∀ n ∈ S, ∀ n' ∈ S, Nat.dist n' n ≤ D)
    (hD : (D : ℝ) ≤ R)
    (hX : ∀ n ∈ S, ∀ n' ∈ S, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 ≤
      (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ((S.card : ℝ) *
          (Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            ((S.card - 1 : ℕ) : ℝ) * E))) := by
  calc
    ∑ m ∈ K, ‖typeIIProductRestrictedInnerSum I S γ N M j m‖ ^ 2 ≤
        (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
          L ^ 2 * ∑ n ∈ S, ∑ n' ∈ S.erase n,
            ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ :=
      sum_typeIIProductRestrictedInnerSum_norm_sq_le
        I K S γ N M j hK hS hL hγ
    _ ≤ (K.card : ℝ) * (S.card : ℝ) * L ^ 2 +
        L ^ 2 * ((S.card : ℝ) *
          (Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            ((S.card - 1 : ℕ) : ℝ) * E))) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left
          (sum_norm_typeIIProductRestrictedCorrelationSum_offDiagonal_le_sourceScale
            I K S N M j D hQ hA hR hF hc0 hc hDnat hD hX)
          (sq_nonneg L))
        ((K.card : ℝ) * (S.card : ℝ) * L ^ 2)

/-- The off-diagonal decay summation specialized to one actual quotient block
from the shorter-than-dyadic decomposition.  Its distance hypothesis is
discharged by the block construction. -/
theorem sum_norm_typeIIProductRestrictedCorrelationSum_shortIntervalBlock_le_decayKernel
    (I K : Finset ℕ) (N M : ℝ) (j a b q k : ℕ) {Q A E R F c : ℝ}
    (hq : 0 < q) (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hqR : (q : ℝ) ≤ R)
    (hX : ∀ n ∈ shortIntervalBlock a b q k,
      ∀ n' ∈ shortIntervalBlock a b q k, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ n ∈ shortIntervalBlock a b q k,
      ∑ n' ∈ (shortIntervalBlock a b q k).erase n,
        ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
      ((shortIntervalBlock a b q k).card : ℝ) *
        (Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
          (((shortIntervalBlock a b q k).card - 1 : ℕ) : ℝ) * E)) := by
  exact
    sum_norm_typeIIProductRestrictedCorrelationSum_offDiagonal_le_decayKernel
      I K (shortIntervalBlock a b q k) N M j q hQ hA hR hF hc0 hc
      (fun n hn n' hn' =>
        Nat.le_of_lt (natDist_lt_of_mem_same_shortIntervalBlock hq hn' hn))
      hqR hX

/-- Final squared-inner-sum estimate on one actual shorter-than-dyadic
coefficient block.  The block diameter is supplied internally. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalBlock_norm_sq_le_of_decayKernel
    (I K : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j a b q k : ℕ)
    {L Q A E R F c : ℝ}
    (hq : 0 < q) (hK : ∀ m ∈ K, m ≠ 0)
    (hS : ∀ n ∈ shortIntervalBlock a b q k, n ≠ 0)
    (hL : 0 ≤ L)
    (hγ : ∀ n ∈ shortIntervalBlock a b q k, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hqR : (q : ℝ) ≤ R)
    (hX : ∀ n ∈ shortIntervalBlock a b q k,
      ∀ n' ∈ shortIntervalBlock a b q k, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ K,
        ‖typeIIProductRestrictedInnerSum I (shortIntervalBlock a b q k)
          γ N M j m‖ ^ 2 ≤
      (K.card : ℝ) * ((shortIntervalBlock a b q k).card : ℝ) * L ^ 2 +
        L ^ 2 * (((shortIntervalBlock a b q k).card : ℝ) *
          (Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            (((shortIntervalBlock a b q k).card - 1 : ℕ) : ℝ) * E))) := by
  exact
    sum_typeIIProductRestrictedInnerSum_norm_sq_le_of_decayKernel
      I K (shortIntervalBlock a b q k) γ N M j q hK hS hL hγ
      hQ hA hR hF hc0 hc
      (fun n hn n' hn' =>
        Nat.le_of_lt (natDist_lt_of_mem_same_shortIntervalBlock hq hn' hn))
      hqR hX

/-- Endpoint-free source-scale version on an actual shorter-than-dyadic
coefficient block. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalBlock_norm_sq_le_sourceScale
    (I K : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ) (j a b q k : ℕ)
    {L Q A E R F c : ℝ}
    (hq : 0 < q) (hK : ∀ m ∈ K, m ≠ 0)
    (hS : ∀ n ∈ shortIntervalBlock a b q k, n ≠ 0)
    (hL : 0 ≤ L)
    (hγ : ∀ n ∈ shortIntervalBlock a b q k, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hqR : (q : ℝ) ≤ R)
    (hX : ∀ n ∈ shortIntervalBlock a b q k,
      ∀ n' ∈ shortIntervalBlock a b q k, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I K N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ K,
        ‖typeIIProductRestrictedInnerSum I (shortIntervalBlock a b q k)
          γ N M j m‖ ^ 2 ≤
      (K.card : ℝ) * ((shortIntervalBlock a b q k).card : ℝ) * L ^ 2 +
        L ^ 2 * (((shortIntervalBlock a b q k).card : ℝ) *
          (Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            (((shortIntervalBlock a b q k).card - 1 : ℕ) : ℝ) * E))) := by
  exact
    sum_typeIIProductRestrictedInnerSum_norm_sq_le_sourceScale
      I K (shortIntervalBlock a b q k) γ N M j q hK hS hL hγ
      hQ hA hR hF hc0 hc
      (fun n hn n' hn' =>
        Nat.le_of_lt (natDist_lt_of_mem_same_shortIntervalBlock hq hn' hn))
      hqR hX

/-- Exact double-block specialization used by the product-box Vaughan
decomposition.  Both natural supports begin at `1`, so all reciprocal-phase
indices are proved nonzero from block membership. -/
theorem sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_of_decayKernel
    (I : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ)
    (j Bouter Binner qouter qinner kouter kinner : ℕ)
    {L Q A E R F c : ℝ}
    (hqinner : 0 < qinner) (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hqinnerR : (qinner : ℝ) ≤ R)
    (hX : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I
          (shortIntervalBlock 1 (Bouter + 1) qouter kouter)
          N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ shortIntervalBlock 1 (Bouter + 1) qouter kouter,
        ‖typeIIProductRestrictedInnerSum I
          (shortIntervalBlock 1 (Binner + 1) qinner kinner)
          γ N M j m‖ ^ 2 ≤
      ((shortIntervalBlock 1 (Bouter + 1) qouter kouter).card : ℝ) *
          ((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) * L ^ 2 +
        L ^ 2 *
          (((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) *
            (Q * (A *
                (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
              (((shortIntervalBlock 1 (Binner + 1) qinner kinner).card - 1 : ℕ) : ℝ) *
                E))) := by
  apply
    sum_typeIIProductRestrictedInnerSum_shortIntervalBlock_norm_sq_le_of_decayKernel
      I (shortIntervalBlock 1 (Bouter + 1) qouter kouter) γ N M j
      1 (Binner + 1) qinner kinner hqinner
  · intro m hm
    rw [mem_shortIntervalBlock] at hm
    omega
  · intro n hn
    rw [mem_shortIntervalBlock] at hn
    omega
  · exact hL
  · exact fun n _hn => hγ n
  · exact hQ
  · exact hA
  · exact hR
  · exact hF
  · exact hc0
  · exact hc
  · exact hqinnerR
  · exact hX

/-- Endpoint-free source-scale estimate on the exact double-block geometry used
by the product-box Vaughan decomposition.  The inner correlation support is an
erased-center off-diagonal set, so no zero-distance endpoint term occurs. -/
theorem sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_sourceScale
    (I : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ)
    (j Bouter Binner qouter qinner kouter kinner : ℕ)
    {L Q A E R F c : ℝ}
    (hqinner : 0 < qinner) (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hqinnerR : (qinner : ℝ) ≤ R)
    (hX : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I
          (shortIntervalBlock 1 (Bouter + 1) qouter kouter)
          N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ shortIntervalBlock 1 (Bouter + 1) qouter kouter,
        ‖typeIIProductRestrictedInnerSum I
          (shortIntervalBlock 1 (Binner + 1) qinner kinner)
          γ N M j m‖ ^ 2 ≤
      ((shortIntervalBlock 1 (Bouter + 1) qouter kouter).card : ℝ) *
          ((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) * L ^ 2 +
        L ^ 2 *
          (((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) *
            (Q * (A *
                (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
              (((shortIntervalBlock 1 (Binner + 1) qinner kinner).card - 1 : ℕ) : ℝ) *
                E))) := by
  apply
    sum_typeIIProductRestrictedInnerSum_shortIntervalBlock_norm_sq_le_sourceScale
      I (shortIntervalBlock 1 (Bouter + 1) qouter kouter) γ N M j
      1 (Binner + 1) qinner kinner hqinner
  · intro m hm
    rw [mem_shortIntervalBlock] at hm
    omega
  · intro n hn
    rw [mem_shortIntervalBlock] at hn
    omega
  · exact hL
  · exact fun n _hn => hγ n
  · exact hQ
  · exact hA
  · exact hR
  · exact hF
  · exact hc0
  · exact hc
  · exact hqinnerR
  · exact hX

/-- Source-facing double-block estimate with both support cardinalities
replaced by their explicit block lengths. -/
theorem sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_blockLengths
    (I : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ)
    (j Bouter Binner qouter qinner kouter kinner : ℕ)
    {L Q A E R F c : ℝ}
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hqinnerR : (qinner : ℝ) ≤ R)
    (hX : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I
          (shortIntervalBlock 1 (Bouter + 1) qouter kouter)
          N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ shortIntervalBlock 1 (Bouter + 1) qouter kouter,
        ‖typeIIProductRestrictedInnerSum I
          (shortIntervalBlock 1 (Binner + 1) qinner kinner)
          γ N M j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            (qinner : ℝ) * E))) := by
  have hKcardNat := card_shortIntervalBlock_le
    1 (Bouter + 1) qouter kouter hqouter
  have hScardNat := card_shortIntervalBlock_le
    1 (Binner + 1) qinner kinner hqinner
  have hKcard :
      ((shortIntervalBlock 1 (Bouter + 1) qouter kouter).card : ℝ) ≤ qouter := by
    exact_mod_cast hKcardNat
  have hScard :
      ((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) ≤ qinner := by
    exact_mod_cast hScardNat
  have hSsubCard :
      ((((shortIntervalBlock 1 (Binner + 1) qinner kinner).card - 1 : ℕ) : ℝ)) ≤
        qinner := by
    exact_mod_cast (Nat.sub_le _ _).trans hScardNat
  have hdecay :
      0 ≤ 2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) := by
    have hconstant : 0 ≤ 2 ^ (1 - c) / (1 - c) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hc.le)
    have hscale : 0 ≤ R * F ^ (-c) :=
      mul_nonneg hR.le (Real.rpow_nonneg (zero_le_one.trans hF) _)
    positivity
  have hdiag :
      ((shortIntervalBlock 1 (Bouter + 1) qouter kouter).card : ℝ) *
          ((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) * L ^ 2 ≤
        (qouter : ℝ) * (qinner : ℝ) * L ^ 2 := by
    gcongr
  have hoff :
      L ^ 2 *
          (((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) *
            (Q * (A *
                (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
              (((shortIntervalBlock 1 (Binner + 1) qinner kinner).card - 1 : ℕ) : ℝ) *
                E))) ≤
        L ^ 2 * ((qinner : ℝ) *
          (Q * (A * (2 * (1 + (2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            (qinner : ℝ) * E))) := by
    gcongr
  exact
    (sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_of_decayKernel
      I γ N M j Bouter Binner qouter qinner kouter kinner hqinner hL hγ
      hQ hA hR hF hc0 hc hqinnerR hX).trans (add_le_add hdiag hoff)

/-- Endpoint-free source-facing estimate for two arbitrary positive quotient
blocks.  This is the form consumed by the canonical dyadic Vaughan family,
whose blocks begin at powers of two rather than at one. -/
theorem sum_typeIIProductRestrictedInnerSum_shortIntervalDoubleBlock_norm_sq_le_sourceScale_blockLengths
    (I : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ)
    (j K₀ K₁ S₀ S₁ qouter qinner kouter kinner : ℕ)
    {L Q A E R F c : ℝ}
    (hK₀ : 0 < K₀) (hS₀ : 0 < S₀)
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hqinnerR : (qinner : ℝ) ≤ R)
    (hX : ∀ n ∈ shortIntervalBlock S₀ S₁ qinner kinner,
      ∀ n' ∈ shortIntervalBlock S₀ S₁ qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I
          (shortIntervalBlock K₀ K₁ qouter kouter)
          N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ shortIntervalBlock K₀ K₁ qouter kouter,
        ‖typeIIProductRestrictedInnerSum I
          (shortIntervalBlock S₀ S₁ qinner kinner)
          γ N M j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            (qinner : ℝ) * E))) := by
  have hKcardNat := card_shortIntervalBlock_le K₀ K₁ qouter kouter hqouter
  have hScardNat := card_shortIntervalBlock_le S₀ S₁ qinner kinner hqinner
  have hKcard :
      ((shortIntervalBlock K₀ K₁ qouter kouter).card : ℝ) ≤ qouter := by
    exact_mod_cast hKcardNat
  have hScard :
      ((shortIntervalBlock S₀ S₁ qinner kinner).card : ℝ) ≤ qinner := by
    exact_mod_cast hScardNat
  have hSsubCard :
      ((((shortIntervalBlock S₀ S₁ qinner kinner).card - 1 : ℕ) : ℝ)) ≤
        qinner := by
    exact_mod_cast (Nat.sub_le _ _).trans hScardNat
  have hdecay :
      0 ≤ 2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) := by
    have hconstant : 0 ≤ 2 ^ (1 - c) / (1 - c) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hc.le)
    have hscale : 0 ≤ R * F ^ (-c) :=
      mul_nonneg hR.le (Real.rpow_nonneg (zero_le_one.trans hF) _)
    positivity
  have hdiag :
      ((shortIntervalBlock K₀ K₁ qouter kouter).card : ℝ) *
          ((shortIntervalBlock S₀ S₁ qinner kinner).card : ℝ) * L ^ 2 ≤
        (qouter : ℝ) * (qinner : ℝ) * L ^ 2 := by
    gcongr
  have hoff :
      L ^ 2 *
          (((shortIntervalBlock S₀ S₁ qinner kinner).card : ℝ) *
            (Q * (A *
                (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
              (((shortIntervalBlock S₀ S₁ qinner kinner).card - 1 : ℕ) : ℝ) *
                E))) ≤
        L ^ 2 * ((qinner : ℝ) *
          (Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            (qinner : ℝ) * E))) := by
    gcongr
  have hbase :=
    sum_typeIIProductRestrictedInnerSum_shortIntervalBlock_norm_sq_le_sourceScale
      I (shortIntervalBlock K₀ K₁ qouter kouter) γ N M j
      S₀ S₁ qinner kinner hqinner
      (fun m hm => by
        rw [mem_shortIntervalBlock] at hm
        omega)
      (fun n hn => by
        rw [mem_shortIntervalBlock] at hn
        omega)
      hL (fun n _ => hγ n) hQ hA hR hF hc0 hc hqinnerR hX
  exact hbase.trans (add_le_add hdiag hoff)

/-- Endpoint-free source-facing estimate with both exact Vaughan block
cardinalities replaced by their chosen lengths. -/
theorem sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_sourceScale_blockLengths
    (I : Finset ℕ) (γ : ℕ → ℂ) (N M : ℝ)
    (j Bouter Binner qouter qinner kouter kinner : ℕ)
    {L Q A E R F c : ℝ}
    (hqouter : 0 < qouter) (hqinner : 0 < qinner)
    (hL : 0 ≤ L) (hγ : ∀ n, ‖γ n‖ ≤ L)
    (hQ : 0 ≤ Q) (hA : 0 ≤ A) (hE : 0 ≤ E)
    (hR : 0 < R) (hF : 1 ≤ F) (hc0 : 0 ≤ c) (hc : c < 1)
    (hqinnerR : (qinner : ℝ) ≤ R)
    (hX : ∀ n ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner,
      ∀ n' ∈ shortIntervalBlock 1 (Binner + 1) qinner kinner, n ≠ n' →
      ‖typeIIProductRestrictedCorrelationSum I
          (shortIntervalBlock 1 (Bouter + 1) qouter kouter)
          N M j n n'‖ ≤
        Q * (A * typeIIDecayKernel R F c (Nat.dist n' n) + E)) :
    ∑ m ∈ shortIntervalBlock 1 (Bouter + 1) qouter kouter,
        ‖typeIIProductRestrictedInnerSum I
          (shortIntervalBlock 1 (Binner + 1) qinner kinner)
          γ N M j m‖ ^ 2 ≤
      (qouter : ℝ) * (qinner : ℝ) * L ^ 2 +
        L ^ 2 * ((qinner : ℝ) *
          (Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            (qinner : ℝ) * E))) := by
  have hKcardNat := card_shortIntervalBlock_le
    1 (Bouter + 1) qouter kouter hqouter
  have hScardNat := card_shortIntervalBlock_le
    1 (Binner + 1) qinner kinner hqinner
  have hKcard :
      ((shortIntervalBlock 1 (Bouter + 1) qouter kouter).card : ℝ) ≤ qouter := by
    exact_mod_cast hKcardNat
  have hScard :
      ((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) ≤ qinner := by
    exact_mod_cast hScardNat
  have hSsubCard :
      ((((shortIntervalBlock 1 (Binner + 1) qinner kinner).card - 1 : ℕ) : ℝ)) ≤
        qinner := by
    exact_mod_cast (Nat.sub_le _ _).trans hScardNat
  have hdecay :
      0 ≤ 2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c)) := by
    have hconstant : 0 ≤ 2 ^ (1 - c) / (1 - c) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) (sub_nonneg.mpr hc.le)
    have hscale : 0 ≤ R * F ^ (-c) :=
      mul_nonneg hR.le (Real.rpow_nonneg (zero_le_one.trans hF) _)
    positivity
  have hdiag :
      ((shortIntervalBlock 1 (Bouter + 1) qouter kouter).card : ℝ) *
          ((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) * L ^ 2 ≤
        (qouter : ℝ) * (qinner : ℝ) * L ^ 2 := by
    gcongr
  have hoff :
      L ^ 2 *
          (((shortIntervalBlock 1 (Binner + 1) qinner kinner).card : ℝ) *
            (Q * (A *
                (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
              (((shortIntervalBlock 1 (Binner + 1) qinner kinner).card - 1 : ℕ) : ℝ) *
                E))) ≤
        L ^ 2 * ((qinner : ℝ) *
          (Q * (A * (2 * ((2 ^ (1 - c) / (1 - c)) * R * F ^ (-c))) +
            (qinner : ℝ) * E))) := by
    gcongr
  exact
    (sum_typeIIProductRestrictedInnerSum_doubleBlock_norm_sq_le_sourceScale
      I γ N M j Bouter Binner qouter qinner kouter kinner hqinner hL hγ
      hQ hA hR hF hc0 hc hqinnerR hX).trans (add_le_add hdiag hoff)


end Tao2026
