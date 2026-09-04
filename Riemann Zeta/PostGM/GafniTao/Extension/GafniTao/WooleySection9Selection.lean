import GafniTao.WooleySection9Arithmetic
import Mathlib.Analysis.MeanInequalities

/-!
# The finite selection in Wooley Lemma 9.2

This is the exact finite AM--GM/pigeonhole step used after (9.2).  It is
kept independent of the analytic means: the input family is nonnegative,
and the conclusion selects an actual index in `[1,r]` rather than inserting
an unspecified maximum.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The interval of grades occurring in Wooley (9.2). -/
def wooleyGradeRange (r : ℕ) : Finset ℕ := Finset.Icc 1 r

theorem wooleyRho_one {k : ℕ} (hk : 1 ≤ k) :
    wooleyRho k 1 = 1 / (k : ℝ) := by
  unfold wooleyRho
  rw [Nat.sub_add_cancel hk]
  norm_num

theorem wooleyGradeRange_card (r : ℕ) :
    (wooleyGradeRange r).card = r := by
  simp [wooleyGradeRange]

theorem wooleyGradeRange_nonempty {r : ℕ} (hr : 1 ≤ r) :
    (wooleyGradeRange r).Nonempty := by
  refine ⟨1, ?_⟩
  simp only [wooleyGradeRange, mem_Icc, le_refl, true_and]
  exact hr

/-- Equal-weight AM--GM on the source grade interval. -/
theorem wooley_grade_geometric_le_average
    {r : ℕ} (hr : 1 ≤ r) (Y : ℕ → ℝ)
    (hY : ∀ j ∈ wooleyGradeRange r, 0 ≤ Y j) :
    ∏ j ∈ wooleyGradeRange r, (Y j) ^ (1 / (r : ℝ)) ≤
      (1 / (r : ℝ)) * ∑ j ∈ wooleyGradeRange r, Y j := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hweights :
      ∑ _j ∈ wooleyGradeRange r, (1 / (r : ℝ)) = 1 := by
    rw [sum_const, wooleyGradeRange_card, nsmul_eq_mul]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted
    (s := wooleyGradeRange r)
    (fun _j : ℕ => 1 / (r : ℝ)) Y
    (fun _j _ => by positivity) hweights hY
  simpa only [one_div, Finset.mul_sum] using hamgm

/-- Some actual grade dominates the equal-weight geometric mean. -/
theorem exists_wooley_grade_ge_geometric
    {r : ℕ} (hr : 1 ≤ r) (Y : ℕ → ℝ)
    (hY : ∀ j ∈ wooleyGradeRange r, 0 ≤ Y j) :
    ∃ j ∈ wooleyGradeRange r,
      ∏ i ∈ wooleyGradeRange r, (Y i) ^ (1 / (r : ℝ)) ≤ Y j := by
  let S : ℝ := ∑ i ∈ wooleyGradeRange r, Y i
  have havg := wooley_grade_geometric_le_average hr Y hY
  have hsum :
      ∑ _j ∈ wooleyGradeRange r, S / (r : ℝ) ≤
        ∑ j ∈ wooleyGradeRange r, Y j := by
    rw [sum_const, wooleyGradeRange_card, nsmul_eq_mul]
    dsimp [S]
    have hrR : (r : ℝ) ≠ 0 := by positivity
    field_simp
    exact le_rfl
  obtain ⟨j, hj, hjdom⟩ :=
    Finset.exists_le_of_sum_le (wooleyGradeRange_nonempty hr) hsum
  refine ⟨j, hj, havg.trans ?_⟩
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  dsimp [S] at hjdom ⊢
  simpa only [one_div, inv_mul_eq_div] using hjdom

/-- Source form of the elementary inequality used in Lemma 9.2, with
`Y_j = X_j ^ rho_j`. -/
theorem exists_wooley_grade_for_weighted_product
    {k r : ℕ} (hr : 1 ≤ r) (X : ℕ → ℝ)
    (hX : ∀ j ∈ wooleyGradeRange r, 0 ≤ X j) :
    ∃ j ∈ wooleyGradeRange r,
      ∏ i ∈ wooleyGradeRange r,
          (X i) ^ (wooleyRho k i / (r : ℝ)) ≤
        (X j) ^ wooleyRho k j := by
  let Y : ℕ → ℝ := fun j => (X j) ^ wooleyRho k j
  have hY : ∀ j ∈ wooleyGradeRange r, 0 ≤ Y j :=
    fun j _ => Real.rpow_nonneg (hX j ‹_›) _
  obtain ⟨j, hj, hgeom⟩ := exists_wooley_grade_ge_geometric hr Y hY
  refine ⟨j, hj, ?_⟩
  rw [show (X j) ^ wooleyRho k j = Y j by rfl]
  calc
    ∏ i ∈ wooleyGradeRange r,
        (X i) ^ (wooleyRho k i / (r : ℝ)) =
      ∏ i ∈ wooleyGradeRange r, (Y i) ^ (1 / (r : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        dsimp [Y]
        rw [← Real.rpow_mul (hX i hi)]
        congr 1
        ring
    _ ≤ Y j := hgeom

/-- The exact exponent comparison in the last paragraph of the proof of
Wooley Lemma 9.2.  The hypothesis is the displayed hierarchy inequality
`b*Lambda/k ≥ 2(r+1)k^2*nu`. -/
theorem wooley_section9_decay_exponent
    {k r b nu : ℕ} {Lambda : ℝ}
    (hk : 2 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k - 1)
    (hLambda : 0 ≤ Lambda)
    (hhierarchy :
      2 * (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
        (b : ℝ) * Lambda / (k : ℝ)) :
    (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) -
        (b : ℝ) * ((1 - 1 / (k : ℝ)) * Lambda / (r : ℝ)) ≤
      -(b : ℝ) * Lambda / (2 * (k : ℝ)) := by
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hkOne : 1 ≤ k := by omega
  have hrkR : (r : ℝ) ≤ (k : ℝ) - 1 := by
    calc
      (r : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by exact_mod_cast hrk
      _ = (k : ℝ) - 1 := by rw [Nat.cast_sub hkOne]; norm_num
  have hkpos : (0 : ℝ) < k := by positivity
  have hrpos : (0 : ℝ) < r := by positivity
  have hweight :
      1 / (k : ℝ) ≤ (1 - 1 / (k : ℝ)) / (r : ℝ) := by
    rw [div_le_div_iff₀ hkpos hrpos]
    have hident : (1 - 1 / (k : ℝ)) * (k : ℝ) = (k : ℝ) - 1 := by
      field_simp
    rw [one_mul, hident]
    exact hrkR
  have hbLambda : 0 ≤ (b : ℝ) * Lambda :=
    mul_nonneg (Nat.cast_nonneg _) hLambda
  have hweighted :
      (b : ℝ) * Lambda / (k : ℝ) ≤
        (b : ℝ) * ((1 - 1 / (k : ℝ)) * Lambda / (r : ℝ)) := by
    calc
      (b : ℝ) * Lambda / (k : ℝ) =
          ((b : ℝ) * Lambda) * (1 / (k : ℝ)) := by ring
      _ ≤ ((b : ℝ) * Lambda) *
          ((1 - 1 / (k : ℝ)) / (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hweight hbLambda
      _ = (b : ℝ) * ((1 - 1 / (k : ℝ)) * Lambda / (r : ℝ)) := by
        ring
  have hhalf :
      -(b : ℝ) * Lambda / (2 * (k : ℝ)) =
        -((b : ℝ) * Lambda / (k : ℝ)) / 2 := by ring
  rw [hhalf]
  linarith

/-- The power-of-`p` form of the Lemma 9.2 loss absorption. -/
theorem wooley_section9_loss_absorption
    {p k r b nu : ℕ} {Lambda : ℝ}
    (hp : 2 ≤ p) (hk : 2 ≤ k) (hr : 1 ≤ r) (hrk : r ≤ k - 1)
    (hLambda : 0 ≤ Lambda)
    (hhierarchy :
      2 * (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) ≤
        (b : ℝ) * Lambda / (k : ℝ)) :
    (p : ℝ) ^ (((r + 1) * k ^ 2 * nu : ℕ) : ℝ) *
        (p : ℝ) ^
          (-(b : ℝ) * ((1 - 1 / (k : ℝ)) * Lambda / (r : ℝ))) ≤
      (p : ℝ) ^ (-(b : ℝ) * Lambda / (2 * (k : ℝ))) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [← Real.rpow_add hpR]
  apply Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast (show 1 ≤ p by omega))
  have h := wooley_section9_decay_exponent hk hr hrk hLambda hhierarchy
  convert h using 1
  all_goals ring

#print axioms wooleyGradeRange_card
#print axioms wooleyRho_one
#print axioms wooleyGradeRange_nonempty
#print axioms wooley_grade_geometric_le_average
#print axioms exists_wooley_grade_ge_geometric
#print axioms exists_wooley_grade_for_weighted_product
#print axioms wooley_section9_decay_exponent
#print axioms wooley_section9_loss_absorption

end

end GafniTao
