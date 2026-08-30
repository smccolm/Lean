import RiemannZeta.GuthMaynard.HughesYoungFiniteContourSet
import RiemannZeta.GuthMaynard.HughesYoungInfiniteBox
import RiemannZeta.GuthMaynard.HughesYoungSquareTruncation

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Finite effective-conductor dyadic family

For positive reduced coefficients `a,b`, every divisor pair with `m*n ≤ R`
is reconstructed by the finite collection of equation-(69) boxes whose
physical scale product is at most `a*b*R`.
-/

/-- The `hughesYoungActiveDyadicBoxes` definition used by the source-facing construction in `HughesYoungActiveDyadic`. -/
noncomputable def hughesYoungActiveDyadicBoxes
    (a b R K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (K + 2)).product (Finset.range (K + 2))).filter
    (fun ij => hughesYoungFullDyadicScale ij.1 *
      hughesYoungFullDyadicScale ij.2 ≤ ((a * b * R : ℕ) : ℝ))

/-- The active two-dimensional dyadic family has at most the square of the
number of retained generations. -/
theorem card_hughesYoungActiveDyadicBoxes_le (a b R K : ℕ) :
    (hughesYoungActiveDyadicBoxes a b R K).card ≤ (K + 2) ^ 2 := by
  unfold hughesYoungActiveDyadicBoxes
  apply (Finset.card_filter_le _ _).trans_eq
  simp [pow_two]

/-- The `hughesYoungActiveDyadicWeight` definition used by the source-facing construction in `HughesYoungActiveDyadic`. -/
noncomputable def hughesYoungActiveDyadicWeight
    (a b R K m n : ℕ) : ℝ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
    hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
      hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ)

theorem left_coordinate_le_active_cover
    {a b R m n : ℕ} (hb : 0 < b) (hn : 0 < n)
    (hmn : m * n ≤ R) :
    a * m ≤ a * b * R := by
  have hnOne : 1 ≤ n := hn
  have hbOne : 1 ≤ b := hb
  have hm_mn : m ≤ m * n := by
    simpa only [mul_one] using Nat.mul_le_mul_left m hnOne
  have hR_bR : R ≤ b * R := by
    simpa only [one_mul] using Nat.mul_le_mul_right R hbOne
  calc
    a * m ≤ a * (m * n) := Nat.mul_le_mul_left a hm_mn
    _ ≤ a * R := Nat.mul_le_mul_left a hmn
    _ ≤ a * (b * R) := Nat.mul_le_mul_left a hR_bR
    _ = a * b * R := by ac_rfl

theorem right_coordinate_le_active_cover
    {a b R m n : ℕ} (ha : 0 < a) (hm : 0 < m)
    (hmn : m * n ≤ R) :
    b * n ≤ a * b * R := by
  have hmOne : 1 ≤ m := hm
  have haOne : 1 ≤ a := ha
  have hn_mn : n ≤ m * n := by
    simpa only [one_mul] using Nat.mul_le_mul_right n hmOne
  have hR_aR : R ≤ a * R := by
    simpa only [one_mul] using Nat.mul_le_mul_right R haOne
  calc
    b * n ≤ b * (m * n) := Nat.mul_le_mul_left b hn_mn
    _ ≤ b * R := Nat.mul_le_mul_left b hmn
    _ ≤ b * (a * R) := Nat.mul_le_mul_left b hR_aR
    _ = a * b * R := by ac_rfl

theorem hughesYoungActiveDyadicWeight_eq_one
    {a b R K m n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) (hmn : m * n ≤ R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    hughesYoungActiveDyadicWeight a b R K m n = 1 := by
  let F : ℕ × ℕ → ℝ := fun ij =>
    hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
      hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ)
  have hleftCoord : a * m ≤ a * b * R :=
    left_coordinate_le_active_cover hb hn hmn
  have hrightCoord : b * n ≤ a * b * R :=
    right_coordinate_le_active_cover ha hm hmn
  have hleftCover : (((a * m : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1) := by
    have hcast : (((a * m : ℕ) : ℝ)) ≤ ((a * b * R : ℕ) : ℝ) := by
      exact_mod_cast hleftCoord
    exact hcast.trans hcover
  have hrightCover : (((b * n : ℕ) : ℝ)) ≤
      hughesYoungDyadicRatio ^ (K + 1) := by
    have hcast : (((b * n : ℕ) : ℝ)) ≤ ((a * b * R : ℕ) : ℝ) := by
      exact_mod_cast hrightCoord
    exact hcast.trans hcover
  have houtside : ∀ ij ∉ hughesYoungActiveDyadicBoxes a b R K,
      F ij = 0 := by
    intro ij hij
    by_cases hi : ij.1 < K + 2
    · by_cases hj : ij.2 < K + 2
      · have hscale : ¬ (hughesYoungFullDyadicScale ij.1 *
            hughesYoungFullDyadicScale ij.2 ≤ ((a * b * R : ℕ) : ℝ)) := by
          intro hs
          apply hij
          unfold hughesYoungActiveDyadicBoxes
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_product.mpr
            ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩, hs⟩
        by_cases hcutI :
            hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) = 0
        · change hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
              hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) = 0
          rw [hcutI, zero_mul]
        · by_cases hcutJ :
              hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) = 0
          · change hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
                hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) = 0
            rw [hcutJ, mul_zero]
          · have hsuppI := support_hughesYoungDyadicCutoffAt_subset
                (hughesYoungFullDyadicScale_pos ij.1) hcutI
            have hsuppJ := support_hughesYoungDyadicCutoffAt_subset
                (hughesYoungFullDyadicScale_pos ij.2) hcutJ
            have hmul : hughesYoungFullDyadicScale ij.1 *
                  hughesYoungFullDyadicScale ij.2 ≤
                (((a * m : ℕ) : ℝ)) * (((b * n : ℕ) : ℝ)) := by
              exact mul_le_mul hsuppI.1 hsuppJ.1
                (hughesYoungFullDyadicScale_pos ij.2).le
                (by positivity)
            have hprodNat : a * m * (b * n) ≤ a * b * R := by
              calc
                a * m * (b * n) = a * b * (m * n) := by ac_rfl
                _ ≤ a * b * R := Nat.mul_le_mul_left (a * b) hmn
            have hprodReal : (((a * m : ℕ) : ℝ)) * (((b * n : ℕ) : ℝ)) ≤
                ((a * b * R : ℕ) : ℝ) := by
              exact_mod_cast hprodNat
            exact (hscale (hmul.trans hprodReal)).elim
      · have hzero := hughesYoungFullDyadicCutoff_eq_zero_of_cover
          hrightCover (Nat.le_of_not_gt hj)
        change hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
            hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) = 0
        rw [hzero, mul_zero]
    · have hzero := hughesYoungFullDyadicCutoff_eq_zero_of_cover
        hleftCover (Nat.le_of_not_gt hi)
      change hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
          hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) = 0
      rw [hzero, zero_mul]
  have hsum : (∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K, F ij) =
      ∑' ij : ℕ × ℕ, F ij := by
    rw [tsum_eq_sum houtside]
  have hFsum : (∑' ij : ℕ × ℕ, F ij) = 1 := by
    have hleft := tsum_hughesYoungFullDyadicCutoff_nat_eq_one
      (Nat.mul_pos ha hm)
    have hright := tsum_hughesYoungFullDyadicCutoff_nat_eq_one
      (Nat.mul_pos hb hn)
    have hsummable : Summable F :=
      (summable_hughesYoungFullDyadicCutoff_nat (a * m)).mul_of_nonneg
        (summable_hughesYoungFullDyadicCutoff_nat (b * n))
        (fun _ => hughesYoungFullDyadicCutoff_nonneg_nat _ _)
        (fun _ => hughesYoungFullDyadicCutoff_nonneg_nat _ _)
    rw [hsummable.tsum_prod]
    simp only [F]
    simp_rw [tsum_mul_left]
    rw [hright]
    simp only [mul_one]
    exact hleft
  unfold hughesYoungActiveDyadicWeight
  exact hsum.trans hFsum

theorem hughesYoungActiveDyadicWeight_nonneg
    (a b R K m n : ℕ) :
    0 ≤ hughesYoungActiveDyadicWeight a b R K m n := by
  unfold hughesYoungActiveDyadicWeight
  exact Finset.sum_nonneg fun ij _ => mul_nonneg
    (hughesYoungFullDyadicCutoff_nonneg_nat _ _)
    (hughesYoungFullDyadicCutoff_nonneg_nat _ _)

theorem hughesYoungActiveDyadicWeight_le_one
    {a b R K m n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) :
    hughesYoungActiveDyadicWeight a b R K m n ≤ 1 := by
  let F : ℕ × ℕ → ℝ := fun ij =>
    hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
      hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ)
  have hsummable : Summable F :=
    (summable_hughesYoungFullDyadicCutoff_nat (a * m)).mul_of_nonneg
      (summable_hughesYoungFullDyadicCutoff_nat (b * n))
      (fun _ => hughesYoungFullDyadicCutoff_nonneg_nat _ _)
      (fun _ => hughesYoungFullDyadicCutoff_nonneg_nat _ _)
  have hpartial :
      (∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K, F ij) ≤
        ∑' ij : ℕ × ℕ, F ij :=
    hsummable.sum_le_tsum _ (fun ij _ => mul_nonneg
      (hughesYoungFullDyadicCutoff_nonneg_nat _ _)
      (hughesYoungFullDyadicCutoff_nonneg_nat _ _))
  have hfull : (∑' ij : ℕ × ℕ, F ij) = 1 := by
    rw [hsummable.tsum_prod]
    simp only [F]
    simp_rw [tsum_mul_left]
    rw [tsum_hughesYoungFullDyadicCutoff_nat_eq_one (Nat.mul_pos hb hn)]
    simp only [mul_one]
    exact tsum_hughesYoungFullDyadicCutoff_nat_eq_one (Nat.mul_pos ha hm)
  unfold hughesYoungActiveDyadicWeight
  exact hpartial.trans_eq hfull

/-- The finite effective-conductor family on the opening line. -/
noncomputable def hughesYoungActiveHighPairSum
    (q a b R K : ℕ) (t u : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    (hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℂ) *
      hughesYoungRightPairTerm t (2 * q) u p

/-- The exact omitted part of the opening-line pair series. -/
noncomputable def hughesYoungActiveHighPairRemainder
    (q a b R K : ℕ) (t u : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
      hughesYoungRightPairTerm t (2 * q) u p

theorem norm_one_sub_hughesYoungActiveDyadicWeight_le_one
    {a b R K m n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) :
    |1 - hughesYoungActiveDyadicWeight a b R K m n| ≤ 1 := by
  have hnonneg := hughesYoungActiveDyadicWeight_nonneg a b R K m n
  have hle := hughesYoungActiveDyadicWeight_le_one
    (R := R) (K := K) ha hb hm hn
  rw [abs_of_nonneg (sub_nonneg.mpr hle)]
  linarith

theorem norm_activeHighPairRemainder_term_le_tail
    {q a b R K : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u : ℝ) (p : ℕ × ℕ) :
    ‖((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
        hughesYoungRightPairTerm t (2 * q) u p‖ ≤
      ‖if (R : ℝ) < (p.1 : ℝ) * p.2 then
          hughesYoungRightPairTerm t (2 * q) u p else 0‖ := by
  rcases p with ⟨m, n⟩
  by_cases hm : m = 0
  · subst m
    simp [hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero]
  by_cases hn : n = 0
  · subst n
    simp [hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero]
  have hmPos : 0 < m := Nat.pos_of_ne_zero hm
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  by_cases hmn : m * n ≤ R
  · have hweight := hughesYoungActiveDyadicWeight_eq_one
      ha hb hmPos hnPos hmn hcover
    have hprod : ¬ (R : ℝ) < (m : ℝ) * n := by
      have hnot : ¬ R < m * n := not_lt.mpr hmn
      exact_mod_cast hnot
    simp [hweight, hprod]
  · have hprodNat : R < m * n := Nat.lt_of_not_ge hmn
    have hprod : (R : ℝ) < (m : ℝ) * n := by
      exact_mod_cast hprodNat
    rw [if_pos hprod, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (norm_one_sub_hughesYoungActiveDyadicWeight_le_one
        ha hb hmPos hnPos)

theorem summable_hughesYoungActiveHighPairRemainder
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
        hughesYoungRightPairTerm t (2 * q) u p) := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hη : (1 / 4 : ℝ) < 2 * (q : ℝ) - 1 / 2 := by
    have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  exact (summable_norm_hughesYoungRightPairTerm_high_tail
      hRreal (by norm_num) hη).of_norm_bounded
    (norm_activeHighPairRemainder_term_le_tail ha hb hcover t u)

theorem summable_hughesYoungActiveHighPairSum
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t u : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      (hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℂ) *
        hughesYoungRightPairTerm t (2 * q) u p) := by
  have hfull : Summable (hughesYoungRightPairTerm t (2 * q) u) :=
    summable_hughesYoungRightPairTerm t u (by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith)
  exact hfull.norm.of_norm_bounded (fun p => by
    rcases p with ⟨m, n⟩
    by_cases hm : m = 0
    · subst m
      simp [hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero]
    by_cases hn : n = 0
    · subst n
      simp [hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hughesYoungActiveDyadicWeight_nonneg a b R K m n)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (hughesYoungActiveDyadicWeight_le_one (R := R) (K := K) ha hb
        (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)))

/-- Exact decomposition of the full opening-line pair series into the finite
effective-conductor dyadic family and its product-tail remainder. -/
theorem tsum_hughesYoungRightPairTerm_eq_active_add_remainder
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u : ℝ) :
    (∑' p : ℕ × ℕ, hughesYoungRightPairTerm t (2 * q) u p) =
      hughesYoungActiveHighPairSum q a b R K t u +
        hughesYoungActiveHighPairRemainder q a b R K t u := by
  have hactive := summable_hughesYoungActiveHighPairSum
    (R := R) (K := K) hq ha hb t u
  have hrem := summable_hughesYoungActiveHighPairRemainder
    hq ha hb hR hcover t u
  unfold hughesYoungActiveHighPairSum
    hughesYoungActiveHighPairRemainder
  rw [← hactive.tsum_add hrem]
  apply tsum_congr
  intro p
  push_cast
  ring

theorem norm_hughesYoungActiveHighPairRemainder_le
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u : ℝ) {η : ℝ} (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ‖hughesYoungActiveHighPairRemainder q a b R K t u‖ ≤
      ‖hughesYoungRightContourWeight t (2 * q) u‖ *
        (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
        hughesYoungReferenceDivisorPairMass η := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  unfold hughesYoungActiveHighPairRemainder
  calc
    ‖∑' p : ℕ × ℕ,
        ((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
          hughesYoungRightPairTerm t (2 * q) u p‖ ≤
        ∑' p : ℕ × ℕ,
          ‖((1 - hughesYoungActiveDyadicWeight a b R K p.1 p.2 : ℝ) : ℂ) *
            hughesYoungRightPairTerm t (2 * q) u p‖ :=
      norm_tsum_le_tsum_norm
        (summable_hughesYoungActiveHighPairRemainder
          hq ha hb hR hcover t u).norm
    _ ≤ ∑' p : ℕ × ℕ,
        ‖if (R : ℝ) < (p.1 : ℝ) * p.2 then
            hughesYoungRightPairTerm t (2 * q) u p else 0‖ := by
      exact (summable_hughesYoungActiveHighPairRemainder
          hq ha hb hR hcover t u).norm.tsum_le_tsum
        (norm_activeHighPairRemainder_term_le_tail ha hb hcover t u)
        (summable_norm_hughesYoungRightPairTerm_high_tail
          hRreal hη0 hη)
    _ ≤ _ := by
      exact (summable_norm_hughesYoungRightPairTerm_high_tail
          hRreal hη0 hη).tsum_le_tsum
        (fun p => by simpa only [mul_assoc] using
          norm_hughesYoungRightPairTerm_high_tail_le hRreal hη p)
        ((summable_norm_divisorPair_one_add hη0).mul_left
          (‖hughesYoungRightContourWeight t (2 * q) u‖ *
            (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)))) |>.trans_eq (by
              rw [tsum_mul_left]
              rfl)

/-- The `hughesYoungFullDyadicHighPairTerm` definition used by the source-facing construction in `HughesYoungActiveDyadic`. -/
noncomputable def hughesYoungFullDyadicHighPairTerm
    (q a b i j : ℕ) (t u : ℝ) (p : ℕ × ℕ) : ℂ :=
  (hughesYoungFullDyadicCutoff i ((a * p.1 : ℕ) : ℝ) : ℂ) *
    (hughesYoungFullDyadicCutoff j ((b * p.2 : ℕ) : ℝ) : ℂ) *
    hughesYoungRightPairTerm t (2 * q) u p

theorem hughesYoungFullDyadicHighPairTerm_eq_zero_of_left_bound
    {q a b i j m n : ℕ} (ha : 0 < a)
    (hm : hughesYoungFullDyadicBound i < m) (t u : ℝ) :
    hughesYoungFullDyadicHighPairTerm q a b i j t u (m, n) = 0 := by
  unfold hughesYoungFullDyadicHighPairTerm
  rw [hughesYoungFullDyadicCutoff_eq_zero_of_bound_lt ha hm]
  simp

theorem hughesYoungFullDyadicHighPairTerm_eq_zero_of_right_bound
    {q a b i j m n : ℕ} (hb : 0 < b)
    (hn : hughesYoungFullDyadicBound j < n) (t u : ℝ) :
    hughesYoungFullDyadicHighPairTerm q a b i j t u (m, n) = 0 := by
  unfold hughesYoungFullDyadicHighPairTerm
  rw [hughesYoungFullDyadicCutoff_eq_zero_of_bound_lt hb hn]
  simp

theorem hughesYoungFullDyadicHighPairTerm_eq_zero_of_left_zero
    (q a b i j n : ℕ) (t u : ℝ) :
    hughesYoungFullDyadicHighPairTerm q a b i j t u (0, n) = 0 := by
  unfold hughesYoungFullDyadicHighPairTerm
  rw [hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero t (2 * q) u rfl]
  simp

theorem hughesYoungFullDyadicHighPairTerm_eq_zero_of_right_zero
    (q a b i j m : ℕ) (t u : ℝ) :
    hughesYoungFullDyadicHighPairTerm q a b i j t u (m, 0) = 0 := by
  unfold hughesYoungFullDyadicHighPairTerm
  rw [hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero t (2 * q) u rfl]
  simp

theorem summable_hughesYoungFullDyadicHighPairTerm
    {q a b i j : ℕ} (ha : 0 < a) (hb : 0 < b) (t u : ℝ) :
    Summable (hughesYoungFullDyadicHighPairTerm q a b i j t u) := by
  apply summable_of_ne_finset_zero
    (s := Finset.Icc (1, 1)
      (hughesYoungFullDyadicBound i, hughesYoungFullDyadicBound j))
  intro p hp
  rcases p with ⟨m, n⟩
  by_cases hm0 : m = 0
  · subst m
    exact hughesYoungFullDyadicHighPairTerm_eq_zero_of_left_zero
      q a b i j n t u
  by_cases hn0 : n = 0
  · subst n
    exact hughesYoungFullDyadicHighPairTerm_eq_zero_of_right_zero
      q a b i j m t u
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  by_cases hm : m ≤ hughesYoungFullDyadicBound i
  · by_cases hn : n ≤ hughesYoungFullDyadicBound j
    · exfalso
      apply hp
      simp [Prod.le_def, hm1, hn1, hm, hn]
    · exact hughesYoungFullDyadicHighPairTerm_eq_zero_of_right_bound
        hb (Nat.lt_of_not_ge hn) t u
  · exact hughesYoungFullDyadicHighPairTerm_eq_zero_of_left_bound
      ha (Nat.lt_of_not_ge hm) t u

theorem tsum_hughesYoungFullDyadicHighPairTerm_eq_finiteSum
    {q a b i j : ℕ} (ha : 0 < a) (hb : 0 < b) (t u : ℝ) :
    (∑' p : ℕ × ℕ,
      hughesYoungFullDyadicHighPairTerm q a b i j t u p) =
      ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound i),
        ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound j),
          hughesYoungFullDyadicHighPairTerm q a b i j t u (m, n) := by
  rw [tsum_eq_sum (s := Finset.Icc (1, 1)
    (hughesYoungFullDyadicBound i, hughesYoungFullDyadicBound j))]
  · rw [Finset.Icc_prod_def, Finset.sum_product]
  · intro p hp
    rcases p with ⟨m, n⟩
    by_cases hm0 : m = 0
    · subst m
      exact hughesYoungFullDyadicHighPairTerm_eq_zero_of_left_zero
        q a b i j n t u
    by_cases hn0 : n = 0
    · subst n
      exact hughesYoungFullDyadicHighPairTerm_eq_zero_of_right_zero
        q a b i j m t u
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
    by_cases hm : m ≤ hughesYoungFullDyadicBound i
    · by_cases hn : n ≤ hughesYoungFullDyadicBound j
      · exfalso
        apply hp
        simp [Prod.le_def, hm1, hn1, hm, hn]
      · exact hughesYoungFullDyadicHighPairTerm_eq_zero_of_right_bound
          hb (Nat.lt_of_not_ge hn) t u
    · exact hughesYoungFullDyadicHighPairTerm_eq_zero_of_left_bound
        ha (Nat.lt_of_not_ge hm) t u

/-- The apparently infinite active pair sum is exactly the finite sum of
the selected dyadic boxes, each of which is itself a finite rectangle. -/
theorem hughesYoungActiveHighPairSum_eq_finiteBoxes
    {q a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (t u : ℝ) :
    hughesYoungActiveHighPairSum q a b R K t u =
      ∑ ij ∈ hughesYoungActiveDyadicBoxes a b R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            hughesYoungFullDyadicHighPairTerm q a b ij.1 ij.2 t u (m, n) := by
  unfold hughesYoungActiveHighPairSum hughesYoungActiveDyadicWeight
  let S := hughesYoungActiveDyadicBoxes a b R K
  have hpoint (p : ℕ × ℕ) :
      (((∑ ij ∈ S,
          hughesYoungFullDyadicCutoff ij.1 ((a * p.1 : ℕ) : ℝ) *
            hughesYoungFullDyadicCutoff ij.2 ((b * p.2 : ℕ) : ℝ) : ℝ) : ℂ) *
          hughesYoungRightPairTerm t (2 * q) u p) =
        ∑ ij ∈ S,
          hughesYoungFullDyadicHighPairTerm q a b ij.1 ij.2 t u p := by
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ij hij
    unfold hughesYoungFullDyadicHighPairTerm
    push_cast
    ring
  calc
    (∑' p : ℕ × ℕ,
        (((∑ ij ∈ S,
            hughesYoungFullDyadicCutoff ij.1 ((a * p.1 : ℕ) : ℝ) *
              hughesYoungFullDyadicCutoff ij.2 ((b * p.2 : ℕ) : ℝ) : ℝ) : ℂ) *
          hughesYoungRightPairTerm t (2 * q) u p)) =
        ∑' p : ℕ × ℕ,
          ∑ ij ∈ S,
            hughesYoungFullDyadicHighPairTerm q a b ij.1 ij.2 t u p :=
      tsum_congr hpoint
    _ = ∑ ij ∈ S,
          ∑' p : ℕ × ℕ,
            hughesYoungFullDyadicHighPairTerm q a b ij.1 ij.2 t u p := by
      rw [Summable.tsum_finsetSum]
      intro ij hij
      exact summable_hughesYoungFullDyadicHighPairTerm
        (q := q) (a := a) (b := b) (i := ij.1) (j := ij.2) ha hb t u
    _ = ∑ ij ∈ S,
          ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              hughesYoungFullDyadicHighPairTerm q a b ij.1 ij.2 t u (m, n) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact tsum_hughesYoungFullDyadicHighPairTerm_eq_finiteSum ha hb t u

end RiemannZeta.GuthMaynard
