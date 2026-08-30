import RiemannZeta.GuthMaynard.HughesYoungInactiveDFIAssembly

open Asymptotics Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Cancellation-preserving contour transfer for the omitted dyadic family

The product truncation in Hughes--Young equation (83) is made on the
absolutely convergent opening line.  The definitions in this file retain the
entire finite inactive dyadic family while it is moved to the small line.
This avoids estimating individual central summands before the signed source
has been reassembled.
-/

/-- The product-truncation complement after the actual mollifier, physical
height, and finite small-contour integrations. -/
noncomputable def hughesYoungActiveComplementIntegratedCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveComplementSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K

/-- For one positive mollifier pair, joint integrability allows the exact
active-complement subtraction to pass through both integrals. -/
theorem integral_hughesYoungActiveComplementSignedCentralAtHeight_eq_sub
    {T : ℝ} (hT : Real.exp 3 ≤ T) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    (∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveComplementSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K) =
      (∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungFinitePureSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) K) -
      (∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveReassembledSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K) := by
  have hT1 : Real.exp 1 ≤ T :=
    (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 3)).trans hT
  have hT0 : 0 < T := (Real.exp_pos 3).trans_le hT
  have hc := hughesYoungSmallContour_spec hT1
  have hlog3 : 3 ≤ Real.log T := by
    rw [← Real.log_exp (3 : ℝ)]
    exact Real.log_le_log (Real.exp_pos 3) hT
  have hlog0 : 0 < Real.log T :=
    (by norm_num : (0 : ℝ) < 3).trans_le hlog3
  have hcThird : hughesYoungSmallContour T ≤ (3 : ℝ)⁻¹ := by
    unfold hughesYoungSmallContour
    exact (inv_le_inv₀ hlog0 (show (0 : ℝ) < 3 by norm_num)).2 hlog3
  have hcHalf : hughesYoungSmallContour T < 1 / 2 := by
    calc
      hughesYoungSmallContour T ≤ (3 : ℝ)⁻¹ := hcThird
      _ < 1 / 2 := by norm_num
  have hH : 0 ≤ T / 8 := by positivity
  let f : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungFinitePureSignedCentralAtHeight
        T p.1 (hughesYoungSmallContour T) p.2 h k
          (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) K
  let g : ℝ × ℝ → ℂ := fun p =>
    (hughesYoungHeightWeight T p.1 : ℂ) *
      hughesYoungActiveReassembledSignedCentralAtHeight
        T p.1 (hughesYoungSmallContour T) p.2 h k
          (hughesYoungReducedLeft h k)
          (hughesYoungReducedRight h k) R K
  let ν : Measure ℝ := volume.restrict (Set.uIoc (-(T / 8)) (T / 8))
  have hf : Integrable f (volume.prod ν) := by
    simpa only [f, ν] using
      integrable_uncurry_heightWeight_mul_hughesYoungFinitePureSignedCentralAtHeight
        hT0 hc.1 hcHalf hH hh hk K
  have hg0 :=
    integrable_uncurry_heightWeight_mul_hughesYoungActiveReassembledSignedCentralAtHeight
      hT0 hc.1 hH hh hk R K
  have hg : Integrable g (volume.prod ν) := by
    simpa only [g, ν, Function.comp_apply, Prod.swap_prod_mk] using hg0.swap
  have hdouble :
      (∫ t : ℝ, ∫ u : ℝ, f (t, u) - g (t, u) ∂ν) =
        (∫ t : ℝ, ∫ u : ℝ, f (t, u) ∂ν) -
          (∫ t : ℝ, ∫ u : ℝ, g (t, u) ∂ν) := by
    calc
      (∫ t : ℝ, ∫ u : ℝ, f (t, u) - g (t, u) ∂ν) =
          ∫ p : ℝ × ℝ, (f p - g p) ∂volume.prod ν :=
        (integral_prod (fun p => f p - g p) (hf.sub hg)).symm
      _ = (∫ p : ℝ × ℝ, f p ∂volume.prod ν) -
          ∫ p : ℝ × ℝ, g p ∂volume.prod ν := integral_sub hf hg
      _ = (∫ t : ℝ, ∫ u : ℝ, f (t, u) ∂ν) -
          (∫ t : ℝ, ∫ u : ℝ, g (t, u) ∂ν) := by
        congr 1
        · exact integral_prod f hf
        · exact integral_prod g hg
  have hinterval : -(T / 8) ≤ T / 8 := by linarith
  simpa only [f, g, ν, intervalIntegral.integral_of_le hinterval,
    Set.uIoc_of_le hinterval,
    hughesYoungActiveComplementSignedCentralAtHeight, mul_sub] using hdouble

/-- The integrated complement is exactly the pure source minus the active
source after summing the positive mollifier pairs. -/
theorem hughesYoungActiveComplementIntegratedCentral_eq_pure_sub_active
    {T : ℝ} (hT : Real.exp 3 ≤ T) (R K : ℕ) :
    hughesYoungActiveComplementIntegratedCentral T R K =
      hughesYoungFinitePureIntegratedCentral T K -
        hughesYoungActiveReassembledIntegratedCentral T R K := by
  classical
  unfold hughesYoungActiveComplementIntegratedCentral
    hughesYoungFinitePureIntegratedCentral
    hughesYoungActiveReassembledIntegratedCentral
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h hhmem
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hkmem
  have hh : 0 < h := (Finset.mem_Icc.mp hhmem).1
  have hk : 0 < k := (Finset.mem_Icc.mp hkmem).1
  rw [integral_hughesYoungActiveComplementSignedCentralAtHeight_eq_sub
    hT hh hk R K]

/-- The global active-source discrepancy is exactly the negative of the
integrated signed complement. -/
theorem hughesYoungActiveSourceDiscrepancy_eq_neg_activeComplement
    {T : ℝ} (hT : Real.exp 3 ≤ T) (R K : ℕ) :
    hughesYoungActiveSourceDiscrepancy T R K =
      -hughesYoungActiveComplementIntegratedCentral T R K := by
  unfold hughesYoungActiveSourceDiscrepancy
  rw [hughesYoungActiveComplementIntegratedCentral_eq_pure_sub_active hT]
  ring

/-- One dyadic box on the opening line, before the physical product cutoff is
imposed. -/
noncomputable def hughesYoungDyadicIntegratedHighBox
    (q a b i j : ℕ) (t H : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound i),
    ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound j),
      (hughesYoungFullDyadicCutoff i ((a * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff j ((b * n : ℕ) : ℝ) : ℂ) *
        ∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u (m, n)

/-- The same dyadic box after moving the Mellin line to the native small
contour. -/
noncomputable def hughesYoungDyadicIntegratedSmallBox
    (T : ℝ) (a b i j : ℕ) (t H : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound i),
    ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound j),
      (hughesYoungFullDyadicCutoff i ((a * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff j ((b * n : ℕ) : ℝ) : ℂ) *
        ∫ u in -H..H,
          hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)

/-- Opening-line contribution of every box in the finite rectangle omitted
by the physical product cutoff. -/
noncomputable def hughesYoungInactiveIntegratedHigh
    (q a b R K : ℕ) (t H : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
    hughesYoungDyadicIntegratedHighBox q a b ij.1 ij.2 t H

/-- Small-line contribution of the identical finite inactive family. -/
noncomputable def hughesYoungInactiveIntegratedSmall
    (T : ℝ) (a b R K : ℕ) (t H : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
    ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
          ∫ u in -H..H,
            hughesYoungRightPairTerm t (hughesYoungSmallContour T) u (m, n)

/-- Smooth pair weight of the finite inactive dyadic family. -/
noncomputable def hughesYoungInactiveDyadicWeight
    (a b R K m n : ℕ) : ℝ :=
  ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
    hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
      hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ)

/-- Smooth pair weight of the complete finite dyadic rectangle. -/
noncomputable def hughesYoungRectangularDyadicWeight
    (a b K m n : ℕ) : ℝ :=
  ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
    hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
      hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ)

/-- Exact active/inactive split of the finite rectangular pair weight. -/
theorem hughesYoungRectangularDyadicWeight_eq_active_add_inactive
    (a b R K m n : ℕ) :
    hughesYoungRectangularDyadicWeight a b K m n =
      hughesYoungActiveDyadicWeight a b R K m n +
        hughesYoungInactiveDyadicWeight a b R K m n := by
  classical
  unfold hughesYoungRectangularDyadicWeight
    hughesYoungActiveDyadicWeight hughesYoungInactiveDyadicWeight
    hughesYoungCompleteDyadicRectangle hughesYoungActiveDyadicBoxes
    hughesYoungInactiveDyadicBoxes
  exact (Finset.sum_filter_add_sum_filter_not
    (s := (Finset.range (K + 2)).product (Finset.range (K + 2)))
    (p := fun ij => hughesYoungFullDyadicScale ij.1 *
      hughesYoungFullDyadicScale ij.2 ≤ ((a * b * R : ℕ) : ℝ))
    (f := fun ij =>
      hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
        hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ))).symm

theorem hughesYoungInactiveDyadicWeight_nonneg
    (a b R K m n : ℕ) :
    0 ≤ hughesYoungInactiveDyadicWeight a b R K m n := by
  unfold hughesYoungInactiveDyadicWeight
  exact Finset.sum_nonneg fun ij _ => mul_nonneg
    (hughesYoungFullDyadicCutoff_nonneg_nat _ _)
    (hughesYoungFullDyadicCutoff_nonneg_nat _ _)

/-- A finite complete rectangle has no more than the unit mass of the full
locally finite dyadic partition. -/
theorem hughesYoungRectangularDyadicWeight_le_one
    {a b K m n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) :
    hughesYoungRectangularDyadicWeight a b K m n ≤ 1 := by
  let F : ℕ × ℕ → ℝ := fun ij =>
    hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) *
      hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ)
  have hsummable : Summable F :=
    (summable_hughesYoungFullDyadicCutoff_nat (a * m)).mul_of_nonneg
      (summable_hughesYoungFullDyadicCutoff_nat (b * n))
      (fun _ => hughesYoungFullDyadicCutoff_nonneg_nat _ _)
      (fun _ => hughesYoungFullDyadicCutoff_nonneg_nat _ _)
  have hpartial :
      (∑ ij ∈ hughesYoungCompleteDyadicRectangle K, F ij) ≤
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
  unfold hughesYoungRectangularDyadicWeight
  exact hpartial.trans_eq hfull

/-- The inactive family has coefficient at most one. -/
theorem hughesYoungInactiveDyadicWeight_le_one
    {a b R K m n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) :
    hughesYoungInactiveDyadicWeight a b R K m n ≤ 1 := by
  have hsplit := hughesYoungRectangularDyadicWeight_eq_active_add_inactive
    a b R K m n
  have hrect := hughesYoungRectangularDyadicWeight_le_one
    (K := K) ha hb hm hn
  have hactive := hughesYoungActiveDyadicWeight_nonneg a b R K m n
  linarith

/-- No inactive dyadic mass can meet the product-truncated source.  This is
the exact support statement needed before estimating the omitted contour as
a high-product tail. -/
theorem hughesYoungInactiveDyadicWeight_eq_zero_of_mul_le
    {a b R K m n : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hm : 0 < m) (hn : 0 < n) (hmn : m * n ≤ R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1)) :
    hughesYoungInactiveDyadicWeight a b R K m n = 0 := by
  have hsplit := hughesYoungRectangularDyadicWeight_eq_active_add_inactive
    a b R K m n
  have hrect := hughesYoungRectangularDyadicWeight_le_one
    (K := K) ha hb hm hn
  have hactive := hughesYoungActiveDyadicWeight_eq_one
    ha hb hm hn hmn hcover
  have hinactive := hughesYoungInactiveDyadicWeight_nonneg a b R K m n
  linarith

/-- Opening-line pair sum carried by the inactive finite rectangle. -/
noncomputable def hughesYoungInactiveHighPairSum
    (q a b R K : ℕ) (t u : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ,
    (hughesYoungInactiveDyadicWeight a b R K p.1 p.2 : ℂ) *
      hughesYoungRightPairTerm t (2 * q) u p

theorem summable_hughesYoungInactiveHighPairSum
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t u : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      (hughesYoungInactiveDyadicWeight a b R K p.1 p.2 : ℂ) *
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
      abs_of_nonneg (hughesYoungInactiveDyadicWeight_nonneg a b R K m n)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (hughesYoungInactiveDyadicWeight_le_one ha hb
        (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn)))

/-- Every inactive opening-line summand is supported in the literal product
tail and has coefficient norm at most one. -/
theorem norm_inactiveHighPairSum_term_le_tail
    {q a b R K : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u : ℝ) (p : ℕ × ℕ) :
    ‖(hughesYoungInactiveDyadicWeight a b R K p.1 p.2 : ℂ) *
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
  · have hweight := hughesYoungInactiveDyadicWeight_eq_zero_of_mul_le
      ha hb hmPos hnPos hmn hcover
    have hprod : ¬ (R : ℝ) < (m : ℝ) * n := by
      exact_mod_cast (not_lt.mpr hmn)
    simp [hweight, hprod]
  · have hprodNat : R < m * n := Nat.lt_of_not_ge hmn
    have hprod : (R : ℝ) < (m : ℝ) * n := by exact_mod_cast hprodNat
    rw [if_pos hprod, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hughesYoungInactiveDyadicWeight_nonneg a b R K m n)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (hughesYoungInactiveDyadicWeight_le_one ha hb hmPos hnPos)

theorem norm_hughesYoungInactiveHighPairSum_le
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (t u : ℝ) {η : ℝ} (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ‖hughesYoungInactiveHighPairSum q a b R K t u‖ ≤
      ‖hughesYoungRightContourWeight t (2 * q) u‖ *
        (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
        hughesYoungReferenceDivisorPairMass η := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  unfold hughesYoungInactiveHighPairSum
  calc
    ‖∑' p : ℕ × ℕ,
        (hughesYoungInactiveDyadicWeight a b R K p.1 p.2 : ℂ) *
          hughesYoungRightPairTerm t (2 * q) u p‖ ≤
        ∑' p : ℕ × ℕ,
          ‖(hughesYoungInactiveDyadicWeight a b R K p.1 p.2 : ℂ) *
            hughesYoungRightPairTerm t (2 * q) u p‖ :=
      norm_tsum_le_tsum_norm
        (summable_hughesYoungInactiveHighPairSum hq ha hb t u).norm
    _ ≤ ∑' p : ℕ × ℕ,
        ‖if (R : ℝ) < (p.1 : ℝ) * p.2 then
            hughesYoungRightPairTerm t (2 * q) u p else 0‖ := by
      exact (summable_hughesYoungInactiveHighPairSum hq ha hb t u).norm.tsum_le_tsum
        (norm_inactiveHighPairSum_term_le_tail ha hb hcover t u)
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

/-- The inactive weighted pair series is exactly the finite inactive box
sum used by the contour-transfer theorem. -/
theorem hughesYoungInactiveHighPairSum_eq_finiteBoxes
    {q a b R K : ℕ} (ha : 0 < a) (hb : 0 < b) (t u : ℝ) :
    hughesYoungInactiveHighPairSum q a b R K t u =
      ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            hughesYoungFullDyadicHighPairTerm
              q a b ij.1 ij.2 t u (m, n) := by
  unfold hughesYoungInactiveHighPairSum hughesYoungInactiveDyadicWeight
  let S := hughesYoungInactiveDyadicBoxes a b R K
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
              hughesYoungFullDyadicHighPairTerm
                q a b ij.1 ij.2 t u (m, n) := by
      apply Finset.sum_congr rfl
      intro ij hij
      exact tsum_hughesYoungFullDyadicHighPairTerm_eq_finiteSum ha hb t u

theorem hughesYoungInactiveIntegratedHigh_eq_intervalIntegral
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (t H : ℝ) :
    hughesYoungInactiveIntegratedHigh q a b R K t H =
      ∫ u in -H..H,
        hughesYoungInactiveHighPairSum q a b R K t u := by
  unfold hughesYoungInactiveIntegratedHigh
    hughesYoungDyadicIntegratedHighBox
  simp_rw [hughesYoungInactiveHighPairSum_eq_finiteBoxes ha hb]
  symm
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro ij hij
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro n hn
        unfold hughesYoungFullDyadicHighPairTerm
        simp
      · intro n hn
        exact (continuous_hughesYoungFullDyadicHighPairTerm
          hq a b ij.1 ij.2 t (m, n)).intervalIntegrable
            (μ := volume) (-H) H
    · intro m hm
      exact (continuous_finsetSum
        (Finset.Icc 1 (hughesYoungFullDyadicBound ij.2))
        (fun n hn => continuous_hughesYoungFullDyadicHighPairTerm
          hq a b ij.1 ij.2 t (m, n))).intervalIntegrable
            (μ := volume) (-H) H
  · intro ij hij
    exact (continuous_finsetSum
      (Finset.Icc 1 (hughesYoungFullDyadicBound ij.1))
      (fun m hm => continuous_finsetSum
        (Finset.Icc 1 (hughesYoungFullDyadicBound ij.2))
        (fun n hn => continuous_hughesYoungFullDyadicHighPairTerm
          hq a b ij.1 ij.2 t (m, n)))).intervalIntegrable
            (μ := volume) (-H) H

/-- The complete finite dyadic rectangle on the opening line. -/
noncomputable def hughesYoungRectangularIntegratedHigh
    (q a b K : ℕ) (t H : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
    hughesYoungDyadicIntegratedHighBox q a b ij.1 ij.2 t H

/-- Exact active/inactive decomposition on the opening line. -/
theorem hughesYoungRectangularIntegratedHigh_eq_active_add_inactive
    (q a b R K : ℕ) (t H : ℝ) :
    hughesYoungRectangularIntegratedHigh q a b K t H =
      hughesYoungActiveIntegratedHigh q a b R K t H +
        hughesYoungInactiveIntegratedHigh q a b R K t H := by
  classical
  unfold hughesYoungRectangularIntegratedHigh
    hughesYoungActiveIntegratedHigh hughesYoungInactiveIntegratedHigh
    hughesYoungDyadicIntegratedHighBox hughesYoungActiveDyadicBoxes
    hughesYoungInactiveDyadicBoxes hughesYoungCompleteDyadicRectangle
  exact (Finset.sum_filter_add_sum_filter_not
    (s := (Finset.range (K + 2)).product (Finset.range (K + 2)))
    (p := fun ij => hughesYoungFullDyadicScale ij.1 *
      hughesYoungFullDyadicScale ij.2 ≤ ((a * b * R : ℕ) : ℝ))
    (f := fun ij =>
      ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
        ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
          (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
            (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
            ∫ u in -H..H,
              hughesYoungRightPairTerm t (2 * q) u (m, n))).symm

/-- Exact active/inactive decomposition on the small line. -/
theorem hughesYoungRectangularIntegratedSmall_eq_active_add_inactive
    (T : ℝ) (a b R K : ℕ) (t H : ℝ) :
    (∑ ij ∈ hughesYoungCompleteDyadicRectangle K,
        hughesYoungDyadicIntegratedSmallBox T a b ij.1 ij.2 t H) =
      hughesYoungActiveIntegratedSmall T a b R K t H +
        hughesYoungInactiveIntegratedSmall T a b R K t H := by
  classical
  unfold hughesYoungActiveIntegratedSmall hughesYoungInactiveIntegratedSmall
    hughesYoungDyadicIntegratedSmallBox hughesYoungActiveDyadicBoxes
    hughesYoungInactiveDyadicBoxes hughesYoungCompleteDyadicRectangle
  exact (Finset.sum_filter_add_sum_filter_not
    (s := (Finset.range (K + 2)).product (Finset.range (K + 2)))
    (p := fun ij => hughesYoungFullDyadicScale ij.1 *
      hughesYoungFullDyadicScale ij.2 ≤ ((a * b * R : ℕ) : ℝ))
    (f := fun ij =>
      ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
        ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
          (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
            (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
            ∫ u in -H..H,
              hughesYoungRightPairTerm t
                (hughesYoungSmallContour T) u (m, n))).symm

set_option maxHeartbeats 2000000 in
/-- The omitted finite dyadic family may be shifted as one signed object.
Every actual contour shift is still performed on a finite positive pair;
the outer subtraction is made only after those kernel-checked shifts. -/
theorem tendsto_hughesYoungInactiveIntegratedHigh_sub_small_zero
    {q : ℕ} (hq : 0 < q) {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (a b R K : ℕ) :
    Tendsto (fun H : ℝ =>
      hughesYoungInactiveIntegratedHigh q a b R K t H -
        hughesYoungInactiveIntegratedSmall T a b R K t H)
      atTop (𝓝 0) := by
  classical
  unfold hughesYoungInactiveIntegratedHigh
    hughesYoungInactiveIntegratedSmall
    hughesYoungDyadicIntegratedHighBox
  let D : ℝ → (ℕ × ℕ) → ℕ → ℕ → ℂ := fun H ij m n =>
    ((hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
      (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ)) *
      ((∫ u in -H..H, hughesYoungRightPairTerm t (2 * q) u (m, n)) -
        ∫ u in -H..H,
          hughesYoungRightPairTerm t
            (hughesYoungSmallContour T) u (m, n))
  have hsum : Tendsto
      (fun H : ℝ =>
        ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
          ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              D H ij m n)
      atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      (show Tendsto
          (fun H : ℝ =>
            ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
              ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
                ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
                  D H ij m n)
          atTop
          (𝓝 (∑ _ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
            ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound _ij.1),
              ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound _ij.2),
                (0 : ℂ))) from by
          apply tendsto_finsetSum
          intro ij hij
          apply tendsto_finsetSum
          intro m hm
          apply tendsto_finsetSum
          intro n hn
          have hm0 : 0 < m :=
            Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1
          have hn0 : 0 < n :=
            Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1
          have hpair := tendsto_hughesYoungRightPairTerm_vertical_sub_zero
            (p := (m, n))
            (c₀ := hughesYoungSmallContour T)
            (c₁ := (2 * q : ℝ))
            t hm0 hn0 (hughesYoungSmallContour_spec hT).1
            (by
              have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
              have hsmallLe := (hughesYoungSmallContour_spec hT).2.1
              linarith)
          simpa only [mul_zero] using hpair.const_mul
            ((hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
              (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ)))
  convert hsum using 1
  funext H
  dsimp only [D]
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- Whole-line small-contour value of the finite inactive dyadic family. -/
noncomputable def hughesYoungInactiveWholeSmall
    (T : ℝ) (a b R K : ℕ) (t : ℝ) : ℂ :=
  ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
    ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
          (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
          ∫ u : ℝ,
            hughesYoungRightPairTerm t
              (hughesYoungSmallContour T) u (m, n)

/-- The finite inactive small-contour family converges to its whole-line
value.  This is a finite dominated-convergence step; every positive pair is
integrable on the Hughes--Young small line. -/
theorem tendsto_hughesYoungInactiveIntegratedSmall_to_whole
    {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) (a b R K : ℕ) :
    Tendsto (fun H : ℝ =>
      hughesYoungInactiveIntegratedSmall T a b R K t H)
      atTop (𝓝 (hughesYoungInactiveWholeSmall T a b R K t)) := by
  unfold hughesYoungInactiveIntegratedSmall hughesYoungInactiveWholeSmall
  apply tendsto_finsetSum
  intro ij hij
  apply tendsto_finsetSum
  intro m hm
  apply tendsto_finsetSum
  intro n hn
  apply Filter.Tendsto.const_mul
  have hm0 : 0 < m := by simpa using (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < n := by simpa using (Finset.mem_Icc.mp hn).1
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungRightPairTerm_small hT ht hm0 hn0)
    tendsto_neg_atTop_atBot tendsto_id

/-- The opening-line inactive family converges to the whole small-contour
value of precisely the same omitted dyadic boxes. -/
theorem tendsto_hughesYoungInactiveIntegratedHigh_to_wholeSmall
    {q : ℕ} (hq : 0 < q) {T t : ℝ} (hT : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) (a b R K : ℕ) :
    Tendsto (fun H : ℝ =>
      hughesYoungInactiveIntegratedHigh q a b R K t H)
      atTop (𝓝 (hughesYoungInactiveWholeSmall T a b R K t)) := by
  have hsmall := tendsto_hughesYoungInactiveIntegratedSmall_to_whole
    hT ht a b R K
  have hdiff := tendsto_hughesYoungInactiveIntegratedHigh_sub_small_zero
    hq (t := t) hT a b R K
  have hadd := hsmall.add hdiff
  convert hadd using 1
  · funext H
    ring
  · simp

theorem integrable_hughesYoungInactiveHighPairSum
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T)) :
    Integrable (fun u : ℝ =>
      hughesYoungInactiveHighPairSum q a b R K t u) := by
  let C : ℝ := 256 * Real.exp (400 * (q : ℝ) ^ 2) *
    ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
    (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
    hughesYoungReferenceDivisorPairMass η
  let K₀ : ℝ := 625 * (2 * (q : ℝ) + 1) ^ 8
  let g : ℝ → ℝ := fun u =>
    Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (4 * q + 16)
  have hg : Integrable g :=
    integrable_exp_neg_84_mul_one_add_abs_pow (4 * q + 16)
  have hmeas : AEStronglyMeasurable (fun u : ℝ =>
      hughesYoungInactiveHighPairSum q a b R K t u) := by
    have hc : (1 / 2 : ℝ) < 2 * q := by
      have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
      linarith
    have hpmeas : ∀ p : ℕ × ℕ, AEMeasurable (fun u : ℝ =>
        (hughesYoungInactiveDyadicWeight a b R K p.1 p.2 : ℂ) *
          hughesYoungRightPairTerm t (2 * q) u p) := by
      intro p
      exact (continuous_const.mul
        (continuous_hughesYoungRightPairTerm t hc p)).aemeasurable
    unfold hughesYoungInactiveHighPairSum
    exact (AEMeasurable.tsum hpmeas).aestronglyMeasurable
  apply (hg.const_mul (C * K₀)).mono' hmeas
  filter_upwards with u
  have hweight :=
    norm_hughesYoungRightContourWeight_even_le_on_height_support hT ht hq u
  have htail := norm_hughesYoungInactiveHighPairSum_le
    hq ha hb hR hcover t u hη0 hη
  have hexp :
      Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) =
        Real.exp (400 * (q : ℝ) ^ 2) * Real.exp (-84 * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hbasepow :
      ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) =
        ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          (1 + |u|) ^ (4 * q + 8) := by
    rw [mul_pow]
  calc
    ‖hughesYoungInactiveHighPairSum q a b R K t u‖ ≤
        ‖hughesYoungRightContourWeight t (2 * q) u‖ *
          (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η := htail
    _ ≤ (160000 * (2 * (q : ℝ) + 1) ^ 8 *
          Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
          ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) *
          (1 + |u|) ^ 8) *
          (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η := by
      gcongr
      exact hughesYoungReferenceDivisorPairMass_nonneg η
    _ = (C * K₀) * g u := by
      rw [hexp, hbasepow]
      unfold C K₀ g
      ring

/-- The `hughesYoungInactiveWholeHigh` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveWholeHigh
    (q a b R K : ℕ) (t : ℝ) : ℂ :=
  ∫ u : ℝ, hughesYoungInactiveHighPairSum q a b R K t u

theorem tendsto_hughesYoungInactiveIntegratedHigh_to_wholeHigh
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hT : 1 ≤ T) (ht : t ∈ Set.Icc (T / 4) (4 * T)) :
    Tendsto (fun H : ℝ =>
      hughesYoungInactiveIntegratedHigh q a b R K t H)
      atTop (𝓝 (hughesYoungInactiveWholeHigh q a b R K t)) := by
  rw [show (fun H : ℝ =>
      hughesYoungInactiveIntegratedHigh q a b R K t H) =
      (fun H : ℝ => ∫ u in -H..H,
        hughesYoungInactiveHighPairSum q a b R K t u) by
    funext H
    exact hughesYoungInactiveIntegratedHigh_eq_intervalIntegral
      hq ha hb t H]
  exact MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_hughesYoungInactiveHighPairSum
      hq ha hb hR hcover η hη0 hη hT ht)
    tendsto_neg_atTop_atBot tendsto_id

/-- The cancellation-preserving inactive small-contour source is exactly
the high-line product-tail integral. -/
theorem hughesYoungInactiveWholeSmall_eq_wholeHigh
    {q a b R K : ℕ} (hq : 0 < q) (ha : 0 < a) (hb : 0 < b)
    (hR : 0 < R)
    (hcover : ((a * b * R : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K + 1))
    (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T t : ℝ} (hTexp : Real.exp 1 ≤ T)
    (ht : t ∈ Set.Icc (T / 4) (4 * T)) :
    hughesYoungInactiveWholeSmall T a b R K t =
      hughesYoungInactiveWholeHigh q a b R K t := by
  have hT : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
  exact tendsto_nhds_unique
    (tendsto_hughesYoungInactiveIntegratedHigh_to_wholeSmall
      hq hTexp ht a b R K)
    (tendsto_hughesYoungInactiveIntegratedHigh_to_wholeHigh
      hq ha hb hR hcover η hη0 hη hT ht)

/-- Uniform negative-power bound for the whole inactive small-contour
family.  Its proof is performed on the absolutely convergent opening line
and transported back by the exact contour identity above. -/
theorem exists_norm_hughesYoungInactiveWholeSmall_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {a b R K : ℕ} {T t : ℝ},
      0 < a → 0 < b → 0 < R →
      ((a * b * R : ℕ) : ℝ) ≤ hughesYoungDyadicRatio ^ (K + 1) →
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) →
      ‖hughesYoungInactiveWholeSmall T a b R K t‖ ≤
        (256 * Real.exp (400 * (q : ℝ) ^ 2) *
          ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
          (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
          hughesYoungReferenceDivisorPairMass η) * L := by
  let K₀ : ℝ := 625 * (2 * (q : ℝ) + 1) ^ 8
  let g : ℝ → ℝ := fun u =>
    Real.exp (-84 * u ^ 2) * (1 + |u|) ^ (4 * q + 16)
  have hg : Integrable g :=
    integrable_exp_neg_84_mul_one_add_abs_pow (4 * q + 16)
  have hg0 : 0 ≤ ∫ u : ℝ, g u :=
    integral_nonneg fun u => mul_nonneg (by positivity) (by positivity)
  let L : ℝ := K₀ * (1 + ∫ u : ℝ, g u)
  have hK₀ : 0 < K₀ := by unfold K₀; positivity
  have hL : 0 < L := by
    unfold L
    exact mul_pos hK₀ (by linarith)
  refine ⟨L, hL, ?_⟩
  intro a b R K T t ha hb hR hcover hTexp ht
  have hT : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
  let C : ℝ := 256 * Real.exp (400 * (q : ℝ) ^ 2) *
    ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
    (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
    hughesYoungReferenceDivisorPairMass η
  have hC0 : 0 ≤ C := by
    unfold C
    exact mul_nonneg (by positivity)
      (hughesYoungReferenceDivisorPairMass_nonneg η)
  rw [hughesYoungInactiveWholeSmall_eq_wholeHigh
    hq ha hb hR hcover η hη0 hη hTexp ht]
  unfold hughesYoungInactiveWholeHigh
  calc
    ‖∫ u : ℝ, hughesYoungInactiveHighPairSum q a b R K t u‖ ≤
        ∫ u : ℝ, (C * K₀) * g u := by
      apply norm_integral_le_of_norm_le (hg.const_mul (C * K₀))
      filter_upwards with u
      have hweight :=
        norm_hughesYoungRightContourWeight_even_le_on_height_support
          hT ht hq u
      have htail := norm_hughesYoungInactiveHighPairSum_le
        hq ha hb hR hcover t u hη0 hη
      have hexp :
          Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) =
            Real.exp (400 * (q : ℝ) ^ 2) * Real.exp (-84 * u ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hbasepow :
          ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) =
            ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
              (1 + |u|) ^ (4 * q + 8) := by
        rw [mul_pow]
      calc
        ‖hughesYoungInactiveHighPairSum q a b R K t u‖ ≤
            ‖hughesYoungRightContourWeight t (2 * q) u‖ *
              (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
              hughesYoungReferenceDivisorPairMass η := htail
        _ ≤ (160000 * (2 * (q : ℝ) + 1) ^ 8 *
              Real.exp (400 * (q : ℝ) ^ 2 - 84 * u ^ 2) *
              ((7 + 2 * (q : ℝ)) * T * (1 + |u|)) ^ (4 * q + 8) *
              (1 + |u|) ^ 8) *
              (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
              hughesYoungReferenceDivisorPairMass η := by
            gcongr
            exact hughesYoungReferenceDivisorPairMass_nonneg η
        _ = (C * K₀) * g u := by
            rw [hexp, hbasepow]
            unfold C K₀ g
            ring
    _ = (C * K₀) * (∫ u : ℝ, g u) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ (C * K₀) * (1 + ∫ u : ℝ, g u) := by
      exact mul_le_mul_of_nonneg_left (by linarith)
        (mul_nonneg hC0 hK₀.le)
    _ = C * L := by
      unfold L
      ring
    _ = _ := by rfl

/-- The complete mollifier-weighted omitted dyadic family after the
cancellation-preserving contour transfer. -/
noncomputable def hughesYoungInactiveWholeTwistedIntegrand
    (T : ℝ) (R K : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungInactiveWholeSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t

/-- Height average of the complete omitted dyadic family. -/
noncomputable def hughesYoungInactiveWholeSmoothedMoment
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungInactiveWholeTwistedIntegrand T R K t

/-- Uniform pointwise opening-line estimate after the actual mollifier
indices have been inserted. -/
theorem exists_norm_hughesYoungInactiveWholeTwistedIntegrand_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 0 < R →
      (∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (((hughesYoungReducedLeft h k) *
            (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
              hughesYoungDyadicRatio ^ (K + 1)) →
      ∀ t ∈ Set.Icc (T / 4) (4 * T),
        ‖hughesYoungInactiveWholeTwistedIntegrand T R K t‖ ≤
          hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) *
            ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
              ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
              (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
              hughesYoungReferenceDivisorPairMass η) * L) := by
  classical
  obtain ⟨L, hL, hpair⟩ :=
    exists_norm_hughesYoungInactiveWholeSmall_le q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro T R K hT hR hcover t ht
  let B : ℝ :=
    (256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L
  have hB0 : 0 ≤ B := by
    have hRpow : 0 ≤ (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) :=
      Real.rpow_nonneg (by positivity) _
    have hmass : 0 ≤ hughesYoungReferenceDivisorPairMass η :=
      hughesYoungReferenceDivisorPairMass_nonneg η
    have hT0 : 0 ≤ T := (Real.exp_pos 1).le.trans hT
    have hbase : 0 ≤ (7 + 2 * (q : ℝ)) * T :=
      mul_nonneg (by positivity) hT0
    unfold B
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity) (pow_nonneg hbase _)) hRpow)
        hmass) hL.le
  have hpi : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  unfold hughesYoungInactiveWholeTwistedIntegrand
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
            hughesYoungInactiveWholeSmall T
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t‖ ≤
        ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            ‖hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungInactiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _h _hh => norm_sum_le _ _)
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖) *
              (1 / Real.pi) * B := by
      apply Finset.sum_le_sum
      intro h hhmem
      apply Finset.sum_le_sum
      intro k hkmem
      have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
      have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
      have hmoll := norm_hughesYoungMollifierPairTerm_le T t hh hk
      have hinactive := hpair
        (hughesYoungReducedLeft_pos hh)
        (hughesYoungReducedRight_pos hh hk) hR
        (hcover h hhmem k hkmem) hT ht
      rw [norm_mul, norm_mul, hpi]
      calc
        ‖hughesYoungMollifierPairTerm T t h k‖ * (1 / Real.pi) *
            ‖hughesYoungInactiveWholeSmall T
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t‖ ≤
          (‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖) *
            (1 / Real.pi) * B := by
              gcongr
        _ = _ := rfl
    _ = hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) * B := by
      unfold hughesYoungMollifierCoefficientMass
      let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
      let a : ℕ → ℝ := fun n => ‖shortMobiusSquareCoeff T n‖
      have hprod :
          (∑ h ∈ S, a h) * (∑ k ∈ S, a k) =
            ∑ h ∈ S, ∑ k ∈ S, a h * a k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro h _hh
        rw [Finset.mul_sum]
      calc
        (∑ h ∈ S, ∑ k ∈ S, a h * a k * (1 / Real.pi) * B) =
            (∑ h ∈ S, ∑ k ∈ S, a h * a k) * (1 / Real.pi) * B := by
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro h _hh
          rw [Finset.sum_mul, Finset.sum_mul]
        _ = ((∑ h ∈ S, a h) * (∑ k ∈ S, a k)) *
              (1 / Real.pi) * B := by rw [hprod]
        _ = (∑ h ∈ S, a h) ^ 2 * (1 / Real.pi) * B := by rw [pow_two]
    _ = _ := by rfl

/-- The omitted dyadic source has an arbitrary negative opening-line power
after the physical height average.  The exact exponent is deliberately
retained for the final native scale choice. -/
theorem exists_norm_hughesYoungInactiveWholeSmoothedMoment_le
    (q : ℕ) (hq : 0 < q) (η : ℝ) (hη0 : 0 < η)
    (hη : η < 2 * (q : ℝ) - 1 / 2) :
    ∃ L : ℝ, 0 < L ∧ ∀ {T : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → 0 < R →
      (∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (((hughesYoungReducedLeft h k) *
            (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
              hughesYoungDyadicRatio ^ (K + 1)) →
      ‖hughesYoungInactiveWholeSmoothedMoment T R K‖ ≤
        (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
            ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
            (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
            hughesYoungReferenceDivisorPairMass η) * L) := by
  obtain ⟨L, hL, hpoint⟩ :=
    exists_norm_hughesYoungInactiveWholeTwistedIntegrand_le q hq η hη0 hη
  refine ⟨L, hL, ?_⟩
  intro T R K hT hR hcover
  let A : ℝ := hughesYoungMollifierCoefficientMass T ^ 2 *
    (1 / Real.pi) *
    ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L)
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hA0 : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (hughesYoungMollifierCoefficientMass_nonneg T) 2)
        (by positivity))
      (mul_nonneg
        (mul_nonneg (by positivity)
          (hughesYoungReferenceDivisorPairMass_nonneg η)) hL.le)
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  unfold hughesYoungInactiveWholeSmoothedMoment
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) = ∫ _t in Set.Icc (T / 4) (4 * T), A by
        exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    unfold A
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · rw [hw]
      simp only [ofReal_zero, zero_mul, norm_zero]
      simpa only [B] using Set.indicator_nonneg (fun _ _ => hA0) t
    · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
        hughesYoungHeightWeight_support hT0 hw
      have hsource := hpoint hT hR hcover t ht
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      change _ ≤ Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
      rw [Set.indicator_of_mem ht]
      calc
        hughesYoungHeightWeight T t *
            ‖hughesYoungInactiveWholeTwistedIntegrand T R K t‖ ≤
          1 * ‖hughesYoungInactiveWholeTwistedIntegrand T R K t‖ := by gcongr
        _ ≤ A := by simpa only [one_mul, A] using hsource

/-! ## Exact finite inactive source

The contour estimate above applies to the whole inactive source.  The next
definitions retain the identical finite dyadic family on the small line, so
that the off-diagonal projection used by the DFI assembly can be recovered
without taking norms before the diagonal cancellation is exposed. -/

/-- The `hughesYoungInactiveDyadicMoment` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveDyadicMoment
    (T c H : ℝ) (h k R K : ℕ) : ℂ :=
  ∑ ij ∈ hughesYoungInactiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
    hughesYoungFullDyadicIntegratedBox T c H h k ij.1 ij.2

/-- The `hughesYoungInactiveDyadicDiagonal` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveDyadicDiagonal
    (T c H : ℝ) (h k R K : ℕ) : ℂ :=
  ∑ ij ∈ hughesYoungInactiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
    hughesYoungFullDyadicDiagonalBox T c H h k ij.1 ij.2

/-- The `hughesYoungInactiveDyadicOffDiagonal` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveDyadicOffDiagonal
    (T c H : ℝ) (h k R K : ℕ) : ℂ :=
  ∑ ij ∈ hughesYoungInactiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
    hughesYoungLocalizedOffDiagonalBox T c H
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) h k
      (hughesYoungFullDyadicBound ij.1)
      (hughesYoungFullDyadicBound ij.2)

theorem hughesYoungInactiveDyadicMoment_eq_diagonal_add_offDiagonal
    (T c H : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (R K : ℕ) :
    hughesYoungInactiveDyadicMoment T c H h k R K =
      hughesYoungInactiveDyadicDiagonal T c H h k R K +
        hughesYoungInactiveDyadicOffDiagonal T c H h k R K := by
  unfold hughesYoungInactiveDyadicMoment hughesYoungInactiveDyadicDiagonal
    hughesYoungInactiveDyadicOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _hij
  exact hughesYoungFullDyadicIntegratedBox_eq_diagonal_add_offDiagonal
    T c H hh hk

theorem mollifierPair_mul_inactiveIntegratedSmall_eq_finiteDyadicTerms
    (T t H : ℝ) (h k R K : ℕ) :
    hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungInactiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H =
      ∑ ij ∈ hughesYoungInactiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            hughesYoungFullDyadicArithmeticTerm T t
              (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n) := by
  unfold hughesYoungInactiveIntegratedSmall hughesYoungMollifierPairTerm
    hughesYoungFullDyadicArithmeticTerm hughesYoungFiniteArithmeticTerm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij _hij
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  ring

theorem integral_mollifierPair_mul_inactiveIntegratedSmall_eq_inactiveDyadicMoment
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ)
    {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
      (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungInactiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) =
      hughesYoungInactiveDyadicMoment T (hughesYoungSmallContour T)
        H h k R K := by
  classical
  let B := hughesYoungInactiveDyadicBoxes
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc : 0 < hughesYoungSmallContour T := (hughesYoungSmallContour_spec hT).1
  have hterm : ∀ ij ∈ B,
      ∀ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∀ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
      Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFullDyadicArithmeticTerm T t
          (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)) := by
    intro ij _hij m hm n hn
    unfold hughesYoungFullDyadicArithmeticTerm
    have hi := (integrable_weight_mul_hughesYoungFiniteArithmeticTerm
      (p := (m, n)) hT0 hc H hh hk
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)).const_mul
        ((hughesYoungFullDyadicCutoff ij.1
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff ij.2
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hi
  have hfun : (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungInactiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) =
      fun t : ℝ => ∑ ij ∈ B,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungFullDyadicArithmeticTerm T t
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n) := by
    funext t
    rw [mollifierPair_mul_inactiveIntegratedSmall_eq_finiteDyadicTerms]
    simp_rw [B, Finset.mul_sum]
  rw [hfun]
  unfold hughesYoungInactiveDyadicMoment
  rw [MeasureTheory.integral_finsetSum B (fun ij hij =>
    integrable_finsetSum _ (fun m hm =>
      integrable_finsetSum _ (fun n hn => hterm ij hij m hm n hn)))]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hughesYoungFullDyadicIntegratedBox_eq_finiteSum
    T (hughesYoungSmallContour T) H hh hk]
  rw [MeasureTheory.integral_finsetSum _ (fun m hm =>
    integrable_finsetSum _ (fun n hn => hterm ij hij m hm n hn))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [MeasureTheory.integral_finsetSum _ (fun n hn => hterm ij hij m hm n hn)]
  apply Finset.sum_congr rfl
  intro n _hn
  rfl

theorem integrable_weight_mul_mollifierPair_inactiveIntegratedSmall
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ)
    {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungInactiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) := by
  classical
  let B := hughesYoungInactiveDyadicBoxes
    (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hc : 0 < hughesYoungSmallContour T := (hughesYoungSmallContour_spec hT).1
  have hterm : ∀ ij ∈ B,
      ∀ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∀ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
      Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungFullDyadicArithmeticTerm T t
          (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)) := by
    intro ij _hij m hm n hn
    unfold hughesYoungFullDyadicArithmeticTerm
    have hi := (integrable_weight_mul_hughesYoungFiniteArithmeticTerm
      (p := (m, n)) hT0 hc H hh hk
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1)).const_mul
        ((hughesYoungFullDyadicCutoff ij.1
          ((hughesYoungReducedLeft h k * m : ℕ) : ℝ) : ℂ) *
        (hughesYoungFullDyadicCutoff ij.2
          ((hughesYoungReducedRight h k * n : ℕ) : ℝ) : ℂ))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hi
  have hfun : (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungInactiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) =
      fun t : ℝ => ∑ ij ∈ B,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            (hughesYoungHeightWeight T t : ℂ) *
              hughesYoungFullDyadicArithmeticTerm T t
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n) := by
    funext t
    rw [mollifierPair_mul_inactiveIntegratedSmall_eq_finiteDyadicTerms]
    simp_rw [B, Finset.mul_sum]
  rw [hfun]
  exact integrable_finsetSum B (fun ij hij =>
    integrable_finsetSum _ (fun m hm =>
      integrable_finsetSum _ (fun n hn => hterm ij hij m hm n hn)))

/-- The `hughesYoungInactiveFiniteTwistedIntegrand` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveFiniteTwistedIntegrand
    (T H : ℝ) (R K : ℕ) (t : ℝ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
        hughesYoungInactiveIntegratedSmall T
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H

/-- The `hughesYoungInactiveFiniteSmoothedMoment` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveFiniteSmoothedMoment
    (T H : ℝ) (R K : ℕ) : ℂ :=
  ∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungInactiveFiniteTwistedIntegrand T H R K t

/-- The `hughesYoungInactiveFiniteDiagonal` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveFiniteDiagonal
    (T H : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungInactiveDyadicDiagonal T (hughesYoungSmallContour T)
        H h k R K

/-- The `hughesYoungInactiveFiniteOffDiagonal` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveFiniteOffDiagonal
    (T H : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      hughesYoungInactiveDyadicOffDiagonal T (hughesYoungSmallContour T)
        H h k R K

theorem hughesYoungInactiveFiniteSmoothedMoment_eq_sum_dyadicMoments
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ) (R K : ℕ) :
    hughesYoungInactiveFiniteSmoothedMoment T H R K =
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          hughesYoungInactiveDyadicMoment T (hughesYoungSmallContour T)
            H h k R K := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  have hpair : ∀ h ∈ S, ∀ k ∈ S,
      Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
        (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
          hughesYoungInactiveIntegratedSmall T
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)) := by
    intro h hh k hk
    exact integrable_weight_mul_mollifierPair_inactiveIntegratedSmall hT H
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)
  unfold hughesYoungInactiveFiniteSmoothedMoment
    hughesYoungInactiveFiniteTwistedIntegrand
  simp_rw [Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum S (fun h hh =>
    integrable_finsetSum S (fun k hk => hpair h hh k hk))]
  apply Finset.sum_congr rfl
  intro h hh
  rw [MeasureTheory.integral_finsetSum S (fun k hk => hpair h hh k hk)]
  apply Finset.sum_congr rfl
  intro k hk
  exact integral_mollifierPair_mul_inactiveIntegratedSmall_eq_inactiveDyadicMoment
    hT H
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)

theorem hughesYoungInactiveFiniteSmoothedMoment_eq_diagonal_add_offDiagonal
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ) (R K : ℕ) :
    hughesYoungInactiveFiniteSmoothedMoment T H R K =
      hughesYoungInactiveFiniteDiagonal T H R K +
        hughesYoungInactiveFiniteOffDiagonal T H R K := by
  rw [hughesYoungInactiveFiniteSmoothedMoment_eq_sum_dyadicMoments hT]
  unfold hughesYoungInactiveFiniteDiagonal hughesYoungInactiveFiniteOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact hughesYoungInactiveDyadicMoment_eq_diagonal_add_offDiagonal
    T (hughesYoungSmallContour T) H
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
      (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1) R K

/-- Quantitative removal of the small-contour ordinate cutoff for the exact
inactive family. -/
theorem exists_norm_hughesYoungInactiveWholeSmall_sub_integrated_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T t H : ℝ} {a b R K : ℕ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 ≤ H →
      ‖hughesYoungInactiveWholeSmall T a b R K t -
          hughesYoungInactiveIntegratedSmall T a b R K t H‖ ≤
        ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
          ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (Real.log T * Real.exp (4 * C) * D *
                  (max (hughesYoungFullDyadicBound ij.1)
                    (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
                (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
  obtain ⟨C, D, hC, hD, hweight⟩ :=
    exists_norm_hughesYoungRightContourWeight_small_le_gaussian
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t H a b R K hT ht hH
  classical
  unfold hughesYoungInactiveWholeSmall hughesYoungInactiveIntegratedSmall
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
        ((∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
                (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
                ∫ u : ℝ, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)) -
          (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
                (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
                ∫ u in -H..H, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)))‖ ≤
      ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
        ‖(∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
                (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
                ∫ u : ℝ, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)) -
          (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
            ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
              (hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
                (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
                ∫ u in -H..H, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n))‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            ‖(hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ) *
              (hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ) *
              ((∫ u : ℝ, hughesYoungRightPairTerm t
                    (hughesYoungSmallContour T) u (m, n)) -
                ∫ u in -H..H, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n))‖ := by
      apply Finset.sum_le_sum
      intro ij _hij
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _hm => ?_)
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _hn => ?_)
      rw [mul_sub]
    _ ≤ ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
        ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            (Real.log T * Real.exp (4 * C) * D *
                (max (hughesYoungFullDyadicBound ij.1)
                  (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
              (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
      apply Finset.sum_le_sum
      intro ij _hij
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      let M := max (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2)
      have hM : 0 < M := (hughesYoungFullDyadicBound_pos ij.1).trans_le
        (Nat.le_max_left _ _)
      have hm0 : 0 < m := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hm).1
      have hn0 : 0 < n := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hn).1
      have hpair := norm_hughesYoungWholePairTerm_sub_interval_le
        (M := M) (p := (m, n)) hD hweight hT ht hH hM hm0 hn0
        ((Finset.mem_Icc.mp hm).2.trans (Nat.le_max_left _ _))
        ((Finset.mem_Icc.mp hn).2.trans (Nat.le_max_right _ _))
      have hcutI : ‖(hughesYoungFullDyadicCutoff ij.1
          ((a * m : ℕ) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_hughesYoungDyadicCutoffAt_le_one
          (hughesYoungFullDyadicScale_pos ij.1) (by positivity)
      have hcutJ : ‖(hughesYoungFullDyadicCutoff ij.2
          ((b * n : ℕ) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact abs_hughesYoungDyadicCutoffAt_le_one
          (hughesYoungFullDyadicScale_pos ij.2) (by positivity)
      rw [norm_mul, norm_mul]
      calc
        ‖(hughesYoungFullDyadicCutoff ij.1 ((a * m : ℕ) : ℝ) : ℂ)‖ *
            ‖(hughesYoungFullDyadicCutoff ij.2 ((b * n : ℕ) : ℝ) : ℂ)‖ *
            ‖(∫ u : ℝ, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)) -
              ∫ u in -H..H, hughesYoungRightPairTerm t
                (hughesYoungSmallContour T) u (m, n)‖ ≤
          1 * 1 * ‖(∫ u : ℝ, hughesYoungRightPairTerm t
                  (hughesYoungSmallContour T) u (m, n)) -
              ∫ u in -H..H, hughesYoungRightPairTerm t
                (hughesYoungSmallContour T) u (m, n)‖ := by gcongr
        _ ≤ (Real.log T * Real.exp (4 * C) * D * (M : ℝ) ^ 2) *
              (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
          simpa only [one_mul] using hpair
        _ = _ := by simp only [M, Nat.cast_max]

/-- The `hughesYoungInactiveVerticalTailPairMajorant` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveVerticalTailPairMajorant
    (C D T H : ℝ) (a b R K : ℕ) : ℝ :=
  ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
    ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
      ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
        (Real.log T * Real.exp (4 * C) * D *
            (max (hughesYoungFullDyadicBound ij.1)
              (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))

/-- The `hughesYoungInactiveVerticalTailMajorant` definition used by the source-facing construction in `HughesYoungComplementContourTransfer`. -/
noncomputable def hughesYoungInactiveVerticalTailMajorant
    (C D T H : ℝ) (R K : ℕ) : ℝ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
        (1 / Real.pi) *
        hughesYoungInactiveVerticalTailPairMajorant C D T H
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K

theorem hughesYoungInactiveVerticalTailPairMajorant_nonneg
    {T H C D : ℝ} (hT : Real.exp 1 ≤ T) (hD : 0 ≤ D)
    (a b R K : ℕ) :
    0 ≤ hughesYoungInactiveVerticalTailPairMajorant C D T H a b R K := by
  have hT1 : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
  unfold hughesYoungInactiveVerticalTailPairMajorant
  apply Finset.sum_nonneg
  intro ij _hij
  apply Finset.sum_nonneg
  intro m _hm
  apply Finset.sum_nonneg
  intro n _hn
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD)
        (sq_nonneg _))
    (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))

theorem hughesYoungInactiveVerticalTailMajorant_nonneg
    {T H C D : ℝ} (hT : Real.exp 1 ≤ T) (hD : 0 ≤ D)
    (R K : ℕ) :
    0 ≤ hughesYoungInactiveVerticalTailMajorant C D T H R K := by
  unfold hughesYoungInactiveVerticalTailMajorant
  apply Finset.sum_nonneg
  intro h _hh
  apply Finset.sum_nonneg
  intro k _hk
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity))
    (hughesYoungInactiveVerticalTailPairMajorant_nonneg hT hD _ _ R K)

/-- Crude but uniform polynomial majorant for one inactive mollifier pair.
The four powers of the terminal arithmetic cutoff are exactly two counting
powers and the quadratic contour-weight power. -/
theorem hughesYoungInactiveVerticalTailPairMajorant_le_terminal
    {T H C D : ℝ} (hT : Real.exp 1 ≤ T) (hD : 0 ≤ D)
    (a b R K : ℕ) :
    hughesYoungInactiveVerticalTailPairMajorant C D T H a b R K ≤
      (((K + 2) ^ 2 : ℕ) : ℝ) *
        (hughesYoungFullDyadicBound (K + 1) : ℝ) ^ 4 *
        ((Real.log T * Real.exp (4 * C) * D) *
          (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) := by
  classical
  let B := hughesYoungFullDyadicBound (K + 1)
  let E : ℝ := (Real.log T * Real.exp (4 * C) * D) *
    (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))
  have hT1 : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD)
      (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
  have hbox : ∀ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
      (∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
        ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
          (Real.log T * Real.exp (4 * C) * D *
              (max (hughesYoungFullDyadicBound ij.1)
                (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) ≤
        (B : ℝ) ^ 4 * E := by
    intro ij hij
    have hrect := (Finset.mem_filter.mp hij).1
    have hi : ij.1 < K + 2 := by
      exact (Finset.mem_product.mp hrect).1 |> Finset.mem_range.mp
    have hj : ij.2 < K + 2 := by
      exact (Finset.mem_product.mp hrect).2 |> Finset.mem_range.mp
    have hiB : hughesYoungFullDyadicBound ij.1 ≤ B := by
      exact hughesYoungFullDyadicBound_le_terminal hi
    have hjB : hughesYoungFullDyadicBound ij.2 ≤ B := by
      exact hughesYoungFullDyadicBound_le_terminal hj
    have hmaxB : max (hughesYoungFullDyadicBound ij.1)
        (hughesYoungFullDyadicBound ij.2) ≤ B := max_le hiB hjB
    have hterm :
        (Real.log T * Real.exp (4 * C) * D *
              (max (hughesYoungFullDyadicBound ij.1)
                (hughesYoungFullDyadicBound ij.2) : ℝ) ^ 2) *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) ≤
          (B : ℝ) ^ 2 * E := by
      dsimp only [E]
      have hmaxCast : (max (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2) : ℝ) ≤ B := by
        exact_mod_cast hmaxB
      have hfront : 0 ≤ Real.log T * Real.exp (4 * C) * D :=
        mul_nonneg (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD
      have hgauss : 0 ≤ Real.exp (-40 * H ^ 2) *
          Real.sqrt (Real.pi / 40) :=
        mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
      calc
        _ ≤ (Real.log T * Real.exp (4 * C) * D * (B : ℝ) ^ 2) *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)) := by
          gcongr
        _ = (B : ℝ) ^ 2 *
            ((Real.log T * Real.exp (4 * C) * D) *
              (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))) := by ring
    have hcardI : ((Finset.Icc 1
        (hughesYoungFullDyadicBound ij.1)).card : ℝ) ≤ B := by
      exact_mod_cast ((by simp : (Finset.Icc 1
        (hughesYoungFullDyadicBound ij.1)).card ≤
          hughesYoungFullDyadicBound ij.1).trans hiB)
    have hcardJ : ((Finset.Icc 1
        (hughesYoungFullDyadicBound ij.2)).card : ℝ) ≤ B := by
      exact_mod_cast ((by simp : (Finset.Icc 1
        (hughesYoungFullDyadicBound ij.2)).card ≤
          hughesYoungFullDyadicBound ij.2).trans hjB)
    calc
      _ ≤ ∑ _m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ _n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            (B : ℝ) ^ 2 * E := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        exact hterm
      _ = ((Finset.Icc 1 (hughesYoungFullDyadicBound ij.1)).card : ℝ) *
          ((Finset.Icc 1 (hughesYoungFullDyadicBound ij.2)).card : ℝ) *
            ((B : ℝ) ^ 2 * E) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (B : ℝ) * (B : ℝ) * ((B : ℝ) ^ 2 * E) := by
        gcongr
      _ = (B : ℝ) ^ 4 * E := by ring
  have hcard : ((hughesYoungInactiveDyadicBoxes a b R K).card : ℝ) ≤
      (((K + 2) ^ 2 : ℕ) : ℝ) := by
    have hnat : (hughesYoungInactiveDyadicBoxes a b R K).card ≤
        (K + 2) ^ 2 := by
      calc
        _ ≤ (hughesYoungCompleteDyadicRectangle K).card :=
          Finset.card_filter_le _ _
        _ = (K + 2) ^ 2 := by
          simp [hughesYoungCompleteDyadicRectangle, pow_two]
    exact_mod_cast hnat
  unfold hughesYoungInactiveVerticalTailPairMajorant
  calc
    _ ≤ ∑ ij ∈ hughesYoungInactiveDyadicBoxes a b R K,
        (B : ℝ) ^ 4 * E := Finset.sum_le_sum hbox
    _ = ((hughesYoungInactiveDyadicBoxes a b R K).card : ℝ) *
        ((B : ℝ) ^ 4 * E) := by simp
    _ ≤ (((K + 2) ^ 2 : ℕ) : ℝ) * ((B : ℝ) ^ 4 * E) := by
      gcongr
    _ = _ := by dsimp only [B, E]; ring

/-- The global inactive vertical tail loses only the squared mollifier
coefficient mass in addition to the finite dyadic polynomial. -/
theorem hughesYoungInactiveVerticalTailMajorant_le_terminal
    {T H C D : ℝ} (hT : Real.exp 1 ≤ T) (hD : 0 ≤ D)
    (R K : ℕ) :
    hughesYoungInactiveVerticalTailMajorant C D T H R K ≤
      hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) *
        ((((K + 2) ^ 2 : ℕ) : ℝ) *
          (hughesYoungFullDyadicBound (K + 1) : ℝ) ^ 4 *
          ((Real.log T * Real.exp (4 * C) * D) *
            (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40)))) := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  let E : ℝ := ((((K + 2) ^ 2 : ℕ) : ℝ) *
    (hughesYoungFullDyadicBound (K + 1) : ℝ) ^ 4 *
    ((Real.log T * Real.exp (4 * C) * D) *
      (Real.exp (-40 * H ^ 2) * Real.sqrt (Real.pi / 40))))
  have hE0 : 0 ≤ E := by
    have hT1 : (1 : ℝ) ≤ T := by linarith [Real.exp_one_gt_d9]
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (mul_nonneg
        (mul_nonneg (mul_nonneg (Real.log_nonneg hT1) (Real.exp_pos _).le) hD)
        (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)))
  unfold hughesYoungInactiveVerticalTailMajorant
  calc
    _ ≤ ∑ h ∈ S, ∑ k ∈ S,
        ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          (1 / Real.pi) * E := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (hughesYoungInactiveVerticalTailPairMajorant_le_terminal hT hD
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K)
        (mul_nonneg
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity))
    _ = (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ^ 2 *
        (1 / Real.pi) * E := by
      let a : ℕ → ℝ := fun n => ‖shortMobiusSquareCoeff T n‖
      have hprod :
          (∑ h ∈ S, a h) * (∑ k ∈ S, a k) =
            ∑ h ∈ S, ∑ k ∈ S, a h * a k := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro h _hh
        rw [Finset.mul_sum]
      calc
        (∑ h ∈ S, ∑ k ∈ S,
            ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
              (1 / Real.pi) * E) =
            (∑ h ∈ S, ∑ k ∈ S, a h * a k) * (1 / Real.pi) * E := by
          dsimp only [a]
          rw [Finset.sum_mul, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro h _hh
          rw [Finset.sum_mul, Finset.sum_mul]
        _ = ((∑ h ∈ S, a h) * (∑ k ∈ S, a k)) *
              (1 / Real.pi) * E := by rw [hprod]
        _ = (∑ h ∈ S, ‖shortMobiusSquareCoeff T h‖) ^ 2 *
              (1 / Real.pi) * E := by rw [pow_two]
    _ = _ := by
      unfold hughesYoungMollifierCoefficientMass
      rfl

theorem exists_norm_hughesYoungInactiveWholeTwistedIntegrand_sub_finite_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {T t H : ℝ} {R K : ℕ},
      Real.exp 1 ≤ T → t ∈ Set.Icc (T / 4) (4 * T) → 0 ≤ H →
      ‖hughesYoungInactiveWholeTwistedIntegrand T R K t -
          hughesYoungInactiveFiniteTwistedIntegrand T H R K t‖ ≤
        hughesYoungInactiveVerticalTailMajorant C D T H R K := by
  obtain ⟨C, D, hC, hD, hpair⟩ :=
    exists_norm_hughesYoungInactiveWholeSmall_sub_integrated_le
  refine ⟨C, D, hC, hD, ?_⟩
  intro T t H R K hT ht hH
  classical
  unfold hughesYoungInactiveWholeTwistedIntegrand
    hughesYoungInactiveFiniteTwistedIntegrand
    hughesYoungInactiveVerticalTailMajorant
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ((∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungInactiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t) -
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungInactiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)‖ ≤
      ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ‖∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungInactiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t -
          ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
            hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungInactiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H‖ :=
      norm_sum_le _ _
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ‖hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
            (hughesYoungInactiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t -
              hughesYoungInactiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H)‖ := by
      apply Finset.sum_le_sum
      intro h _hh
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _hk => ?_)
      rw [mul_sub]
    _ ≤ ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
            (1 / Real.pi) *
            hughesYoungInactiveVerticalTailPairMajorant C D T H
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      have hh0 : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1
      have hk0 : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
      have hmoll := norm_hughesYoungMollifierPairTerm_le T t hh0 hk0
      have htail := hpair hT ht hH (a := hughesYoungReducedLeft h k)
        (b := hughesYoungReducedRight h k) (R := R) (K := K)
      have htail' :
          ‖hughesYoungInactiveWholeSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t -
              hughesYoungInactiveIntegratedSmall T
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t H‖ ≤
            hughesYoungInactiveVerticalTailPairMajorant C D T H
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K := by
        simpa only [hughesYoungInactiveVerticalTailPairMajorant] using htail
      have hpi : ‖(1 / (Real.pi : ℂ))‖ = 1 / Real.pi := by
        simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      rw [norm_mul, norm_mul, hpi]
      gcongr

theorem aestronglyMeasurable_hughesYoungInactiveWholeHigh
    {q : ℕ} (hq : 0 < q) (a b R K : ℕ) :
    AEStronglyMeasurable (fun t : ℝ =>
      hughesYoungInactiveWholeHigh q a b R K t) := by
  let F : ℝ × ℝ → ℂ := fun z =>
    hughesYoungInactiveHighPairSum q a b R K z.1 z.2
  have hF : AEMeasurable F := by
    unfold F hughesYoungInactiveHighPairSum
    apply AEMeasurable.tsum
    intro p
    by_cases hp1 : p.1 = 0
    · have hz : (fun z : ℝ × ℝ =>
          (hughesYoungInactiveDyadicWeight a b R K p.1 p.2 : ℂ) *
            hughesYoungRightPairTerm z.1 (2 * q) z.2 p) = 0 := by
        funext z
        rw [hughesYoungRightPairTerm_eq_zero_of_fst_eq_zero
          z.1 (2 * q) z.2 hp1]
        simp
      rw [hz]
      exact aemeasurable_const
    by_cases hp2 : p.2 = 0
    · have hz : (fun z : ℝ × ℝ =>
          (hughesYoungInactiveDyadicWeight a b R K p.1 p.2 : ℂ) *
            hughesYoungRightPairTerm z.1 (2 * q) z.2 p) = 0 := by
        funext z
        rw [hughesYoungRightPairTerm_eq_zero_of_snd_eq_zero
          z.1 (2 * q) z.2 hp2]
        simp
      rw [hz]
      exact aemeasurable_const
    exact (continuous_const.mul
      (continuous_uncurry_hughesYoungRightPairTerm_height_ordinate
        (by exact_mod_cast Nat.mul_pos (by omega : 0 < 2) hq)
        (Nat.pos_of_ne_zero hp1) (Nat.pos_of_ne_zero hp2))).aemeasurable
  unfold hughesYoungInactiveWholeHigh
  exact hF.aestronglyMeasurable.integral_prod_right'

theorem aestronglyMeasurable_weight_mul_hughesYoungInactiveWholeTwistedIntegrand
    {q R K : ℕ} (hq : 0 < q) (hR : 0 < R)
    {η : ℝ} (hη0 : 0 < η) (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T : ℝ} (hT : Real.exp 1 ≤ T)
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (K + 1)) :
    AEStronglyMeasurable (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungInactiveWholeTwistedIntegrand T R K t) := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  have hhigh : AEStronglyMeasurable
      (∑ h ∈ S, ∑ k ∈ S, fun t : ℝ =>
        (hughesYoungHeightWeight T t : ℂ) *
          (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
            hughesYoungInactiveWholeHigh q
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t)) := by
    apply Finset.aestronglyMeasurable_sum
    intro h hhmem
    apply Finset.aestronglyMeasurable_sum
    intro k hkmem
    have hh : 0 < h := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1
    exact (Complex.continuous_ofReal.comp
        (contDiff_hughesYoungHeightWeight T).continuous).aestronglyMeasurable.mul
      (((continuous_hughesYoungMollifierPairTerm T hh hk).aestronglyMeasurable.mul
        aestronglyMeasurable_const).mul
        (aestronglyMeasurable_hughesYoungInactiveWholeHigh hq
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K))
  have hhigh' : AEStronglyMeasurable (fun t : ℝ =>
      ∑ h ∈ S, ∑ k ∈ S,
        (hughesYoungHeightWeight T t : ℂ) *
          (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
            hughesYoungInactiveWholeHigh q
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t)) := by
    have heq : (fun t : ℝ =>
        ∑ h ∈ S, ∑ k ∈ S,
          (hughesYoungHeightWeight T t : ℂ) *
            (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungInactiveWholeHigh q
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t)) =
        (∑ h ∈ S, ∑ k ∈ S, fun t : ℝ =>
          (hughesYoungHeightWeight T t : ℂ) *
            (hughesYoungMollifierPairTerm T t h k * (1 / (Real.pi : ℂ)) *
              hughesYoungInactiveWholeHigh q
                (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K t)) := by
      funext t
      simp only [Finset.sum_apply]
    rw [heq]
    exact hhigh
  apply hhigh'.congr
  filter_upwards with t
  unfold hughesYoungInactiveWholeTwistedIntegrand
  simp_rw [Finset.mul_sum]
  by_cases hw : hughesYoungHeightWeight T t = 0
  · simp [hw]
  · have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
    have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
      hughesYoungHeightWeight_support hT0 hw
    apply Finset.sum_congr rfl
    intro h hhmem
    apply Finset.sum_congr rfl
    intro k hkmem
    rw [hughesYoungInactiveWholeSmall_eq_wholeHigh hq
      (hughesYoungReducedLeft_pos
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1))
      (hughesYoungReducedRight_pos
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hhmem).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hkmem).1))
      hR (hcover h hhmem k hkmem) η hη0 hη hT ht]

theorem integrable_weight_mul_hughesYoungInactiveFiniteTwistedIntegrand
    {T : ℝ} (hT : Real.exp 1 ≤ T) (H : ℝ) (R K : ℕ) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungInactiveFiniteTwistedIntegrand T H R K t) := by
  classical
  let S := Finset.Icc 1 ((detectorCutoff T) ^ 2)
  unfold hughesYoungInactiveFiniteTwistedIntegrand
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum S (fun h hh =>
    integrable_finsetSum S (fun k hk =>
      integrable_weight_mul_mollifierPair_inactiveIntegratedSmall hT H
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)
        (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)))

theorem integrable_weight_mul_hughesYoungInactiveWholeTwistedIntegrand
    {q R K : ℕ} (hq : 0 < q) (hR : 0 < R)
    {η : ℝ} (hη0 : 0 < η) (hη : η < 2 * (q : ℝ) - 1 / 2)
    {T : ℝ} (hT : Real.exp 1 ≤ T)
    (hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (K + 1)) :
    Integrable (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ) *
      hughesYoungInactiveWholeTwistedIntegrand T R K t) := by
  obtain ⟨L, hL, hbound⟩ :=
    exists_norm_hughesYoungInactiveWholeTwistedIntegrand_le q hq η hη0 hη
  let A : ℝ := hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) *
    ((256 * Real.exp (400 * (q : ℝ) ^ 2) *
      ((7 + 2 * (q : ℝ)) * T) ^ (4 * q + 8) *
      (R : ℝ) ^ (-(2 * (q : ℝ) - 1 / 2 - η)) *
      hughesYoungReferenceDivisorPairMass η) * L)
  let g : ℝ → ℝ := fun t => hughesYoungHeightWeight T t * A
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hA0 : 0 ≤ A := by
    unfold A
    exact mul_nonneg
      (mul_nonneg (pow_nonneg (hughesYoungMollifierCoefficientMass_nonneg T) 2)
        (by positivity))
      (mul_nonneg
        (mul_nonneg (by positivity)
          (hughesYoungReferenceDivisorPairMass_nonneg η)) hL.le)
  have hcompact : HasCompactSupport (hughesYoungHeightWeight T) := by
    have hc : HasCompactSupport (hughesYoungCutoff : ℝ → ℝ) :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc
        hughesYoungCutoff.support
    simpa only [hughesYoungHeightWeight] using
      hc.comp_smul (inv_ne_zero hT0.ne')
  have hg : Integrable g :=
    ((contDiff_hughesYoungHeightWeight T).continuous.mul
      (continuous_const : Continuous (fun _t : ℝ => A))).integrable_of_hasCompactSupport
        hcompact.mul_right
  have hmeas : AEStronglyMeasurable (fun t : ℝ =>
      (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungInactiveWholeTwistedIntegrand T R K t) :=
    aestronglyMeasurable_weight_mul_hughesYoungInactiveWholeTwistedIntegrand
      hq hR hη0 hη hT hcover
  apply hg.mono' hmeas
  filter_upwards with t
  by_cases hw : hughesYoungHeightWeight T t = 0
  · simp [hw, g]
  · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
      hughesYoungHeightWeight_support hT0 hw
    have hs := hbound hT hR hcover t ht
    have hw0 := hughesYoungHeightWeight_nonneg T t
    unfold g
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_left hs hw0

/-- Quantitative global comparison between the cancellation-preserving
inactive source on the whole small contour and its finite-height arithmetic
realization. -/
theorem exists_norm_hughesYoungInactiveWholeSmoothedMoment_sub_finite_le :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ {q R K : ℕ}, 0 < q → 0 < R →
      ∀ {η : ℝ}, 0 < η → η < 2 * (q : ℝ) - 1 / 2 →
      ∀ {T H : ℝ}, Real.exp 1 ≤ T → 0 ≤ H →
      (∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
          (((hughesYoungReducedLeft h k) *
            (hughesYoungReducedRight h k) * R : ℕ) : ℝ) ≤
              hughesYoungDyadicRatio ^ (K + 1)) →
      ‖hughesYoungInactiveWholeSmoothedMoment T R K -
          hughesYoungInactiveFiniteSmoothedMoment T H R K‖ ≤
        (15 * T / 4) * hughesYoungInactiveVerticalTailMajorant C D T H R K := by
  obtain ⟨C, D, hC, hD, hpoint⟩ :=
    exists_norm_hughesYoungInactiveWholeTwistedIntegrand_sub_finite_le
  refine ⟨C, D, hC, hD, ?_⟩
  intro q R K hq hR η hη0 hη T H hT hH hcover
  have hwhole :=
    integrable_weight_mul_hughesYoungInactiveWholeTwistedIntegrand
      hq hR hη0 hη hT hcover
  have hfinite :=
    integrable_weight_mul_hughesYoungInactiveFiniteTwistedIntegrand hT H R K
  let A := hughesYoungInactiveVerticalTailMajorant C D T H R K
  let B : ℝ → ℝ := Set.Icc (T / 4) (4 * T) |>.indicator (fun _ => A)
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hA0 : 0 ≤ A :=
    hughesYoungInactiveVerticalTailMajorant_nonneg hT hD.le R K
  have hBint : Integrable B := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const isCompact_Icc.measure_ne_top
  unfold hughesYoungInactiveWholeSmoothedMoment
    hughesYoungInactiveFiniteSmoothedMoment
  rw [← integral_sub hwhole hfinite]
  apply (norm_integral_le_of_norm_le hBint ?_).trans_eq
  · rw [show (∫ t : ℝ, B t) = ∫ _t in Set.Icc (T / 4) (4 * T), A by
        exact MeasureTheory.integral_indicator measurableSet_Icc]
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by nlinarith : 0 ≤ 4 * T - T / 4)]
    unfold A
    ring
  · filter_upwards with t
    by_cases hw : hughesYoungHeightWeight T t = 0
    · have hleft :
          ‖(hughesYoungHeightWeight T t : ℂ) *
                hughesYoungInactiveWholeTwistedIntegrand T R K t -
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungInactiveFiniteTwistedIntegrand T H R K t‖ = 0 := by
          simp [hw]
      rw [hleft]
      simpa only [B] using
        (Set.indicator_nonneg (s := Set.Icc (T / 4) (4 * T))
          (fun _ _ => hA0) t)
    · have ht : t ∈ Set.Icc (T / 4) (4 * T) :=
        hughesYoungHeightWeight_support hT0 hw
      have hdiff := hpoint hT ht hH (R := R) (K := K)
      have hw0 := hughesYoungHeightWeight_nonneg T t
      have hw1 := hughesYoungHeightWeight_le_one T t
      rw [show
          (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungInactiveWholeTwistedIntegrand T R K t -
              (hughesYoungHeightWeight T t : ℂ) *
                hughesYoungInactiveFiniteTwistedIntegrand T H R K t =
            (hughesYoungHeightWeight T t : ℂ) *
              (hughesYoungInactiveWholeTwistedIntegrand T R K t -
                hughesYoungInactiveFiniteTwistedIntegrand T H R K t) by ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
      change _ ≤ Set.indicator (Set.Icc (T / 4) (4 * T)) (fun _ => A) t
      rw [Set.indicator_of_mem ht]
      exact (mul_le_mul_of_nonneg_left hdiff hw0).trans
        (by simpa only [A, one_mul] using
          mul_le_mul_of_nonneg_right hw1 hA0)

set_option maxRecDepth 100000 in
/-- At the native conductor radius the complete inactive opening-line
family is already power-saving.  This is the cancellation-preserving
estimate needed before projecting to the DFI off-diagonal source. -/
theorem exists_norm_hughesYoungConductorInactiveWholeMoment_le_height :
    ∃ C : ℝ, 0 < C ∧ ∀ {T : ℝ}, Real.exp 1 ≤ T →
      ‖hughesYoungInactiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤ C * T := by
  obtain ⟨L, hL, hrem⟩ :=
    exists_norm_hughesYoungInactiveWholeSmoothedMoment_le
      1000 (by norm_num) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  let C : ℝ :=
    (15 / 4) * 81 ^ 2 * (1 / Real.pi) *
      (256 * Real.exp (400 * (1000 : ℝ) ^ 2) *
        2007 ^ (4008 : ℕ) *
        (hughesYoungReferenceDivisorPairMass (1 / 2) + 1) * L)
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos
      (mul_pos (mul_pos (by norm_num) (by norm_num)) (by positivity))
      (mul_pos
        (mul_pos (mul_pos (by positivity) (by positivity))
          (by linarith [hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)])) hL)
  refine ⟨C, hC, ?_⟩
  intro T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT2 : 2 ≤ T := by linarith [Real.exp_one_gt_two]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR := hughesYoungConductorRadius_pos hT1
  have hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * hughesYoungConductorRadius T : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
    intro h hh k hk
    exact hughesYoungConductor_cover hT2 hh hk
  have hraw := hrem hT hR hcover
  have hraw' :
      ‖hughesYoungInactiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (1000 : ℝ) ^ 2) *
            ((2007 : ℝ) * T) ^ (4008 : ℕ) *
            (hughesYoungConductorRadius T : ℝ) ^ (-1999 : ℝ) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) := by
    convert hraw using 1
    all_goals norm_num
  have hmass := hughesYoungMollifierCoefficientMass_le_height_fourth hT1
  have hmass0 := hughesYoungMollifierCoefficientMass_nonneg T
  have hpair0 := hughesYoungReferenceDivisorPairMass_nonneg (1 / 2)
  have hpair : hughesYoungReferenceDivisorPairMass (1 / 2) ≤
      hughesYoungReferenceDivisorPairMass (1 / 2) + 1 := by linarith
  have hrneg : (hughesYoungConductorRadius T : ℝ) ^ (-1999 : ℝ) ≤
      T ^ (-401799 / 100 : ℝ) := by
    have hlower : T ^ (201 / 100 : ℝ) ≤
        (hughesYoungConductorRadius T : ℝ) :=
      hughesYoungConductorRadius_lower T
    have hneg := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hT0 (201 / 100 : ℝ)) hlower
        (by norm_num : (-1999 : ℝ) ≤ 0)
    calc
      _ ≤ (T ^ (201 / 100 : ℝ)) ^ (-1999 : ℝ) := hneg
      _ = T ^ (-401799 / 100 : ℝ) := by
        rw [← Real.rpow_mul hT0.le]
        norm_num
  have hbound :
      (15 * T / 4) * hughesYoungMollifierCoefficientMass T ^ 2 *
          (1 / Real.pi) *
          ((256 * Real.exp (400 * (1000 : ℝ) ^ 2) *
            ((2007 : ℝ) * T) ^ (4008 : ℕ) *
            (hughesYoungConductorRadius T : ℝ) ^ (-1999 : ℝ) *
            hughesYoungReferenceDivisorPairMass (1 / 2)) * L) ≤
        C * T ^ (-99 / 100 : ℝ) := by
    calc
      _ ≤
          (15 * T / 4) * (81 * T ^ (4 : ℝ)) ^ 2 *
            (1 / Real.pi) *
            ((256 * Real.exp (400 * (1000 : ℝ) ^ 2) *
              ((2007 : ℝ) * T) ^ (4008 : ℕ) *
              T ^ (-401799 / 100 : ℝ) *
              (hughesYoungReferenceDivisorPairMass (1 / 2) + 1)) * L) := by
        gcongr
    _ = C * T ^ (-99 / 100 : ℝ) := by
      have hfour : (T ^ (4 : ℝ)) ^ 2 = T ^ (8 : ℝ) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hT0.le]
        norm_num
      have hpowers :
          T * T ^ (8 : ℝ) * T ^ (4008 : ℕ) *
              T ^ (-401799 / 100 : ℝ) =
            T ^ (-99 / 100 : ℝ) := by
        calc
          _ = T ^ (1 : ℝ) * T ^ (8 : ℝ) * T ^ (4008 : ℝ) *
                T ^ (-401799 / 100 : ℝ) := by
            rw [Real.rpow_one]
            exact congrArg
              (fun x : ℝ => T * T ^ (8 : ℝ) * x *
                T ^ (-401799 / 100 : ℝ))
              (Real.rpow_natCast T 4008).symm
          _ = T ^ ((1 : ℝ) + 8) * T ^ (4008 : ℝ) *
                T ^ (-401799 / 100 : ℝ) := by
            rw [← Real.rpow_add hT0]
          _ = T ^ ((1 : ℝ) + 8 + 4008) *
                T ^ (-401799 / 100 : ℝ) := by
            rw [← Real.rpow_add hT0]
          _ = T ^ ((1 : ℝ) + 8 + 4008 - 401799 / 100) := by
            rw [← Real.rpow_add hT0]
            congr 1
            ring
          _ = T ^ (-99 / 100 : ℝ) := by norm_num
      rw [mul_pow, hfour]
      calc
        _ = C * (T * T ^ (8 : ℝ) * T ^ (4008 : ℕ) *
            T ^ (-401799 / 100 : ℝ)) := by
          dsimp only [C]
          set_option exponentiation.threshold 5000 in ring
        _ = C * T ^ (-99 / 100 : ℝ) := by rw [hpowers]
  have hlast : C * T ^ (-99 / 100 : ℝ) ≤ C * T := by
    have hp : T ^ (-99 / 100 : ℝ) ≤ T := by
      calc
        T ^ (-99 / 100 : ℝ) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
        _ = T := by simp
    exact mul_le_mul_of_nonneg_left hp hC.le
  exact hraw'.trans (hbound.trans hlast)

/-- Native epsilon-power form of the cancellation-preserving inactive
opening-line estimate. -/
theorem hughesYoungConductorInactiveWholeMoment_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungInactiveWholeSmoothedMoment T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungConductorInactiveWholeMoment_le_height
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (1 : ℝ)] with T hT hT1
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hpow : 1 ≤ T ^ ε := Real.one_le_rpow hT1 hε.le
  rw [Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungInactiveWholeSmoothedMoment T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)))]
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hT0.le ε) (abs_nonneg T)),
    abs_of_pos hT0]
  calc
    |‖hughesYoungInactiveWholeSmoothedMoment T
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖| =
        ‖hughesYoungInactiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ :=
      abs_of_nonneg (norm_nonneg _)
    _ ≤ C * T := hbound hT
    _ ≤ C * (T ^ ε * T) := by
      gcongr
      calc
        T = 1 * T := by ring
        _ ≤ T ^ ε * T := mul_le_mul_of_nonneg_right hpow hT0.le

/-- At the native height `H = T / 8`, replacing the whole small contour by
the finite contour costs less than every positive power of the fourth-moment
scale.  The proof keeps the inactive family summed before taking norms. -/
theorem hughesYoungConductorInactiveVerticalTail_epsilonPowerBound :
    EpsilonPowerBound
      (fun T =>
        ‖hughesYoungInactiveWholeSmoothedMoment T
              (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
            hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
              (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  obtain ⟨C, D, hC, hD, htail⟩ :=
    exists_norm_hughesYoungInactiveWholeSmoothedMoment_sub_finite_le
  let A : ℝ :=
    (15 / 4) * 81 ^ 2 * (1 / Real.pi) * 103 ^ 2 * 7 ^ 4 *
      Real.exp (4 * C) * D * Real.sqrt (Real.pi / 40)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hbaseRpow : Tendsto (fun T : ℝ =>
      T ^ (412 : ℝ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2))
      atTop (nhds 0) :=
    (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg
      (by norm_num : (0 : ℝ) < 5 / 8) 412).tendsto_zero_of_tendsto
        (Real.tendsto_exp_atBot.comp
          (tendsto_id.const_mul_atTop_of_neg
            (by norm_num : (-(1 / 2 : ℝ)) < 0)))
  have hbase : Tendsto (fun T : ℝ =>
      T ^ (412 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2))
      atTop (nhds 0) := by
    simpa only [← Real.rpow_natCast] using hbaseRpow
  have hlimit : Tendsto (fun T : ℝ =>
      A * (T ^ (412 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hbase.const_mul A
  have hsmall : ∀ᶠ T : ℝ in atTop,
      A * (T ^ (412 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)) ≤ 1 :=
    (hlimit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      fun _ h => h.le
  apply IsBigO.of_bound 1
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 1)] with T hsmallT hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT2 : 2 ≤ T := by linarith [Real.exp_one_gt_two]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hR : 0 < hughesYoungConductorRadius T :=
    hughesYoungConductorRadius_pos hT1
  have hcover : ∀ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∀ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
        (((hughesYoungReducedLeft h k) *
          (hughesYoungReducedRight h k) * hughesYoungConductorRadius T : ℕ) : ℝ) ≤
            hughesYoungDyadicRatio ^ (hughesYoungGlobalDepth T + 1) := by
    intro h hh k hk
    exact hughesYoungConductor_cover hT2 hh hk
  have hraw := htail (q := 1000) (by norm_num) hR
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 2 * (1000 : ℝ) - 1 / 2)
    hT (by positivity : (0 : ℝ) ≤ T / 8) hcover
  have hterminal := hughesYoungInactiveVerticalTailMajorant_le_terminal
    (C := C) (H := T / 8) hT hD.le
      (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
  have hmass := hughesYoungMollifierCoefficientMass_le_height_fourth hT1
  have hmass0 := hughesYoungMollifierCoefficientMass_nonneg T
  have hmass' : hughesYoungMollifierCoefficientMass T ≤
      81 * T ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast]
    exact hmass
  have hdepth := hughesYoungGlobalDepth_add_two_le_rpow
    (by norm_num : (0 : ℝ) < 1) hT
  norm_num [Real.rpow_one] at hdepth
  have hfull := hughesYoungTerminalFullDyadicBound_le_seven_mul_pow_hundred hT
  have hlog : Real.log T ≤ T := Real.log_le_self hT0.le
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hmajorant :
      (15 * T / 4) * hughesYoungInactiveVerticalTailMajorant C D T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) ≤
        A * (T ^ (412 : ℕ) * Real.exp (-(5 / 8 : ℝ) * T ^ 2)) := by
    calc
      _ ≤ (15 * T / 4) *
          (hughesYoungMollifierCoefficientMass T ^ 2 * (1 / Real.pi) *
            ((((hughesYoungGlobalDepth T + 2) ^ 2 : ℕ) : ℝ) *
              (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) ^ 4 *
              ((Real.log T * Real.exp (4 * C) * D) *
                (Real.exp (-40 * (T / 8) ^ 2) *
                  Real.sqrt (Real.pi / 40))))) := by
            gcongr
      _ ≤ (15 * T / 4) *
          ((81 * T ^ (4 : ℕ)) ^ 2 * (1 / Real.pi) *
            ((103 * T) ^ 2 * (7 * T ^ (100 : ℕ)) ^ 4 *
              ((T * Real.exp (4 * C) * D) *
                (Real.exp (-40 * (T / 8) ^ 2) *
                  Real.sqrt (Real.pi / 40))))) := by
            push_cast
            gcongr
      _ = A * (T ^ (412 : ℕ) *
          Real.exp (-(5 / 8 : ℝ) * T ^ 2)) := by
            dsimp only [A]
            ring_nf
  have hbound := hraw.trans (hmajorant.trans hsmallT)
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 _ _).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg
      (hughesYoungInactiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
        hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T))), htarget]
  have hone : 1 ≤ 1 * T ^ (1 + ε) := by
    simpa using Real.one_le_rpow hT1 (show 0 ≤ 1 + ε by linarith)
  exact hbound.trans hone

/-- The exact finite-height inactive Hughes--Young moment inherits the native
fourth-moment bound from the whole cancellation-preserving contour and the
Gaussian vertical-tail comparison. -/
theorem hughesYoungConductorInactiveFiniteMoment_epsilonPowerBound :
    EpsilonPowerBound
      (fun T =>
        ‖hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  let whole : ℝ → ℝ := fun T =>
    ‖hughesYoungInactiveWholeSmoothedMoment T
      (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖
  let tail : ℝ → ℝ := fun T =>
    ‖hughesYoungInactiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
        hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖
  have hwhole : EpsilonPowerBound whole (fun T => T) := by
    simpa only [whole] using
      hughesYoungConductorInactiveWholeMoment_epsilonPowerBound
  have htail : EpsilonPowerBound tail (fun T => T) := by
    simpa only [tail] using
      hughesYoungConductorInactiveVerticalTail_epsilonPowerBound
  have hsum := hwhole.add htail
  intro ε hε
  have hsumε := hsum ε hε
  have hdom :
      (fun T =>
        |‖hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖|) =O[atTop]
      (fun T => |whole T + tail T|) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with T
    have htri :
        ‖hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
          whole T + tail T := by
      dsimp only [whole, tail]
      have h := norm_sub_le
        (hughesYoungInactiveWholeSmoothedMoment T
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T))
        (hughesYoungInactiveWholeSmoothedMoment T
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
          hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T))
      simpa only [sub_sub_cancel] using h
    have hsum0 : 0 ≤ whole T + tail T := by
      dsimp only [whole, tail]
      positivity
    calc
      ‖|‖hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖|‖ =
          ‖hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by simp
      _ ≤ whole T + tail T := htri
      _ = 1 * ‖|whole T + tail T|‖ := by
        rw [one_mul, Real.norm_eq_abs, abs_abs, abs_of_nonneg hsum0]
  exact hdom.trans hsumε

/-- The inactive diagonal is bounded by the same literal `hm = kn`
arithmetic majorant as the active diagonal, now enlarged only to the terminal
finite dyadic cutoff. -/
theorem exists_norm_hughesYoungInactiveFiniteDiagonal_le :
    ∃ C W : ℝ, 0 < C ∧ 0 < W ∧
      ∀ {T H : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 0 ≤ H →
      ‖hughesYoungInactiveFiniteDiagonal T H R K‖ ≤
        ((K + 2 : ℕ) : ℝ) ^ 2 *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W *
              Real.sqrt (Real.pi / 80))) *
          hughesYoungFiniteDiagonalArithmeticMajorant T
            ((detectorCutoff T) ^ 2)
            (hughesYoungFullDyadicBound (K + 1)) := by
  obtain ⟨C, W, hC, hW, hterm⟩ :=
    exists_norm_integral_hughesYoungFiniteArithmeticTerm_diagonal_le
  refine ⟨C, W, hC, hW, ?_⟩
  intro T H R K hT hH
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := hughesYoungFullDyadicBound (K + 1)
  let F : ℝ := (15 * T / 4) * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hF0 : 0 ≤ F := by
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    dsimp only [F]
    positivity
  have hbox : ∀ h ∈ Finset.Icc 1 ell, ∀ k ∈ Finset.Icc 1 ell,
      ∀ ij ∈ hughesYoungInactiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
      ‖hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
          H h k ij.1 ij.2‖ ≤
        F * (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
    intro h hhmem k hkmem ij hij
    have hh : 0 < h := (Finset.mem_Icc.mp hhmem).1
    have hk : 0 < k := (Finset.mem_Icc.mp hkmem).1
    have hrect := (Finset.mem_filter.mp hij).1
    have hi : ij.1 < K + 2 :=
      Finset.mem_range.mp (Finset.mem_product.mp hrect).1
    have hj : ij.2 < K + 2 :=
      Finset.mem_range.mp (Finset.mem_product.mp hrect).2
    have hBi : hughesYoungFullDyadicBound ij.1 ≤ B := by
      exact hughesYoungFullDyadicBound_le_terminal hi
    have hBj : hughesYoungFullDyadicBound ij.2 ≤ B := by
      exact hughesYoungFullDyadicBound_le_terminal hj
    unfold hughesYoungFullDyadicDiagonalBox
    calc
      ‖∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            if quadraticDivisorShift h k m n = 0 then
              hughesYoungFullDyadicIntegratedTerm T
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)
            else 0‖ ≤
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            ‖if quadraticDivisorShift h k m n = 0 then
              hughesYoungFullDyadicIntegratedTerm T
                (hughesYoungSmallContour T) H h k ij.1 ij.2 (m, n)
            else 0‖ := (norm_sum_le _ _).trans
              (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
      _ ≤ ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            F * (if h * m = k * n then
              ‖shortMobiusSquareCoeff T h‖ *
                ‖shortMobiusSquareCoeff T k‖ *
                (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                (((h * m : ℕ) : ℝ))⁻¹
            else 0) := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro n hn
        have hm0 : 0 < m := (Finset.mem_Icc.mp hm).1
        have hn0 : 0 < n := (Finset.mem_Icc.mp hn).1
        by_cases hd : h * m = k * n
        · have hs : quadraticDivisorShift h k m n = 0 :=
            (quadraticDivisorShift_eq_zero_iff h k m n).2 hd
          rw [if_pos hs, if_pos hd]
          exact (norm_hughesYoungFullDyadicIntegratedTerm_le hh hk).trans
            ((hterm hT hH hh hk hm0 hn0 hd).trans_eq
              (by dsimp only [F]; ring))
        · have hs : quadraticDivisorShift h k m n ≠ 0 := fun hs =>
            hd ((quadraticDivisorShift_eq_zero_iff h k m n).1 hs)
          simp [hd, hs]
      _ = F * (∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            if h * m = k * n then
              ‖shortMobiusSquareCoeff T h‖ *
                ‖shortMobiusSquareCoeff T k‖ *
                (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                (((h * m : ℕ) : ℝ))⁻¹
            else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.mul_sum]
      _ ≤ F * (∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
          if h * m = k * n then
            ‖shortMobiusSquareCoeff T h‖ *
              ‖shortMobiusSquareCoeff T k‖ *
              (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
              (((h * m : ℕ) : ℝ))⁻¹
          else 0) := by
        apply mul_le_mul_of_nonneg_left _ hF0
        calc
          _ ≤ ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
              ∑ n ∈ Finset.Icc 1 B,
                if h * m = k * n then
                  ‖shortMobiusSquareCoeff T h‖ *
                    ‖shortMobiusSquareCoeff T k‖ *
                    (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                    (((h * m : ℕ) : ℝ))⁻¹ else 0 := by
              apply Finset.sum_le_sum
              intro m _hm
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.Icc_subset_Icc_right hBj
              · intro n _hn _hnnot
                positivity
          _ ≤ ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
                if h * m = k * n then
                  ‖shortMobiusSquareCoeff T h‖ *
                    ‖shortMobiusSquareCoeff T k‖ *
                    (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
                    (((h * m : ℕ) : ℝ))⁻¹ else 0 := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.Icc_subset_Icc_right hBi
              · intro m _hm _hmnot
                positivity
  unfold hughesYoungInactiveFiniteDiagonal hughesYoungInactiveDyadicDiagonal
  let A : ℕ → ℕ → ℝ := fun h k =>
    ∑ m ∈ Finset.Icc 1 B, ∑ n ∈ Finset.Icc 1 B,
      if h * m = k * n then
        ‖shortMobiusSquareCoeff T h‖ * ‖shortMobiusSquareCoeff T k‖ *
          (m.divisors.card : ℝ) * (n.divisors.card : ℝ) *
          (((h * m : ℕ) : ℝ))⁻¹ else 0
  have hA0 : ∀ h k, 0 ≤ A h k := by
    intro h k
    dsimp only [A]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  calc
    ‖∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ ij ∈ hughesYoungInactiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
            H h k ij.1 ij.2‖ ≤
      ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ ij ∈ hughesYoungInactiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          ‖hughesYoungFullDyadicDiagonalBox T (hughesYoungSmallContour T)
            H h k ij.1 ij.2‖ := (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun h _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun k _ => norm_sum_le _ _))
    _ ≤ ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        ∑ _ij ∈ hughesYoungInactiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
          F * A h k := by
      apply Finset.sum_le_sum
      intro h hh
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro ij hij
      simpa only [A] using hbox h hh k hk ij hij
    _ ≤ ∑ h ∈ Finset.Icc 1 ell, ∑ k ∈ Finset.Icc 1 ell,
        (((K + 2 : ℕ) : ℝ) ^ 2) * (F * A h k) := by
      apply Finset.sum_le_sum
      intro h _hh
      apply Finset.sum_le_sum
      intro k _hk
      rw [Finset.sum_const, nsmul_eq_mul]
      push_cast
      have hcard : ((hughesYoungInactiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K).card : ℝ) ≤
          (((K + 2) ^ 2 : ℕ) : ℝ) := by
        exact_mod_cast ((Finset.card_filter_le _ _).trans_eq (by
          simp [hughesYoungCompleteDyadicRectangle, pow_two]))
      norm_num at hcard
      exact mul_le_mul_of_nonneg_right hcard
        (mul_nonneg hF0 (hA0 h k))
    _ = (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        hughesYoungFiniteDiagonalArithmeticMajorant T ell B := by
      unfold hughesYoungFiniteDiagonalArithmeticMajorant
      dsimp only [A]
      simp_rw [Finset.mul_sum]
      ring_nf
    _ = _ := by
      simp only [ell, B, F]

/-- The literal inactive diagonal, with no box discarded, is reduced to the
same divisor-fiber estimate used in the active Hughes--Young diagonal. -/
theorem exists_norm_hughesYoungInactiveFiniteDiagonal_le_power
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C W ca cd : ℝ,
      0 < C ∧ 0 < W ∧ 0 < ca ∧ 0 < cd ∧
      ∀ {T H : ℝ} {R K : ℕ}, Real.exp 1 ≤ T → 0 ≤ H →
        ‖hughesYoungInactiveFiniteDiagonal T H R K‖ ≤
          ((K + 2 : ℕ) : ℝ) ^ 2 *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W *
              Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 *
          ((((detectorCutoff T) ^ 2 *
            hughesYoungFullDyadicBound (K + 1) : ℕ) : ℝ)) ^ (6 * δ) *
          (((harmonic ((detectorCutoff T) ^ 2 *
            hughesYoungFullDyadicBound (K + 1)) : ℚ) : ℝ)) := by
  obtain ⟨C, W, hC, hW, hdiag⟩ :=
    exists_norm_hughesYoungInactiveFiniteDiagonal_le
  obtain ⟨ca, hca, hcoeff⟩ := shortMobiusSquareCoeff_bound δ hδ
  obtain ⟨cd, hcd, hdiv⟩ := divisorCountBound_native δ hδ
  refine ⟨C, W, ca, cd, hC, hW, hca, hcd, ?_⟩
  intro T H R K hT hH
  let ell : ℕ := (detectorCutoff T) ^ 2
  let B : ℕ := hughesYoungFullDyadicBound (K + 1)
  let cutoff : ℕ := ell * B
  let F : ℝ := (15 * T / 4) * (1 / Real.pi) *
    (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hT0 : 0 < T := (Real.exp_pos 1).trans_le hT
  have hF0 : 0 ≤ F := by
    have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
    have hlog : 0 ≤ Real.log T := Real.log_nonneg hT1
    dsimp only [F]
    positivity
  have hdiag' := hdiag (T := T) (H := H) (R := R) (K := K) hT hH
  have hmajor := hughesYoungFiniteDiagonalArithmeticMajorant_le T ell B
  have hsmooth := smoothTwistedDiagonalMajorant_le
    (ell := ell) (cutoff := cutoff) hT0.le
    (shortMobiusSquareCoeff T) hδ.le hca.le hcd.le
    (fun h hh => hcoeff T h (Finset.mem_Icc.mp hh).1) hdiv
  have hsum :
      (∑ q ∈ Finset.Icc 1 cutoff,
        smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
          (q : ℝ)⁻¹) ≤
        ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
          (((harmonic cutoff : ℚ) : ℝ)) := by
    unfold smoothTwistedDiagonalMajorant at hsmooth
    have hfactor : 0 < 5 * T / 2 := by positivity
    nlinarith
  change _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
    ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
      (((harmonic cutoff : ℚ) : ℝ))
  calc
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        hughesYoungFiniteDiagonalArithmeticMajorant T ell B := by
      simpa only [F, ell, B] using hdiag'
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        (∑ q ∈ Finset.Icc 1 cutoff,
          smoothTwistedDiagonalFiber ell q (shortMobiusSquareCoeff T) ^ 2 *
            (q : ℝ)⁻¹) := by
      gcongr
    _ ≤ (((K + 2 : ℕ) : ℝ) ^ 2) * F *
        (ca ^ 2 * cd ^ 4 * (cutoff : ℝ) ^ (6 * δ) *
          (((harmonic cutoff : ℚ) : ℝ))) := by
      gcongr
    _ = _ := by ring

/-- The full inactive diagonal rectangle is still polynomially bounded at
the native depth.  This is the scale input needed to absorb every divisor
and harmonic loss into an arbitrary epsilon. -/
theorem hughesYoungInactiveCombinedArithmeticCutoff_le
    {T : ℝ} (hT : Real.exp 1 ≤ T) :
    ((((detectorCutoff T) ^ 2 *
      hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℕ) : ℝ)) ≤
      63 * T ^ (102 : ℝ) := by
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hcut := detectorCutoff_le_three_mul T hT1
  have hell : (((detectorCutoff T) ^ 2 : ℕ) : ℝ) ≤
      9 * T ^ (2 : ℝ) := by
    rw [Nat.cast_pow, Real.rpow_two]
    nlinarith
  have hfull :=
    hughesYoungTerminalFullDyadicBound_le_seven_mul_pow_hundred hT
  calc
    _ = (((detectorCutoff T) ^ 2 : ℕ) : ℝ) *
        (hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1) : ℝ) := by
      push_cast
      ring
    _ ≤ (9 * T ^ (2 : ℝ)) * (7 * T ^ (100 : ℕ)) := by
      gcongr
    _ = 63 * (T ^ (2 : ℝ) * T ^ (100 : ℝ)) := by
      norm_num
      ring
    _ = 63 * T ^ (102 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hT1)]
      norm_num

/-- The complete inactive diagonal at the conductor scale satisfies the
Hughes--Young `T^(1+ε)` estimate.  The exponent bookkeeping includes the
entire terminal dyadic rectangle, rather than only active boxes. -/
theorem hughesYoungConductorInactiveFiniteDiagonal_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungInactiveFiniteDiagonal T (T / 8)
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  intro ε hε
  let δ : ℝ := ε / 1000
  have hδ : 0 < δ := div_pos hε (by norm_num)
  obtain ⟨C, W, ca, cd, hC, hW, hca, hcd, hdiag⟩ :=
    exists_norm_hughesYoungInactiveFiniteDiagonal_le_power δ hδ
  let A : ℝ :=
    (100 / δ + 3) ^ 2 *
      ((15 / 4) * (1 / Real.pi) *
        (δ⁻¹ * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
      ca ^ 2 * cd ^ 4 * (1 + δ⁻¹) * (63 : ℝ) ^ (7 * δ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  apply IsBigO.of_bound A
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
  have hT1 : 1 ≤ T := by linarith [Real.exp_one_gt_d9]
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  let Q : ℕ := (detectorCutoff T) ^ 2 *
    hughesYoungFullDyadicBound (hughesYoungGlobalDepth T + 1)
  have hQone : 1 ≤ Q := by
    dsimp only [Q]
    have hc : 0 < detectorCutoff T := by simp [detectorCutoff]
    exact Nat.mul_pos (pow_pos hc 2)
      (hughesYoungFullDyadicBound_pos (hughesYoungGlobalDepth T + 1))
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQbound : (Q : ℝ) ≤ 63 * T ^ (102 : ℝ) := by
    simpa only [Q] using hughesYoungInactiveCombinedArithmeticCutoff_le hT
  have hHarm := harmonic_le_epsilon_rpow hδ Q
  have hmax : max 1 ((Q : ℝ) ^ δ) = (Q : ℝ) ^ δ :=
    max_eq_right (Real.one_le_rpow (by exact_mod_cast hQone) hδ.le)
  rw [hmax] at hHarm
  have hQpower : (Q : ℝ) ^ (7 * δ) ≤
      (63 : ℝ) ^ (7 * δ) * T ^ (714 * δ) := by
    calc
      (Q : ℝ) ^ (7 * δ) ≤
          (63 * T ^ (102 : ℝ)) ^ (7 * δ) := by
            exact Real.rpow_le_rpow hQ0 hQbound (by positivity)
      _ = (63 : ℝ) ^ (7 * δ) *
          (T ^ (102 : ℝ)) ^ (7 * δ) := by
            rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le _)]
      _ = (63 : ℝ) ^ (7 * δ) * T ^ (714 * δ) := by
            rw [← Real.rpow_mul hT0.le]
            congr 1
            ring_nf
  have hQcombine : (Q : ℝ) ^ (6 * δ) *
      (((harmonic Q : ℚ) : ℝ)) ≤
        (1 + δ⁻¹) * (63 : ℝ) ^ (7 * δ) * T ^ (714 * δ) := by
    calc
      _ ≤ (Q : ℝ) ^ (6 * δ) *
          ((1 + δ⁻¹) * (Q : ℝ) ^ δ) := by
            gcongr
      _ = (1 + δ⁻¹) * (Q : ℝ) ^ (7 * δ) := by
            have hQRpos : (0 : ℝ) < Q := by exact_mod_cast hQone
            rw [show 7 * δ = 6 * δ + δ by ring,
              Real.rpow_add hQRpos]
            ring
      _ ≤ (1 + δ⁻¹) *
          ((63 : ℝ) ^ (7 * δ) * T ^ (714 * δ)) :=
            mul_le_mul_of_nonneg_left hQpower (by positivity)
      _ = _ := by ring
  have hdepth := hughesYoungGlobalDepth_add_two_le_rpow hδ hT
  have hdepthSq : (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) ≤
      (100 / δ + 3) ^ 2 * T ^ (2 * δ) := by
    calc
      _ ≤ ((100 / δ + 3) * T ^ δ) ^ 2 := by gcongr
      _ = (100 / δ + 3) ^ 2 * T ^ (2 * δ) := by
        rw [mul_pow]
        rw [show (T ^ δ) ^ 2 = T ^ (2 * δ) by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le]
          ring_nf]
  have hlog : Real.log T ≤ δ⁻¹ * T ^ δ := by
    have := Real.log_le_rpow_div hT0.le hδ
    simpa [div_eq_mul_inv, mul_comm] using this
  let G : ℝ := (15 / 4) * (1 / Real.pi) *
    (δ⁻¹ * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))
  have hfactor0 : 0 ≤ (15 * T / 4) * (1 / Real.pi) *
      (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80)) := by
    have hlog0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    positivity
  have hfactor : (15 * T / 4) * (1 / Real.pi) *
      (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80)) ≤
        G * T ^ (1 + δ) := by
    calc
      _ ≤ (15 * T / 4) * (1 / Real.pi) *
          ((δ⁻¹ * T ^ δ) * Real.exp (4 * C) * W *
            Real.sqrt (Real.pi / 80)) := by gcongr
      _ = G * T ^ (1 + δ) := by
        dsimp only [G]
        have hp : T * T ^ δ = T ^ (1 + δ) := by
          calc
            T * T ^ δ = T ^ (1 : ℝ) * T ^ δ := by rw [Real.rpow_one]
            _ = T ^ ((1 : ℝ) + δ) := (Real.rpow_add hT0 1 δ).symm
        rw [← hp]
        ring
  have hharm0 : 0 ≤ (((harmonic Q : ℚ) : ℝ)) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    positivity
  have hpowcombine : T ^ (2 * δ) * T ^ (1 + δ) * T ^ (714 * δ) =
      T ^ (1 + 717 * δ) := by
    rw [← Real.rpow_add hT0, ← Real.rpow_add hT0]
    congr 1
    ring
  have hraw := hdiag (T := T) (H := T / 8)
    (R := hughesYoungConductorRadius T) (K := hughesYoungGlobalDepth T)
    hT (by positivity)
  have hbound :
      ‖hughesYoungInactiveFiniteDiagonal T (T / 8)
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
        A * T ^ (1 + 717 * δ) := by
    calc
      _ ≤ (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 * (Q : ℝ) ^ (6 * δ) *
          (((harmonic Q : ℚ) : ℝ)) := by simpa only [Q] using hraw
      _ = (((hughesYoungGlobalDepth T + 2 : ℕ) : ℝ) ^ 2) *
          ((15 * T / 4) * (1 / Real.pi) *
            (Real.log T * Real.exp (4 * C) * W * Real.sqrt (Real.pi / 80))) *
          ca ^ 2 * cd ^ 4 *
          ((Q : ℝ) ^ (6 * δ) * (((harmonic Q : ℚ) : ℝ))) := by ring
      _ ≤ ((100 / δ + 3) ^ 2 * T ^ (2 * δ)) *
          (G * T ^ (1 + δ)) * ca ^ 2 * cd ^ 4 *
          ((1 + δ⁻¹) * (63 : ℝ) ^ (7 * δ) *
            T ^ (714 * δ)) := by gcongr
      _ = A * T ^ (1 + 717 * δ) := by
        dsimp only [A, G]
        rw [← hpowcombine]
        ring
  have hexp : 1 + 717 * δ ≤ 1 + ε := by
    dsimp only [δ]
    linarith
  have hpow : T ^ (1 + 717 * δ) ≤ T ^ (1 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hT1 hexp
  have htarget : ‖T ^ ε * |T|‖ = T ^ (1 + ε) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (Real.rpow_nonneg hT0.le _) (abs_nonneg T)), abs_of_pos hT0]
    calc
      T ^ ε * T = T ^ ε * T ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = T ^ (ε + 1) := (Real.rpow_add hT0 ε 1).symm
      _ = T ^ (1 + ε) := by ring_nf
  rw [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg (hughesYoungInactiveFiniteDiagonal T (T / 8)
      (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T))), htarget]
  exact hbound.trans (mul_le_mul_of_nonneg_left hpow hA)

/-- Removing the exact diagonal from the exact inactive finite moment gives
the complete inactive off-diagonal estimate.  No DFI estimate is assumed in
this step: it is a consequence of the whole-contour cancellation bound and
the literal diagonal calculation above. -/
theorem hughesYoungConductorInactiveFiniteOffDiagonal_epsilonPowerBound :
    EpsilonPowerBound
      (fun T => ‖hughesYoungInactiveFiniteOffDiagonal T (T / 8)
        (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖)
      (fun T => T) := by
  let finite : ℝ → ℝ := fun T =>
    ‖hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
      (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖
  let diagonal : ℝ → ℝ := fun T =>
    ‖hughesYoungInactiveFiniteDiagonal T (T / 8)
      (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖
  have hfinite : EpsilonPowerBound finite (fun T => T) := by
    simpa only [finite] using
      hughesYoungConductorInactiveFiniteMoment_epsilonPowerBound
  have hdiagonal : EpsilonPowerBound diagonal (fun T => T) := by
    simpa only [diagonal] using
      hughesYoungConductorInactiveFiniteDiagonal_epsilonPowerBound
  have hsum := hfinite.add hdiagonal
  intro ε hε
  have hsumε := hsum ε hε
  have hdom :
      (fun T =>
        |‖hughesYoungInactiveFiniteOffDiagonal T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖|) =O[atTop]
      (fun T => |finite T + diagonal T|) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (Real.exp 1)] with T hT
    have hsplit := hughesYoungInactiveFiniteSmoothedMoment_eq_diagonal_add_offDiagonal
      hT (T / 8) (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)
    have hoff :
        hughesYoungInactiveFiniteOffDiagonal T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) =
          hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
              (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) -
            hughesYoungInactiveFiniteDiagonal T (T / 8)
              (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T) := by
      rw [hsplit]
      abel
    have htri :
        ‖hughesYoungInactiveFiniteOffDiagonal T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ ≤
          finite T + diagonal T := by
      rw [hoff]
      simpa only [finite, diagonal] using norm_sub_le
        (hughesYoungInactiveFiniteSmoothedMoment T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T))
        (hughesYoungInactiveFiniteDiagonal T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T))
    have hsum0 : 0 ≤ finite T + diagonal T := by
      dsimp only [finite, diagonal]
      positivity
    calc
      ‖|‖hughesYoungInactiveFiniteOffDiagonal T (T / 8)
          (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖|‖ =
          ‖hughesYoungInactiveFiniteOffDiagonal T (T / 8)
            (hughesYoungConductorRadius T) (hughesYoungGlobalDepth T)‖ := by simp
      _ ≤ finite T + diagonal T := htri
      _ = 1 * ‖|finite T + diagonal T|‖ := by
        rw [one_mul, Real.norm_eq_abs, abs_abs, abs_of_nonneg hsum0]
  exact hdom.trans hsumε

end RiemannZeta.GuthMaynard
