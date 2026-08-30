import RiemannZeta.GuthMaynard.HughesYoungCentralSourceBridge

open Complex Filter
open scoped BigOperators

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Quantitative arithmetic tail for the Hughes--Young shift completion

The equation-(84) source is indexed by a positive modulus/shift pair.  Its
absolute-convergence proof reindexes that pair by `(d,m,n)` with shift
`r = d*n`.  The lemmas below retain a positive power of this product.  This
is the arithmetic input needed to show that completing the finite signed
shift window is power-saving at the project's logarithmic dyadic depth.
-/

theorem sum_Icc_one_eq_tsum_pnat_cutoff
    (f : ℕ → ℂ) (L : ℕ) :
    (∑ n ∈ Finset.Icc 1 L, f n) =
      ∑' r : ℕ+, if (r : ℕ) ≤ L then f r else 0 := by
  let g : ℕ → ℂ := fun n => if 0 < n ∧ n ≤ L then f n else 0
  let fp : ℕ → ℂ := fun n => if n ≤ L then f n else 0
  calc
    (∑ n ∈ Finset.Icc 1 L, f n) =
        ∑ n ∈ Finset.Icc 1 L, g n := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Finset.mem_Icc] at hn
      have hn0 : 0 < n := by omega
      simp [g, hn, hn0]
    _ = ∑' n : ℕ, g n := by
      symm
      apply tsum_eq_sum (s := Finset.Icc 1 L)
      intro n hn
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      simp only [g]
      split_ifs with h
      · exfalso
        rcases hn with hn | hn <;> omega
      · rfl
    _ = ∑' n : ℕ, ({n : ℕ | 0 < n}.indicator fp) n := by
      apply tsum_congr
      intro n
      by_cases hn : 0 < n
      · simp [g, fp, hn]
      · simp [g, fp, hn]
    _ = ∑' r : ℕ+, fp r := by
      simpa only [PNat] using (tsum_subtype {n : ℕ | 0 < n} fp).symm
    _ = _ := by rfl

/-- The factorized equation-(96) majorant restricted to shifts `d*n > B`. -/
noncomputable def hughesYoungPositiveTripleShiftTailWeight
    (A C B : ℝ) (x : (ℕ+ × ℕ+) × ℕ+) : ℝ :=
  if B < ((x.1.1 : ℕ) : ℝ) * ((x.2 : ℕ) : ℝ) then
    hughesYoungPositiveTripleWeight A C x
  else 0

theorem hughesYoungPositiveTripleShiftTailWeight_nonneg
    {A C B : ℝ} (x : (ℕ+ × ℕ+) × ℕ+) :
    0 ≤ hughesYoungPositiveTripleShiftTailWeight A C B x := by
  unfold hughesYoungPositiveTripleShiftTailWeight
  split_ifs
  · exact hughesYoungPositiveTripleWeight_nonneg A C x
  · exact le_rfl

/-- On a shift beyond `B`, half of the available `r^(-C)` convergence can
be extracted as the explicit factor `B^(-C/2)`. -/
theorem hughesYoungPositiveTripleWeight_le_shiftTailFactor
    {A C B : ℝ} (hC : 0 < C) (hB : 0 < B)
    {x : (ℕ+ × ℕ+) × ℕ+}
    (hx : B < ((x.1.1 : ℕ) : ℝ) * ((x.2 : ℕ) : ℝ)) :
    hughesYoungPositiveTripleWeight A C x ≤
      B ^ (-(C / 2)) * hughesYoungPositiveTripleWeight A (C / 2) x := by
  let d : ℝ := ((x.1.1 : ℕ) : ℝ)
  let m : ℝ := ((x.1.2 : ℕ) : ℝ)
  let n : ℝ := ((x.2 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp only [d]
    positivity
  have hm : 0 < m := by
    dsimp only [m]
    positivity
  have hn : 0 < n := by
    dsimp only [n]
    positivity
  have hdn : 0 < d * n := mul_pos hd hn
  have hpower :
      (d * n) ^ (-(C / 2)) ≤ B ^ (-(C / 2)) :=
    Real.rpow_le_rpow_of_nonpos hB hx.le (by linarith)
  have hfactor :
      hughesYoungPositiveTripleWeight A C x =
        (d * n) ^ (-(C / 2)) *
          hughesYoungPositiveTripleWeight A (C / 2) x := by
    unfold hughesYoungPositiveTripleWeight
    change d ^ (-(A + C)) * m ^ (-A) * n ^ (-(1 + C)) =
      (d * n) ^ (-(C / 2)) *
        (d ^ (-(A + C / 2)) * m ^ (-A) * n ^ (-(1 + C / 2)))
    rw [Real.mul_rpow (le_of_lt hd) (le_of_lt hn)]
    rw [show d ^ (-(A + C)) =
        d ^ (-(C / 2)) * d ^ (-(A + C / 2)) by
      rw [← Real.rpow_add hd]
      congr 1
      ring]
    rw [show n ^ (-(1 + C)) =
        n ^ (-(C / 2)) * n ^ (-(1 + C / 2)) by
      rw [← Real.rpow_add hn]
      congr 1
      ring]
    ring
  rw [hfactor]
  exact mul_le_mul_of_nonneg_right hpower
    (hughesYoungPositiveTripleWeight_nonneg A (C / 2) x)

/-- Absolute summability of the shift-tail majorant, uniformly with an
explicit negative power of the cutoff. -/
theorem summable_hughesYoungPositiveTripleShiftTailWeight
    {A C B : ℝ} (hA : 1 < A) (hC : 0 < C) (hB : 0 < B) :
    Summable (hughesYoungPositiveTripleShiftTailWeight A C B) := by
  have hhalf : 0 < C / 2 := by positivity
  have hmajor : Summable (fun x : (ℕ+ × ℕ+) × ℕ+ =>
      B ^ (-(C / 2)) * hughesYoungPositiveTripleWeight A (C / 2) x) :=
    (summable_hughesYoungPositiveTripleWeight hA hhalf).mul_left _
  apply Summable.of_norm_bounded hmajor
  intro x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (hughesYoungPositiveTripleShiftTailWeight_nonneg x)]
  unfold hughesYoungPositiveTripleShiftTailWeight
  split_ifs with hx
  · exact hughesYoungPositiveTripleWeight_le_shiftTailFactor hC hB hx
  · exact mul_nonneg (Real.rpow_nonneg hB.le _)
      (hughesYoungPositiveTripleWeight_nonneg A (C / 2) x)

/-- Quantitative total-mass form of the preceding summability theorem. -/
theorem tsum_hughesYoungPositiveTripleShiftTailWeight_le
    {A C B : ℝ} (hA : 1 < A) (hC : 0 < C) (hB : 0 < B) :
    (∑' x : (ℕ+ × ℕ+) × ℕ+,
        hughesYoungPositiveTripleShiftTailWeight A C B x) ≤
      B ^ (-(C / 2)) *
        ∑' x : (ℕ+ × ℕ+) × ℕ+,
          hughesYoungPositiveTripleWeight A (C / 2) x := by
  have hhalf : 0 < C / 2 := by positivity
  rw [← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro x
    unfold hughesYoungPositiveTripleShiftTailWeight
    split_ifs with hx
    · exact hughesYoungPositiveTripleWeight_le_shiftTailFactor hC hB hx
    · exact mul_nonneg (Real.rpow_nonneg hB.le _)
        (hughesYoungPositiveTripleWeight_nonneg A (C / 2) x)
  · exact summable_hughesYoungPositiveTripleShiftTailWeight hA hC hB
  · exact (summable_hughesYoungPositiveTripleWeight hA hhalf).mul_left _

/-- The same tail expressed in the equation-(84) `(modulus,shift)`
coordinates.  The second coordinate is the positive shift. -/
noncomputable def hughesYoungPositivePairShiftTailMajorant
    (A C B : ℝ) : ℝ :=
  ∑' y : ℕ+ × ℕ+,
    if B < ((y.2 : ℕ) : ℝ) then
      hughesYoungPositivePairMajorant A C y
    else 0

/-- Fiberwise regrouping does not alter the shift-tail mass.  This is the
quantitative counterpart of the exact `(d,m,n) ↦ (d*m,d*n)` reindexing in
the absolute-convergence proof. -/
theorem hughesYoungPositivePairShiftTailMajorant_eq_triple
    {A C B : ℝ} (hA : 1 < A) (hC : 0 < C) (hB : 0 < B) :
    hughesYoungPositivePairShiftTailMajorant A C B =
      ∑' x : (ℕ+ × ℕ+) × ℕ+,
        hughesYoungPositiveTripleShiftTailWeight A C B x := by
  have htail :=
    summable_hughesYoungPositiveTripleShiftTailWeight hA hC hB
  have hfiber := htail.hasSum.tsum_fiberwise hughesYoungPositiveTripleMap
  rw [hughesYoungPositivePairShiftTailMajorant]
  calc
    (∑' y : ℕ+ × ℕ+,
        if B < ((y.2 : ℕ) : ℝ) then
          hughesYoungPositivePairMajorant A C y
        else 0) =
        ∑' y : ℕ+ × ℕ+,
          ∑' x : {x : (ℕ+ × ℕ+) × ℕ+ //
              hughesYoungPositiveTripleMap x = y},
            hughesYoungPositiveTripleShiftTailWeight A C B x.1 := by
      apply tsum_congr
      intro y
      by_cases hy : B < ((y.2 : ℕ) : ℝ)
      · rw [if_pos hy]
        unfold hughesYoungPositivePairMajorant
        apply tsum_congr
        intro x
        unfold hughesYoungPositiveTripleShiftTailWeight
        have hcoord : ((x.1.1.1 : ℕ) : ℝ) * ((x.1.2 : ℕ) : ℝ) =
            ((y.2 : ℕ) : ℝ) := by
          have h := congrArg (fun z : ℕ+ × ℕ+ => ((z.2 : ℕ) : ℝ)) x.2
          simpa [hughesYoungPositiveTripleMap] using h
        rw [hcoord, if_pos hy]
      · rw [if_neg hy]
        symm
        calc
          (∑' x : {x : (ℕ+ × ℕ+) × ℕ+ //
              hughesYoungPositiveTripleMap x = y},
              hughesYoungPositiveTripleShiftTailWeight A C B x.1) =
              ∑' _x : {x : (ℕ+ × ℕ+) × ℕ+ //
                hughesYoungPositiveTripleMap x = y}, (0 : ℝ) := by
            apply tsum_congr
            intro x
            unfold hughesYoungPositiveTripleShiftTailWeight
            have hcoord : ((x.1.1.1 : ℕ) : ℝ) * ((x.1.2 : ℕ) : ℝ) =
                ((y.2 : ℕ) : ℝ) := by
              have h := congrArg (fun z : ℕ+ × ℕ+ => ((z.2 : ℕ) : ℝ)) x.2
              simpa [hughesYoungPositiveTripleMap] using h
            rw [hcoord, if_neg hy]
          _ = 0 := tsum_zero
    _ = ∑' x : (ℕ+ × ℕ+) × ℕ+,
          hughesYoungPositiveTripleShiftTailWeight A C B x :=
      hfiber.tsum_eq

/-- Explicit negative-power bound for the equation-(84) pair tail. -/
theorem hughesYoungPositivePairShiftTailMajorant_le
    {A C B : ℝ} (hA : 1 < A) (hC : 0 < C) (hB : 0 < B) :
    hughesYoungPositivePairShiftTailMajorant A C B ≤
      B ^ (-(C / 2)) *
        ∑' x : (ℕ+ × ℕ+) × ℕ+,
          hughesYoungPositiveTripleWeight A (C / 2) x := by
  rw [hughesYoungPositivePairShiftTailMajorant_eq_triple hA hC hB]
  exact tsum_hughesYoungPositiveTripleShiftTailWeight_le hA hC hB

theorem summable_hughesYoungPositivePairShiftTailWeight
    {A C B : ℝ} (hA : 1 < A) (hC : 0 < C) :
    Summable (fun y : ℕ+ × ℕ+ =>
      if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungPositivePairMajorant A C y
      else 0) := by
  refine Summable.of_nonneg_of_le (fun y => ?_) (fun y => ?_)
    (summable_hughesYoungPositivePairMajorant hA hC)
  · split_ifs
    · exact tsum_nonneg fun _ => hughesYoungPositiveTripleWeight_nonneg A C _
    · exact le_rfl
  · split_ifs
    · exact le_rfl
    · exact tsum_nonneg fun _ => hughesYoungPositiveTripleWeight_nonneg A C _

/-- The portion of one equation-(96) arithmetic moment whose positive shift
exceeds `B`.  This is the source-level object omitted by the finite DFI
rectangle. -/
noncomputable def hughesYoungEquation96VerticalShiftTailMoment
    (h k : ℕ) (i j : Bool) (u B : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    if B < ((y.2 : ℕ) : ℝ) then
      hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y *
        hughesYoungDFIPositiveLogSelectorLeft j h y *
        hughesYoungDFIPositiveLogSelectorRight i k y
    else 0

/-- Complementary retained portion of an equation-(96) moment. -/
noncomputable def hughesYoungEquation96VerticalPrefixMoment
    (h k : ℕ) (i j : Bool) (u B : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    if ((y.2 : ℕ) : ℝ) ≤ B then
      hughesYoungEquation96PositiveTerm h k 1 1
          ((2 : ℂ) + (2 * u : ℂ) * I) y *
        hughesYoungDFIPositiveLogSelectorLeft j h y *
        hughesYoungDFIPositiveLogSelectorRight i k y
    else 0

theorem summable_hughesYoungEquation96VerticalShiftTailMoment
    (i j : Bool) (u B : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungEquation96PositiveTerm h k 1 1
            ((2 : ℂ) + (2 * u : ℂ) * I) y *
          hughesYoungDFIPositiveLogSelectorLeft j h y *
          hughesYoungDFIPositiveLogSelectorRight i k y
      else 0) := by
  let K : ℝ := ((h : ℝ) ^ (1 / 2 + 2 * η) *
      (k : ℝ) ^ (1 / 2 + 2 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * (if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y
      else 0)) :=
    (summable_hughesYoungPositivePairShiftTailWeight hA hC).mul_left K
  exact Summable.of_norm_bounded hm fun y => by
    by_cases hy : B < ((y.2 : ℕ) : ℝ)
    · rw [if_pos hy, if_pos hy]
      dsimp only [K]
      exact norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
        j i u hh hk hη hη4 y
    · rw [if_neg hy, if_neg hy, norm_zero]
      positivity

theorem summable_hughesYoungEquation96VerticalPrefixMoment
    (i j : Bool) (u B : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    Summable (fun y : ℕ+ × ℕ+ =>
      if ((y.2 : ℕ) : ℝ) ≤ B then
        hughesYoungEquation96PositiveTerm h k 1 1
            ((2 : ℂ) + (2 * u : ℂ) * I) y *
          hughesYoungDFIPositiveLogSelectorLeft j h y *
          hughesYoungDFIPositiveLogSelectorRight i k y
      else 0) := by
  let K : ℝ := ((h : ℝ) ^ (1 / 2 + 2 * η) *
      (k : ℝ) ^ (1 / 2 + 2 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y) :=
    (summable_hughesYoungPositivePairMajorant hA hC).mul_left K
  exact Summable.of_norm_bounded hm fun y => by
    by_cases hy : ((y.2 : ℕ) : ℝ) ≤ B
    · rw [if_pos hy]
      dsimp only [K]
      exact norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
        j i u hh hk hη hη4 y
    · rw [if_neg hy, norm_zero]
      exact mul_nonneg (by dsimp only [K]; positivity)
        (tsum_nonneg fun _ =>
          hughesYoungPositiveTripleWeight_nonneg (1 + 2 * η) (1 - 2 * η) _)

/-- Exact partition of the complete equation-(84) arithmetic moment into
the shifts retained by the DFI rectangle and its complementary tail. -/
theorem hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
    (i j : Bool) (u B : ℝ) {h k : ℕ}
    (hh : 0 < h) (hk : 0 < k) (hhk : h.Coprime k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompletePositiveMomentAt h k i j u =
      hughesYoungEquation96VerticalPrefixMoment h k i j u B +
        hughesYoungEquation96VerticalShiftTailMoment h k i j u B := by
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_equation96 i j u hhk]
  unfold hughesYoungEquation96VerticalPrefixMoment
    hughesYoungEquation96VerticalShiftTailMoment
  rw [← (summable_hughesYoungEquation96VerticalPrefixMoment
      i j u B hh hk hη hη4).tsum_add
    (summable_hughesYoungEquation96VerticalShiftTailMoment
      i j u B hh hk hη hη4)]
  apply tsum_congr
  intro y
  by_cases hy : B < ((y.2 : ℕ) : ℝ)
  · rw [if_neg (not_le.mpr hy), if_pos hy]
    simp
  · rw [if_pos (not_lt.mp hy), if_neg hy]
    simp

/-- Quantitative source-level tail bound.  It combines the exact
equation-(96) coefficient estimate with the explicit `B⁻(1-2η)/2`
arithmetic saving proved above. -/
theorem norm_hughesYoungEquation96VerticalShiftTailMoment_le
    (i j : Bool) (u : ℝ) {B : ℝ} (hB : 0 < B)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation96VerticalShiftTailMoment h k i j u B‖ ≤
      (((h : ℝ) ^ (1 / 2 + 2 * η) * (k : ℝ) ^ (1 / 2 + 2 * η)) *
          (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
          ((h : ℝ) ^ η * (k : ℝ) ^ η)) *
        (B ^ (-((1 - 2 * η) / 2)) *
          (∑' x : (ℕ+ × ℕ+) × ℕ+,
            hughesYoungPositiveTripleWeight
              (1 + 2 * η) ((1 - 2 * η) / 2) x)) := by
  let K : ℝ := ((h : ℝ) ^ (1 / 2 + 2 * η) *
      (k : ℝ) ^ (1 / 2 + 2 * η)) *
    (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
    ((h : ℝ) ^ η * (k : ℝ) ^ η)
  have hA : 1 < 1 + 2 * η := by linarith
  have hC : 0 < 1 - 2 * η := by linarith
  have hs := summable_hughesYoungEquation96VerticalShiftTailMoment
    i j u B hh hk hη hη4
  have hm : Summable (fun y : ℕ+ × ℕ+ =>
      K * (if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y
      else 0)) :=
    (summable_hughesYoungPositivePairShiftTailWeight hA hC).mul_left K
  calc
    _ ≤ ∑' y : ℕ+ × ℕ+,
        ‖if B < ((y.2 : ℕ) : ℝ) then
            hughesYoungEquation96PositiveTerm h k 1 1
                ((2 : ℂ) + (2 * u : ℂ) * I) y *
              hughesYoungDFIPositiveLogSelectorLeft j h y *
              hughesYoungDFIPositiveLogSelectorRight i k y
          else 0‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' y : ℕ+ × ℕ+,
        K * (if B < ((y.2 : ℕ) : ℝ) then
          hughesYoungPositivePairMajorant (1 + 2 * η) (1 - 2 * η) y
        else 0) := hs.norm.tsum_le_tsum (fun y => by
          by_cases hy : B < ((y.2 : ℕ) : ℝ)
          · rw [if_pos hy, if_pos hy]
            exact norm_hughesYoungEquation96VerticalTerm_mul_logSelectors_le
              j i u hh hk hη hη4 y
          · rw [if_neg hy, if_neg hy, norm_zero]
            positivity) hm
    _ = K * hughesYoungPositivePairShiftTailMajorant
          (1 + 2 * η) (1 - 2 * η) B := by
      rw [tsum_mul_left]
      rfl
    _ ≤ K * (B ^ (-((1 - 2 * η) / 2)) *
          (∑' x : (ℕ+ × ℕ+) × ℕ+,
            hughesYoungPositiveTripleWeight
              (1 + 2 * η) ((1 - 2 * η) / 2) x)) := by
      apply mul_le_mul_of_nonneg_left
        (hughesYoungPositivePairShiftTailMajorant_le hA hC hB)
      dsimp only [K]
      positivity
    _ = _ := by rfl

/-- The retained positive equation-(84) source line after imposing the DFI
positive-shift cutoff. -/
noncomputable def hughesYoungEquation84PositivePrefixSourceLine
    (T t : ℝ) (h k a b : ℕ) (u B : ℝ) : ℂ :=
  hughesYoungEquation84CompletePositiveOuter T t h k a b u *
    (hughesYoungEquation96VerticalPrefixMoment a b false false u B *
        hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalPrefixMoment a b true false u B *
        hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalPrefixMoment a b false true u B *
        hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalPrefixMoment a b true true u B *
        hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I))

/-- The omitted positive equation-(84) source line after imposing the DFI
positive-shift cutoff. -/
noncomputable def hughesYoungEquation84PositiveShiftTailSourceLine
    (T t : ℝ) (h k a b : ℕ) (u B : ℝ) : ℂ :=
  hughesYoungEquation84CompletePositiveOuter T t h k a b u *
    (hughesYoungEquation96VerticalShiftTailMoment a b false false u B *
        hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalShiftTailMoment a b true false u B *
        hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalShiftTailMoment a b false true u B *
        hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalShiftTailMoment a b true true u B *
        hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I))

/-- Exact source-line finite/tail partition before either contour or height
integration. -/
theorem hughesYoungEquation84CompletePositiveSourceLine_eq_prefix_add_shiftTail
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u B : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompletePositiveSourceLine T t h k a b u =
      hughesYoungEquation84PositivePrefixSourceLine T t h k a b u B +
        hughesYoungEquation84PositiveShiftTailSourceLine T t h k a b u B := by
  rw [hughesYoungEquation84CompletePositiveSourceLine_eq_fourMoments
    T t h k ha hb hab u hη hη4]
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
      false false u B ha hb hab hη hη4,
    hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
      true false u B ha hb hab hη hη4,
    hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
      false true u B ha hb hab hη hη4,
    hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
      true true u B ha hb hab hη hη4]
  unfold hughesYoungEquation84PositivePrefixSourceLine
    hughesYoungEquation84PositiveShiftTailSourceLine
  ring

theorem tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
    (i j : Bool) (u B : ℝ) {a b : ℕ} (hab : a.Coprime b) :
    (∑' y : ℕ+ × ℕ+,
      if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungEquation84PositiveSourceArithmeticTerm a b i j u y
      else 0) =
      hughesYoungEquation96VerticalShiftTailMoment a b i j u B := by
  unfold hughesYoungEquation96VerticalShiftTailMoment
  apply tsum_congr
  intro y
  by_cases hy : B < ((y.2 : ℕ) : ℝ)
  · rw [if_pos hy, if_pos hy]
    unfold hughesYoungEquation84PositiveSourceArithmeticTerm
    exact dfiEquation84PositiveMomentAtTerm_eq_equation96SelectorTerm
      i j u hab y
  · rw [if_neg hy, if_neg hy]

/-- Direct tail of the positive contour-term series. -/
noncomputable def hughesYoungEquation84PositiveContourTermShiftTail
    (T t : ℝ) (h k a b : ℕ) (u B : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    if B < ((y.2 : ℕ) : ℝ) then
      hughesYoungEquation84PositiveContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
    else 0

/-- The `hughesYoungEquation84PositiveContourTermPrefix` definition used by the source-facing construction in `HughesYoungShiftTail`. -/
noncomputable def hughesYoungEquation84PositiveContourTermPrefix
    (T t : ℝ) (h k a b : ℕ) (u B : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    if ((y.2 : ℕ) : ℝ) ≤ B then
      hughesYoungEquation84PositiveContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
    else 0

theorem hughesYoungEquation84CompletePositiveSourceLine_eq_contourPrefix_add_tail
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u B : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompletePositiveSourceLine T t h k a b u =
      hughesYoungEquation84PositiveContourTermPrefix T t h k a b u B +
        hughesYoungEquation84PositiveContourTermShiftTail T t h k a b u B := by
  have hs := summable_hughesYoungEquation84CompletePositiveSourceLine
    T t h k ha hb hab u hη hη4
  have hp : Summable (fun y : ℕ+ × ℕ+ =>
      if ((y.2 : ℕ) : ℝ) ≤ B then
        hughesYoungEquation84PositiveContourTerm T t h k a b
          (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
      else 0) :=
    Summable.of_norm_bounded hs.norm fun y => by
      by_cases hy : ((y.2 : ℕ) : ℝ) ≤ B <;> simp [hy]
  have ht : Summable (fun y : ℕ+ × ℕ+ =>
      if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungEquation84PositiveContourTerm T t h k a b
          (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
      else 0) :=
    Summable.of_norm_bounded hs.norm fun y => by
      by_cases hy : B < ((y.2 : ℕ) : ℝ) <;> simp [hy]
  unfold hughesYoungEquation84CompletePositiveSourceLine
    hughesYoungEquation84PositiveContourTermPrefix
    hughesYoungEquation84PositiveContourTermShiftTail
  rw [← hp.tsum_add ht]
  apply tsum_congr
  intro y
  by_cases hy : B < ((y.2 : ℕ) : ℝ)
  · rw [if_neg (not_le.mpr hy), if_pos hy]
    simp
  · rw [if_pos (not_lt.mp hy), if_neg hy]
    simp

/-- Reindexing the retained positive shift/modulus series by shifts first
gives the same source prefix. -/
theorem tsum_hughesYoungEquation84PositiveContourSeries_prefix_eq
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u B : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (∑' r : ℕ+,
      if ((r : ℕ) : ℝ) ≤ B then
        hughesYoungEquation84PositiveContourSeries T t h k a b r
          ((1 : ℂ) + (u : ℂ) * I)
      else 0) =
      hughesYoungEquation84PositiveContourTermPrefix T t h k a b u B := by
  let F : ℕ+ × ℕ+ → ℂ := fun y =>
    if ((y.2 : ℕ) : ℝ) ≤ B then
      hughesYoungEquation84PositiveContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
    else 0
  have hFull := summable_hughesYoungEquation84CompletePositiveSourceLine
    T t h k ha hb hab u hη hη4
  have hF : Summable F :=
    Summable.of_norm_bounded hFull.norm fun y => by
      by_cases hy : ((y.2 : ℕ) : ℝ) ≤ B <;> simp [F, hy]
  have hSwap : Summable (fun y : ℕ+ × ℕ+ => F y.swap) :=
    hF.comp_injective (Equiv.prodComm ℕ+ ℕ+).injective
  calc
    _ = ∑' r : ℕ+, ∑' q : ℕ+,
        if ((r : ℕ) : ℝ) ≤ B then
          hughesYoungEquation84PositiveContourTerm T t h k a b r q
            ((1 : ℂ) + (u : ℂ) * I)
        else 0 := by
      apply tsum_congr
      intro r
      by_cases hr : ((r : ℕ) : ℝ) ≤ B
      · rw [if_pos hr]
        simp_rw [if_pos hr]
        unfold hughesYoungEquation84PositiveContourSeries
        exact tsum_hughesYoungEquation84PositiveContourTerm_nat_eq_pnat
          T t h k a b r ((1 : ℂ) + (u : ℂ) * I)
      · rw [if_neg hr]
        simp_rw [if_neg hr]
        exact tsum_zero.symm
    _ = ∑' y : ℕ+ × ℕ+, F y.swap := hSwap.tsum_prod.symm
    _ = ∑' y : ℕ+ × ℕ+, F y :=
      (Equiv.prodComm ℕ+ ℕ+).tsum_eq F
    _ = _ := by rfl

theorem sum_hughesYoungEquation84PositiveContourSeries_Icc_eq_prefix
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) (L : ℕ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (∑ r ∈ Finset.Icc 1 L,
      hughesYoungEquation84PositiveContourSeries T t h k a b r
        ((1 : ℂ) + (u : ℂ) * I)) =
      hughesYoungEquation84PositiveContourTermPrefix
        T t h k a b u (L : ℝ) := by
  rw [sum_Icc_one_eq_tsum_pnat_cutoff]
  rw [← tsum_hughesYoungEquation84PositiveContourSeries_prefix_eq
    T t h k ha hb hab u (L : ℝ) hη hη4]
  apply tsum_congr
  intro r
  have hr : (((r : ℕ) : ℝ) ≤ (L : ℝ)) ↔ (r : ℕ) ≤ L := by norm_cast
  by_cases hrl : (r : ℕ) ≤ L
  · simp [hrl, hr.mpr hrl]
  · have hreal : ¬(((r : ℕ) : ℝ) ≤ (L : ℝ)) := fun h => hrl (hr.mp h)
    simp [hrl, hreal]
theorem hughesYoungEquation84PositiveContourTermShiftTail_eq_sourceTail
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u B : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84PositiveContourTermShiftTail T t h k a b u B =
      hughesYoungEquation84PositiveShiftTailSourceLine T t h k a b u B := by
  let P := hughesYoungEquation84CompletePositiveOuter T t h k a b u
  let K00 := hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)
  let K10 := hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)
  let K01 := hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)
  let K11 := hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)
  let f : Bool → Bool → (ℕ+ × ℕ+) → ℂ := fun i j y =>
    if B < ((y.2 : ℕ) : ℝ) then
      hughesYoungEquation84PositiveSourceArithmeticTerm a b i j u y
    else 0
  have hf (i j : Bool) : Summable (f i j) := by
    have hs := summable_hughesYoungEquation96VerticalShiftTailMoment
      i j u B ha hb hη hη4
    apply hs.congr
    intro y
    simp only [f]
    by_cases hy : B < ((y.2 : ℕ) : ℝ)
    · rw [if_pos hy, if_pos hy]
      unfold hughesYoungEquation84PositiveSourceArithmeticTerm
      exact (dfiEquation84PositiveMomentAtTerm_eq_equation96SelectorTerm
        i j u hab y).symm
    · rw [if_neg hy, if_neg hy]
  unfold hughesYoungEquation84PositiveContourTermShiftTail
  rw [show (∑' y : ℕ+ × ℕ+,
      if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungEquation84PositiveContourTerm T t h k a b
          (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
      else 0) =
      ∑' y : ℕ+ × ℕ+,
        P * (f false false y * K00 + f true false y * K10 +
          f false true y * K01 + f true true y * K11) by
    apply tsum_congr
    intro y
    by_cases hy : B < ((y.2 : ℕ) : ℝ)
    · rw [if_pos hy]
      simp only [f, hy, ↓reduceIte]
      simpa only [P, K00, K10, K01, K11] using
        hughesYoungEquation84PositiveSourceTerm_eq_fourTerms
          T t h k a b u y
    · rw [if_neg hy]
      simp [f, hy]]
  simp_rw [tsum_mul_left]
  rw [((((hf false false).mul_right K00).add
        ((hf true false).mul_right K10)).add
      ((hf false true).mul_right K01)).tsum_add
        ((hf true true).mul_right K11),
    (((hf false false).mul_right K00).add
      ((hf true false).mul_right K10)).tsum_add
        ((hf false true).mul_right K01),
    ((hf false false).mul_right K00).tsum_add
      ((hf true false).mul_right K10)]
  simp only [tsum_mul_right]
  rw [tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
      false false u B hab,
    tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
      true false u B hab,
    tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
      false true u B hab,
    tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
      true true u B hab]
  rfl

/-- Explicit arithmetic factor in the positive equation-(84) source tail. -/
noncomputable def hughesYoungEquation84ShiftTailArithmeticBound
    (a b : ℕ) (η B : ℝ) : ℝ :=
  (((a : ℝ) ^ (1 / 2 + 2 * η) * (b : ℝ) ^ (1 / 2 + 2 * η)) *
      (1 + 6 * η⁻¹ + 2 * |Real.eulerMascheroniConstant|) ^ 2 *
      ((a : ℝ) ^ η * (b : ℝ) ^ η)) *
    (B ^ (-((1 - 2 * η) / 2)) *
      (∑' x : (ℕ+ × ℕ+) × ℕ+,
        hughesYoungPositiveTripleWeight
          (1 + 2 * η) ((1 - 2 * η) / 2) x))

theorem hughesYoungEquation84ShiftTailArithmeticBound_nonneg
    (a b : ℕ) {η B : ℝ} (hB : 0 < B) :
    0 ≤ hughesYoungEquation84ShiftTailArithmeticBound a b η B := by
  unfold hughesYoungEquation84ShiftTailArithmeticBound
  exact mul_nonneg (by positivity) <|
    mul_nonneg (by positivity) <|
      tsum_nonneg fun _ =>
        hughesYoungPositiveTripleWeight_nonneg
          (1 + 2 * η) ((1 - 2 * η) / 2) _

/-- Pointwise equation-(84) source-tail estimate, retaining the explicit
negative power of the DFI shift cutoff. -/
theorem norm_hughesYoungEquation84PositiveShiftTailSourceLine_le
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (u : ℝ) {B : ℝ} (hB : 0 < B)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84PositiveShiftTailSourceLine T t h k a b u B‖ ≤
      ‖hughesYoungEquation84CompletePositiveOuter T t h k a b u‖ *
        hughesYoungEquation84ShiftTailArithmeticBound a b η B *
        (‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖) := by
  let D := hughesYoungEquation84ShiftTailArithmeticBound a b η B
  have hD : 0 ≤ D :=
    hughesYoungEquation84ShiftTailArithmeticBound_nonneg a b hB
  have h00 := norm_hughesYoungEquation96VerticalShiftTailMoment_le
    false false u hB ha hb hη hη4
  have h10 := norm_hughesYoungEquation96VerticalShiftTailMoment_le
    true false u hB ha hb hη hη4
  have h01 := norm_hughesYoungEquation96VerticalShiftTailMoment_le
    false true u hB ha hb hη hη4
  have h11 := norm_hughesYoungEquation96VerticalShiftTailMoment_le
    true true u hB ha hb hη hη4
  change ‖hughesYoungEquation96VerticalShiftTailMoment a b false false u B‖ ≤ D at h00
  change ‖hughesYoungEquation96VerticalShiftTailMoment a b true false u B‖ ≤ D at h10
  change ‖hughesYoungEquation96VerticalShiftTailMoment a b false true u B‖ ≤ D at h01
  change ‖hughesYoungEquation96VerticalShiftTailMoment a b true true u B‖ ≤ D at h11
  unfold hughesYoungEquation84PositiveShiftTailSourceLine
  rw [norm_mul]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤
        ‖hughesYoungEquation96VerticalShiftTailMoment a b false false u B‖ *
            ‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation96VerticalShiftTailMoment a b true false u B‖ *
            ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation96VerticalShiftTailMoment a b false true u B‖ *
            ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation96VerticalShiftTailMoment a b true true u B‖ *
            ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ := by
      calc
        _ ≤ ‖hughesYoungEquation96VerticalShiftTailMoment a b false false u B *
                hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I) +
              hughesYoungEquation96VerticalShiftTailMoment a b true false u B *
                hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I) +
              hughesYoungEquation96VerticalShiftTailMoment a b false true u B *
                hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
              ‖hughesYoungEquation96VerticalShiftTailMoment a b true true u B *
                hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ :=
            norm_add_le _ _
        _ ≤ (‖hughesYoungEquation96VerticalShiftTailMoment a b false false u B *
                hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I) +
              hughesYoungEquation96VerticalShiftTailMoment a b true false u B *
                hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
              ‖hughesYoungEquation96VerticalShiftTailMoment a b false true u B *
                hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖) +
              ‖hughesYoungEquation96VerticalShiftTailMoment a b true true u B *
                hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ := by
            gcongr
            exact norm_add_le _ _
        _ ≤ ((‖hughesYoungEquation96VerticalShiftTailMoment a b false false u B *
                hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
              ‖hughesYoungEquation96VerticalShiftTailMoment a b true false u B *
                hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖) +
              ‖hughesYoungEquation96VerticalShiftTailMoment a b false true u B *
                hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖) +
              ‖hughesYoungEquation96VerticalShiftTailMoment a b true true u B *
                hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ := by
            gcongr
            exact norm_add_le _ _
        _ = _ := by simp only [norm_mul]
    _ ≤ D * ‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          D * ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          D * ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          D * ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖ := by
      gcongr
    _ = D *
        (‖hughesYoungEquation84Kernel00 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 t ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 t ((1 : ℂ) + (u : ℂ) * I)‖) := by ring
    _ = _ := by rfl

/-- Coordinate-swapped retained source line for negative shifts. -/
noncomputable def hughesYoungEquation84NegativePrefixSourceLine
    (T t : ℝ) (h k a b : ℕ) (u B : ℝ) : ℂ :=
  hughesYoungEquation84CompleteNegativeOuter T t h k a b u *
    (hughesYoungEquation96VerticalPrefixMoment b a false false u B *
        hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalPrefixMoment b a true false u B *
        hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalPrefixMoment b a false true u B *
        hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalPrefixMoment b a true true u B *
        hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I))

/-- Coordinate-swapped omitted source line for negative shifts. -/
noncomputable def hughesYoungEquation84NegativeShiftTailSourceLine
    (T t : ℝ) (h k a b : ℕ) (u B : ℝ) : ℂ :=
  hughesYoungEquation84CompleteNegativeOuter T t h k a b u *
    (hughesYoungEquation96VerticalShiftTailMoment b a false false u B *
        hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalShiftTailMoment b a true false u B *
        hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalShiftTailMoment b a false true u B *
        hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I) +
      hughesYoungEquation96VerticalShiftTailMoment b a true true u B *
        hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I))

theorem hughesYoungEquation84CompleteNegativeSourceLine_eq_prefix_add_shiftTail
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u B : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u =
      hughesYoungEquation84NegativePrefixSourceLine T t h k a b u B +
        hughesYoungEquation84NegativeShiftTailSourceLine T t h k a b u B := by
  rw [hughesYoungEquation84CompleteNegativeSourceLine_eq_fourMoments
    T t h k ha hb hab u hη hη4]
  rw [hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
      false false u B hb ha hab.symm hη hη4,
    hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
      true false u B hb ha hab.symm hη hη4,
    hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
      false true u B hb ha hab.symm hη hη4,
    hughesYoungEquation84CompletePositiveMomentAt_eq_prefix_add_shiftTail
      true true u B hb ha hab.symm hη hη4]
  unfold hughesYoungEquation84NegativePrefixSourceLine
    hughesYoungEquation84NegativeShiftTailSourceLine
  ring

/-- Direct tail of the negative, coordinate-swapped contour-term series. -/
noncomputable def hughesYoungEquation84NegativeContourTermShiftTail
    (T t : ℝ) (h k a b : ℕ) (u B : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    if B < ((y.2 : ℕ) : ℝ) then
      hughesYoungEquation84NegativeContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
    else 0

/-- The `hughesYoungEquation84NegativeContourTermPrefix` definition used by the source-facing construction in `HughesYoungShiftTail`. -/
noncomputable def hughesYoungEquation84NegativeContourTermPrefix
    (T t : ℝ) (h k a b : ℕ) (u B : ℝ) : ℂ :=
  ∑' y : ℕ+ × ℕ+,
    if ((y.2 : ℕ) : ℝ) ≤ B then
      hughesYoungEquation84NegativeContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
    else 0

theorem hughesYoungEquation84CompleteNegativeSourceLine_eq_contourPrefix_add_tail
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u B : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84CompleteNegativeSourceLine T t h k a b u =
      hughesYoungEquation84NegativeContourTermPrefix T t h k a b u B +
        hughesYoungEquation84NegativeContourTermShiftTail T t h k a b u B := by
  have hs := summable_hughesYoungEquation84CompleteNegativeSourceLine
    T t h k ha hb hab u hη hη4
  have hp : Summable (fun y : ℕ+ × ℕ+ =>
      if ((y.2 : ℕ) : ℝ) ≤ B then
        hughesYoungEquation84NegativeContourTerm T t h k a b
          (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
      else 0) :=
    Summable.of_norm_bounded hs.norm fun y => by
      by_cases hy : ((y.2 : ℕ) : ℝ) ≤ B <;> simp [hy]
  have ht : Summable (fun y : ℕ+ × ℕ+ =>
      if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungEquation84NegativeContourTerm T t h k a b
          (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
      else 0) :=
    Summable.of_norm_bounded hs.norm fun y => by
      by_cases hy : B < ((y.2 : ℕ) : ℝ) <;> simp [hy]
  unfold hughesYoungEquation84CompleteNegativeSourceLine
    hughesYoungEquation84NegativeContourTermPrefix
    hughesYoungEquation84NegativeContourTermShiftTail
  rw [← hp.tsum_add ht]
  apply tsum_congr
  intro y
  by_cases hy : B < ((y.2 : ℕ) : ℝ)
  · rw [if_neg (not_le.mpr hy), if_pos hy]
    simp
  · rw [if_pos (not_lt.mp hy), if_neg hy]
    simp

theorem tsum_hughesYoungEquation84NegativeContourSeries_prefix_eq
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u B : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (∑' r : ℕ+,
      if ((r : ℕ) : ℝ) ≤ B then
        hughesYoungEquation84NegativeContourSeries T t h k a b r
          ((1 : ℂ) + (u : ℂ) * I)
      else 0) =
      hughesYoungEquation84NegativeContourTermPrefix T t h k a b u B := by
  let F : ℕ+ × ℕ+ → ℂ := fun y =>
    if ((y.2 : ℕ) : ℝ) ≤ B then
      hughesYoungEquation84NegativeContourTerm T t h k a b
        (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
    else 0
  have hFull := summable_hughesYoungEquation84CompleteNegativeSourceLine
    T t h k ha hb hab u hη hη4
  have hF : Summable F :=
    Summable.of_norm_bounded hFull.norm fun y => by
      by_cases hy : ((y.2 : ℕ) : ℝ) ≤ B <;> simp [F, hy]
  have hSwap : Summable (fun y : ℕ+ × ℕ+ => F y.swap) :=
    hF.comp_injective (Equiv.prodComm ℕ+ ℕ+).injective
  calc
    _ = ∑' r : ℕ+, ∑' q : ℕ+,
        if ((r : ℕ) : ℝ) ≤ B then
          hughesYoungEquation84NegativeContourTerm T t h k a b r q
            ((1 : ℂ) + (u : ℂ) * I)
        else 0 := by
      apply tsum_congr
      intro r
      by_cases hr : ((r : ℕ) : ℝ) ≤ B
      · rw [if_pos hr]
        simp_rw [if_pos hr]
        unfold hughesYoungEquation84NegativeContourSeries
        exact tsum_hughesYoungEquation84NegativeContourTerm_nat_eq_pnat
          T t h k a b r ((1 : ℂ) + (u : ℂ) * I)
      · rw [if_neg hr]
        simp_rw [if_neg hr]
        exact tsum_zero.symm
    _ = ∑' y : ℕ+ × ℕ+, F y.swap := hSwap.tsum_prod.symm
    _ = ∑' y : ℕ+ × ℕ+, F y :=
      (Equiv.prodComm ℕ+ ℕ+).tsum_eq F
    _ = _ := by rfl

theorem sum_hughesYoungEquation84NegativeContourSeries_Icc_eq_prefix
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u : ℝ) (L : ℕ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    (∑ r ∈ Finset.Icc 1 L,
      hughesYoungEquation84NegativeContourSeries T t h k a b r
        ((1 : ℂ) + (u : ℂ) * I)) =
      hughesYoungEquation84NegativeContourTermPrefix
        T t h k a b u (L : ℝ) := by
  rw [sum_Icc_one_eq_tsum_pnat_cutoff]
  rw [← tsum_hughesYoungEquation84NegativeContourSeries_prefix_eq
    T t h k ha hb hab u (L : ℝ) hη hη4]
  apply tsum_congr
  intro r
  have hr : (((r : ℕ) : ℝ) ≤ (L : ℝ)) ↔ (r : ℕ) ≤ L := by norm_cast
  by_cases hrl : (r : ℕ) ≤ L
  · simp [hrl, hr.mpr hrl]
  · have hreal : ¬(((r : ℕ) : ℝ) ≤ (L : ℝ)) := fun h => hrl (hr.mp h)
    simp [hrl, hreal]

theorem hughesYoungEquation84NegativeContourTermShiftTail_eq_sourceTail
    (T t : ℝ) (h k : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (u B : ℝ) {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    hughesYoungEquation84NegativeContourTermShiftTail T t h k a b u B =
      hughesYoungEquation84NegativeShiftTailSourceLine T t h k a b u B := by
  let P := hughesYoungEquation84CompleteNegativeOuter T t h k a b u
  let K00 := hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K10 := hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K01 := hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let K11 := hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)
  let f : Bool → Bool → (ℕ+ × ℕ+) → ℂ := fun i j y =>
    if B < ((y.2 : ℕ) : ℝ) then
      hughesYoungEquation84PositiveSourceArithmeticTerm b a i j u y
    else 0
  have hf (i j : Bool) : Summable (f i j) := by
    have hs := summable_hughesYoungEquation96VerticalShiftTailMoment
      i j u B hb ha hη hη4
    apply hs.congr
    intro y
    simp only [f]
    by_cases hy : B < ((y.2 : ℕ) : ℝ)
    · rw [if_pos hy, if_pos hy]
      unfold hughesYoungEquation84PositiveSourceArithmeticTerm
      exact (dfiEquation84PositiveMomentAtTerm_eq_equation96SelectorTerm
        i j u hab.symm y).symm
    · rw [if_neg hy, if_neg hy]
  unfold hughesYoungEquation84NegativeContourTermShiftTail
  rw [show (∑' y : ℕ+ × ℕ+,
      if B < ((y.2 : ℕ) : ℝ) then
        hughesYoungEquation84NegativeContourTerm T t h k a b
          (y.2 : ℕ) (y.1 : ℕ) ((1 : ℂ) + (u : ℂ) * I)
      else 0) =
      ∑' y : ℕ+ × ℕ+,
        P * (f false false y * K00 + f true false y * K10 +
          f false true y * K01 + f true true y * K11) by
    apply tsum_congr
    intro y
    by_cases hy : B < ((y.2 : ℕ) : ℝ)
    · rw [if_pos hy]
      simp only [f, hy, ↓reduceIte]
      simpa only [P, K00, K10, K01, K11] using
        hughesYoungEquation84NegativeSourceTerm_eq_fourTerms
          T t h k a b u y
    · rw [if_neg hy]
      simp [f, hy]]
  simp_rw [tsum_mul_left]
  rw [((((hf false false).mul_right K00).add
        ((hf true false).mul_right K10)).add
      ((hf false true).mul_right K01)).tsum_add
        ((hf true true).mul_right K11),
    (((hf false false).mul_right K00).add
      ((hf true false).mul_right K10)).tsum_add
        ((hf false true).mul_right K01),
    ((hf false false).mul_right K00).tsum_add
      ((hf true false).mul_right K10)]
  simp only [tsum_mul_right]
  rw [tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
      false false u B hab.symm,
    tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
      true false u B hab.symm,
    tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
      false true u B hab.symm,
    tsum_hughesYoungEquation84PositiveSourceArithmeticTail_eq_verticalTail
      true true u B hab.symm]
  rfl

theorem norm_hughesYoungEquation84NegativeShiftTailSourceLine_le
    (T t : ℝ) (h k : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (u : ℝ) {B : ℝ} (hB : 0 < B)
    {η : ℝ} (hη : 0 < η) (hη4 : η < 1 / 4) :
    ‖hughesYoungEquation84NegativeShiftTailSourceLine T t h k a b u B‖ ≤
      ‖hughesYoungEquation84CompleteNegativeOuter T t h k a b u‖ *
        hughesYoungEquation84ShiftTailArithmeticBound b a η B *
        (‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖) := by
  let D := hughesYoungEquation84ShiftTailArithmeticBound b a η B
  have h00 := norm_hughesYoungEquation96VerticalShiftTailMoment_le
    false false u hB hb ha hη hη4
  have h10 := norm_hughesYoungEquation96VerticalShiftTailMoment_le
    true false u hB hb ha hη hη4
  have h01 := norm_hughesYoungEquation96VerticalShiftTailMoment_le
    false true u hB hb ha hη hη4
  have h11 := norm_hughesYoungEquation96VerticalShiftTailMoment_le
    true true u hB hb ha hη hη4
  change ‖hughesYoungEquation96VerticalShiftTailMoment b a false false u B‖ ≤ D at h00
  change ‖hughesYoungEquation96VerticalShiftTailMoment b a true false u B‖ ≤ D at h10
  change ‖hughesYoungEquation96VerticalShiftTailMoment b a false true u B‖ ≤ D at h01
  change ‖hughesYoungEquation96VerticalShiftTailMoment b a true true u B‖ ≤ D at h11
  unfold hughesYoungEquation84NegativeShiftTailSourceLine
  rw [norm_mul, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _ ≤
        ‖hughesYoungEquation96VerticalShiftTailMoment b a false false u B‖ *
            ‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation96VerticalShiftTailMoment b a true false u B‖ *
            ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation96VerticalShiftTailMoment b a false true u B‖ *
            ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          ‖hughesYoungEquation96VerticalShiftTailMoment b a true true u B‖ *
            ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ := by
      calc
        _ ≤ ‖hughesYoungEquation96VerticalShiftTailMoment b a false false u B *
                hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I) +
              hughesYoungEquation96VerticalShiftTailMoment b a true false u B *
                hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I) +
              hughesYoungEquation96VerticalShiftTailMoment b a false true u B *
                hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
              ‖hughesYoungEquation96VerticalShiftTailMoment b a true true u B *
                hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ :=
            norm_add_le _ _
        _ ≤ (‖hughesYoungEquation96VerticalShiftTailMoment b a false false u B *
                hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I) +
              hughesYoungEquation96VerticalShiftTailMoment b a true false u B *
                hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
              ‖hughesYoungEquation96VerticalShiftTailMoment b a false true u B *
                hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖) +
              ‖hughesYoungEquation96VerticalShiftTailMoment b a true true u B *
                hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ := by
            gcongr
            exact norm_add_le _ _
        _ ≤ ((‖hughesYoungEquation96VerticalShiftTailMoment b a false false u B *
                hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
              ‖hughesYoungEquation96VerticalShiftTailMoment b a true false u B *
                hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖) +
              ‖hughesYoungEquation96VerticalShiftTailMoment b a false true u B *
                hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖) +
              ‖hughesYoungEquation96VerticalShiftTailMoment b a true true u B *
                hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ := by
            gcongr
            exact norm_add_le _ _
        _ = _ := by simp only [norm_mul]
    _ ≤ D * ‖hughesYoungEquation84Kernel00 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          D * ‖hughesYoungEquation84Kernel10 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          D * ‖hughesYoungEquation84Kernel01 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ +
          D * ‖hughesYoungEquation84Kernel11 (-t) ((1 : ℂ) + (u : ℂ) * I)‖ := by
      gcongr
    _ = _ := by
      dsimp only [D]
      ring

end RiemannZeta.GuthMaynard
