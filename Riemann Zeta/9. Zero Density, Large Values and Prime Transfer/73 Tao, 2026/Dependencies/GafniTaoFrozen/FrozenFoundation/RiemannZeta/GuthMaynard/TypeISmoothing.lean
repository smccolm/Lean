import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import RiemannZeta.GuthMaynard.ClassicalDichotomy

open Complex Finset Set
open scoped BigOperators ContDiff

namespace RiemannZeta.GuthMaynard

/-!
# Source-faithful smoothing for the classical Type-I tail

The cutoff below is the literal telescoping smooth partition used in the
Type-I part of ANTEDB Lemma 11.5.  It is fixed independently of the ordinate,
nonnegative, smooth, and supported in `[1 / 2, 2]`.  Summing its dyadic
rescalings is exactly one on the finite tail `(Y,A]`; no sharp block is
silently substituted for the smooth source block.
-/

/-- A decreasing smooth step which is one on `(-∞,1]` and zero on `[2,∞)`. -/
noncomputable def typeISmoothStep (x : ℝ) : ℝ :=
  Real.smoothTransition (2 - x)

/-- The fixed annular cutoff `η(x)-η(2x)` used in the dyadic partition. -/
noncomputable def typeIDyadicCutoff (x : ℝ) : ℝ :=
  typeISmoothStep x - typeISmoothStep (2 * x)

theorem contDiff_typeIDyadicCutoff : ContDiff ℝ ∞ typeIDyadicCutoff := by
  unfold typeIDyadicCutoff typeISmoothStep
  have hinner₁ : ContDiff ℝ ∞ (fun x : ℝ => (2 : ℝ) - x) := by fun_prop
  have hinner₂ : ContDiff ℝ ∞ (fun x : ℝ => (2 : ℝ) - 2 * x) := by fun_prop
  have h₁ : ContDiff ℝ ∞ (fun x : ℝ =>
      Real.smoothTransition ((2 : ℝ) - x)) := by
    simpa only [Function.comp_apply] using
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hinner₁
  have h₂ : ContDiff ℝ ∞ (fun x : ℝ =>
      Real.smoothTransition ((2 : ℝ) - 2 * x)) := by
    simpa only [Function.comp_apply] using
      (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp hinner₂
  exact h₁.sub h₂

theorem typeISmoothStep_eq_one {x : ℝ} (hx : x ≤ 1) :
    typeISmoothStep x = 1 := by
  unfold typeISmoothStep
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem typeISmoothStep_eq_zero {x : ℝ} (hx : 2 ≤ x) :
    typeISmoothStep x = 0 := by
  unfold typeISmoothStep
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem typeIDyadicCutoff_nonneg (x : ℝ) : 0 ≤ typeIDyadicCutoff x := by
  unfold typeIDyadicCutoff
  by_cases hx : 0 ≤ x
  · exact sub_nonneg.mpr
      (show Real.smoothTransition (2 - 2 * x) ≤
          Real.smoothTransition (2 - x) from
        Real.smoothTransition.monotone (by linarith))
  · rw [typeISmoothStep_eq_one (by linarith),
      typeISmoothStep_eq_one (by linarith)]
    norm_num

theorem typeIDyadicCutoff_le_one (x : ℝ) : typeIDyadicCutoff x ≤ 1 := by
  unfold typeIDyadicCutoff
  have hnonneg : 0 ≤ typeISmoothStep (2 * x) := by
    unfold typeISmoothStep
    exact Real.smoothTransition.nonneg _
  have hle : typeISmoothStep x ≤ 1 := by
    unfold typeISmoothStep
    exact Real.smoothTransition.le_one _
  linarith

theorem typeIDyadicCutoff_eq_zero_of_le_half {x : ℝ} (hx : x ≤ 1 / 2) :
    typeIDyadicCutoff x = 0 := by
  rw [typeIDyadicCutoff, typeISmoothStep_eq_one (by linarith),
    typeISmoothStep_eq_one (by linarith)]
  norm_num

theorem typeIDyadicCutoff_eq_zero_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    typeIDyadicCutoff x = 0 := by
  rw [typeIDyadicCutoff, typeISmoothStep_eq_zero hx,
    typeISmoothStep_eq_zero (by linarith)]
  norm_num

/-- Smooth boundary cutoff which is exactly the indicator of `(Y,A]` at
integer arguments.  Its unit-width transition zones remove the two sharp
edges before Poisson summation. -/
noncomputable def typeITailBoundary (Y A : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (x - (Y : ℝ)) *
    Real.smoothTransition (((A + 1 : ℕ) : ℝ) - x)

theorem contDiff_typeITailBoundary (Y A : ℕ) :
    ContDiff ℝ ∞ (typeITailBoundary Y A) := by
  unfold typeITailBoundary
  have hleft : ContDiff ℝ ∞ (fun x : ℝ =>
      Real.smoothTransition (x - (Y : ℝ))) := by fun_prop
  have hright : ContDiff ℝ ∞ (fun x : ℝ =>
      Real.smoothTransition (((A + 1 : ℕ) : ℝ) - x)) := by fun_prop
  exact hleft.mul hright

theorem typeITailBoundary_natCast (Y A n : ℕ) :
    typeITailBoundary Y A n = if n ∈ Finset.Ioc Y A then 1 else 0 := by
  by_cases hn : n ∈ Finset.Ioc Y A
  · rw [if_pos hn]
    have hnData := Finset.mem_Ioc.mp hn
    have hnLowerR : (Y : ℝ) < n := by exact_mod_cast hnData.1
    have hnUpperR : (n : ℝ) ≤ A := by exact_mod_cast hnData.2
    have hnGapR : ((Y + 1 : ℕ) : ℝ) ≤ n := by
      exact_mod_cast (Nat.succ_le_iff.mpr hnData.1)
    unfold typeITailBoundary
    rw [Real.smoothTransition.one_of_one_le (by push_cast at hnGapR; linarith),
      Real.smoothTransition.one_of_one_le (by push_cast; linarith)]
    norm_num
  · rw [if_neg hn]
    rw [Finset.mem_Ioc, not_and_or] at hn
    rcases hn with hn | hn
    · have hnR : (n : ℝ) ≤ Y := by exact_mod_cast (le_of_not_gt hn)
      unfold typeITailBoundary
      rw [Real.smoothTransition.zero_of_nonpos (by linarith)]
      norm_num
    · have hnR : (A : ℝ) < n := by exact_mod_cast (lt_of_not_ge hn)
      have hnGapR : ((A + 1 : ℕ) : ℝ) ≤ n := by
        exact_mod_cast (Nat.succ_le_iff.mpr (lt_of_not_ge hn))
      have hright : Real.smoothTransition
          (((A + 1 : ℕ) : ℝ) - (n : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      unfold typeITailBoundary
      rw [hright, mul_zero]

/-- The complete fixed smooth weight of the `r`-th source block. -/
noncomputable def typeISourceSmoothWeight (Y A r : ℕ) (x : ℝ) : ℝ :=
  typeITailBoundary Y A x *
    typeIDyadicCutoff (x / (2 ^ r * Y : ℕ))

theorem contDiff_typeISourceSmoothWeight (Y A r : ℕ) :
    ContDiff ℝ ∞ (typeISourceSmoothWeight Y A r) := by
  unfold typeISourceSmoothWeight
  exact (contDiff_typeITailBoundary Y A).mul
    (contDiff_typeIDyadicCutoff.comp
      (contDiff_id.div_const ((2 ^ r * Y : ℕ) : ℝ)))

/-- Globally smooth source block; the finite index set only records a known
compact carrier and does not create an analytic edge because the boundary
weight already vanishes at its endpoints. -/
noncomputable def typeISourceSmoothBlock
    (Y A r : ℕ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (A + 1),
    typeISourceSmoothWeight Y A r n *
      (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)

/-- The `r`-th smooth Type-I block on the scale `2^r Y`. -/
noncomputable def typeISmoothBlock (Y r : ℕ) (σ t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc Y (2 ^ (r + 1) * Y),
    typeIDyadicCutoff ((n : ℝ) / (2 ^ r * Y : ℕ)) *
      (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I)

/-- Algebraic telescoping of the smooth dyadic weights. -/
theorem sum_typeIDyadicCutoff_eq
    (k : ℕ) (x : ℝ) :
    (∑ r ∈ Finset.range (k + 1),
        typeIDyadicCutoff (x / (2 ^ r : ℕ))) =
      typeISmoothStep (x / (2 ^ k : ℕ)) - typeISmoothStep (2 * x) := by
  induction k with
  | zero => simp [typeIDyadicCutoff]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [typeIDyadicCutoff]
      have hpow : ((2 ^ (k + 1) : ℕ) : ℝ) =
          2 * ((2 ^ k : ℕ) : ℝ) := by
        push_cast
        rw [pow_succ]
        ring
      have harg : 2 * (x / ((2 ^ (k + 1) : ℕ) : ℝ)) =
          x / ((2 ^ k : ℕ) : ℝ) := by
        rw [hpow]
        have hk : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
        field_simp [hk.ne']
      rw [harg]
      ring

/-- On the exact tail range, the finite smooth partition sums to one. -/
theorem sum_typeIDyadicCutoff_eq_one
    {Y A n k : ℕ} (hY : 1 ≤ Y) (hn : n ∈ Finset.Ioc Y A)
    (hA : A ≤ 2 ^ k * Y) :
    (∑ r ∈ Finset.range (k + 1),
        typeIDyadicCutoff ((n : ℝ) / (2 ^ r * Y : ℕ))) = 1 := by
  have hYpos : 0 < Y := lt_of_lt_of_le Nat.zero_lt_one hY
  have hscalePos : 0 < 2 ^ k * Y := Nat.mul_pos (pow_pos (by omega) _) hYpos
  have hupper : (n : ℝ) / (2 ^ k * Y : ℕ) ≤ 1 := by
    rw [div_le_one (by exact_mod_cast hscalePos)]
    exact_mod_cast (Finset.mem_Ioc.mp hn).2.trans hA
  have hlower : 2 ≤ 2 * ((n : ℝ) / Y) := by
    have hdiv : 1 < (n : ℝ) / Y := by
      rw [one_lt_div (by exact_mod_cast hYpos)]
      exact_mod_cast (Finset.mem_Ioc.mp hn).1
    linarith
  have hupper' : ((n : ℝ) / Y) / (2 ^ k : ℕ) ≤ 1 := by
    calc
      ((n : ℝ) / Y) / (2 ^ k : ℕ) =
          (n : ℝ) / (2 ^ k * Y : ℕ) := by
            push_cast
            field_simp
      _ ≤ 1 := hupper
  rw [show (∑ r ∈ Finset.range (k + 1),
        typeIDyadicCutoff ((n : ℝ) / (2 ^ r * Y : ℕ))) =
      ∑ r ∈ Finset.range (k + 1),
        typeIDyadicCutoff (((n : ℝ) / Y) / (2 ^ r : ℕ)) by
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      push_cast
      field_simp]
  rw [sum_typeIDyadicCutoff_eq, typeISmoothStep_eq_one hupper',
    typeISmoothStep_eq_zero hlower]
  norm_num

/-- Exact smooth decomposition of the fixed-line Type-I tail. -/
theorem classicalZetaLongTail_eq_sum_smoothBlocks
    (Y A k : ℕ) (σ t : ℝ) (hY : 1 ≤ Y) (hA : A ≤ 2 ^ k * Y) :
    classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ)) =
      ∑ r ∈ Finset.range (k + 1),
        ∑ n ∈ Finset.Ioc Y A,
          typeIDyadicCutoff ((n : ℝ) / (2 ^ r * Y : ℕ)) *
            (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
  rw [classicalZetaLongTail]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  have hnNatPos : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le Y) (Finset.mem_Ioc.mp hn).1
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnNatPos.ne'
  have hweights :
      (∑ r ∈ Finset.range (k + 1),
        (typeIDyadicCutoff ((n : ℝ) / (2 ^ r * Y : ℕ)) : ℂ)) = 1 := by
    exact_mod_cast sum_typeIDyadicCutoff_eq_one hY hn hA
  calc
    (n : ℂ) ^ (-((σ : ℂ) + I * (t : ℂ))) =
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
          rw [show -((σ : ℂ) + I * (t : ℂ)) =
              -(σ : ℂ) + (-(t : ℂ) * I) by ring,
            Complex.cpow_add _ _ hnNe]
    _ = (∑ r ∈ Finset.range (k + 1),
          (typeIDyadicCutoff ((n : ℝ) / (2 ^ r * Y : ℕ)) : ℂ)) *
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
          rw [hweights, one_mul]
    _ = ∑ r ∈ Finset.range (k + 1),
          typeIDyadicCutoff ((n : ℝ) / (2 ^ r * Y : ℕ)) *
            (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
          rw [Finset.sum_mul, Finset.sum_mul]

theorem typeISourceSmoothBlock_eq_restricted
    (Y A r : ℕ) (σ t : ℝ) :
    typeISourceSmoothBlock Y A r σ t =
      ∑ n ∈ Finset.Ioc Y A,
        typeIDyadicCutoff ((n : ℝ) / (2 ^ r * Y : ℕ)) *
          (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
  unfold typeISourceSmoothBlock
  have hsubset : Finset.Ioc Y A ⊆ Finset.Icc 1 (A + 1) := by
    intro n hn
    have hnData := Finset.mem_Ioc.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  rw [← Finset.sum_subset hsubset]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [typeISourceSmoothWeight, typeITailBoundary_natCast,
      if_pos hn, one_mul]
  · intro n hnBig hnSmall
    rw [typeISourceSmoothWeight, typeITailBoundary_natCast,
      if_neg hnSmall]
    norm_num

/-- Exact decomposition into globally smooth source blocks. -/
theorem classicalZetaLongTail_eq_sum_sourceSmoothBlocks
    (Y A k : ℕ) (σ t : ℝ) (hY : 1 ≤ Y) (hA : A ≤ 2 ^ k * Y) :
    classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ)) =
      ∑ r ∈ Finset.range (k + 1),
        typeISourceSmoothBlock Y A r σ t := by
  rw [classicalZetaLongTail_eq_sum_smoothBlocks Y A k σ t hY hA]
  apply Finset.sum_congr rfl
  intro r _
  rw [typeISourceSmoothBlock_eq_restricted]

/-- Pointwise smooth-block extraction with the exact logarithmic loss. -/
theorem exists_typeISmoothBlock_large
    (Y A k : ℕ) (σ t V : ℝ) (hY : 1 ≤ Y) (hk : 0 < k + 1)
    (hA : A ≤ 2 ^ k * Y)
    (hLarge : V ≤
      ‖classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ))‖) :
    ∃ r ∈ Finset.range (k + 1),
      V / ((k + 1 : ℕ) : ℝ) ≤
        ‖typeISourceSmoothBlock Y A r σ t‖ := by
  let block : ℕ → ℂ := fun r => typeISourceSmoothBlock Y A r σ t
  have hsum : V ≤ ∑ r ∈ Finset.range (k + 1), ‖block r‖ := by
    calc
      V ≤ ‖classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ))‖ := hLarge
      _ = ‖∑ r ∈ Finset.range (k + 1), block r‖ := by
        rw [classicalZetaLongTail_eq_sum_sourceSmoothBlocks Y A k σ t hY hA]
      _ ≤ ∑ r ∈ Finset.range (k + 1), ‖block r‖ := norm_sum_le _ _
  obtain ⟨r, hr, hrLarge⟩ := pigeonhole_real_sum (k + 1)
    (fun r => ‖block r‖) V hsum hk
  refine ⟨r, hr, ?_⟩
  simpa only [block, Nat.cast_add, Nat.cast_one] using hrLarge

/-- A single smooth scale can be selected for a separated finite family of
Type-I ordinates.  The selected subfamily remains separated, every ordinate
has the same source cutoff and scale, and the discarded-cardinality loss is
exactly the number of available smooth blocks. -/
theorem exists_common_typeISmoothBlock_large
    (Y A k : ℕ) (σ V : ℝ) (W : Finset ℝ)
    (hY : 1 ≤ Y) (hA : A ≤ 2 ^ k * Y) (hW : W.Nonempty)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖classicalZetaLongTail Y A ((σ : ℂ) + I * (t : ℂ))‖) :
    ∃ r ∈ Finset.range (k + 1), ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      (∀ t ∈ W',
        V / ((k + 1 : ℕ) : ℝ) ≤
          ‖typeISourceSmoothBlock Y A r σ t‖) ∧
      W.card ≤ (k + 1) * W'.card := by
  classical
  have hk : 0 < k + 1 := by omega
  have hEach : ∀ t ∈ W, ∃ r ∈ Finset.range (k + 1),
      V / ((k + 1 : ℕ) : ℝ) ≤
        ‖typeISourceSmoothBlock Y A r σ t‖ := by
    intro t ht
    exact exists_typeISmoothBlock_large Y A k σ t V hY hk hA (hLarge t ht)
  let scale : ℝ → ℕ := fun t =>
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hScale : ∀ t ∈ W, scale t ∈ Finset.range (k + 1) := by
    intro t ht
    simp only [scale, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).1
  obtain ⟨r, hr, hcard⟩ := weighted_finite_pigeonhole W
    (Finset.range (k + 1)) (fun _ => 1) scale hW hScale
  let W' := W.filter (fun t => scale t = r)
  have hW'Separated : IsSeparated 1 W' := by
    intro x hx y hy hxy
    exact hSeparated x (Finset.filter_subset _ _ hx)
      y (Finset.filter_subset _ _ hy) hxy
  refine ⟨r, hr, W', Finset.filter_subset _ _, hW'Separated, ?_, ?_⟩
  · intro t ht
    have htData := Finset.mem_filter.mp ht
    have hchosen := (Classical.choose_spec (hEach t htData.1)).2
    have hscaleEq : Classical.choose (hEach t htData.1) = r := by
      simpa only [scale, dif_pos htData.1] using htData.2
    simpa only [hscaleEq] using hchosen
  · simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_range, W'] using hcard

end RiemannZeta.GuthMaynard
