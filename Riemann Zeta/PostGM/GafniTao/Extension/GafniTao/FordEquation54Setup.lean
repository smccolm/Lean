import GafniTao.FordLemma51Equation53
import GafniTao.FordTentSeries

/-!
# Ford Lemma 5.1: the sinc-square majorant before equation (5.4)

This file inserts Ford's literal coordinate weights

`f_j(c_j) = (r M^j sin (pi c_j / (2 r M^j)) / c_j)^2`

into the oscillatory moment `T`.  The argument uses the fact that every
power-vector coordinate in the representation fiber lies in
`[r, r M^j]`.  No infinite Fourier sum or support truncation is used here;
those are the next, logically separate, steps in equation (5.4).
-/

open Finset
open scoped BigOperators NNReal

namespace GafniTao

noncomputable section

/-- Ford's nonnegative sinc-square weight in degree `j+1`, bundled as an
`NNReal` so the pointwise majorization can be summed without coercion noise. -/
def fordLemma51CoordinateWeight
    (k r M : ℕ) (j : Fin k) (c : Fin k → ℤ) : ℝ≥0 :=
  ⟨fordSincSquareWeight r M ((j : ℕ) + 1) (c j : ℝ),
    fordSincSquareWeight_nonneg r M ((j : ℕ) + 1) (c j : ℝ)⟩

/-- Product of all `k` coordinate weights used between (5.3) and (5.4). -/
def fordLemma51WeightProduct
    (k r M : ℕ) (c : Fin k → ℤ) : ℝ≥0 :=
  ∏ j : Fin k, fordLemma51CoordinateWeight k r M j c

theorem one_le_fordLemma51CoordinateWeight
    {r M k : ℕ} (hr : 0 < r) (hM : 0 < M)
    {c : Fin k → ℤ} (hc : c ∈ fordLemma51FiberSet r k M) (j : Fin k) :
    1 ≤ fordLemma51CoordinateWeight k r M j c := by
  rcases Finset.mem_image.mp hc with ⟨x, _hx, rfl⟩
  apply (NNReal.coe_le_coe).mp
  simp only [fordLemma51CoordinateWeight, NNReal.coe_one]
  have hbounds := fordVinogradovPowerVector_bounds x j
  apply one_le_fordSincSquareWeight hr hM
  · have hrOne : (1 : ℤ) ≤ r := by exact_mod_cast hr
    exact_mod_cast hrOne.trans hbounds.1
  · exact_mod_cast hbounds.2

theorem one_le_fordLemma51WeightProduct
    {r M k : ℕ} (hr : 0 < r) (hM : 0 < M)
    {c : Fin k → ℤ} (hc : c ∈ fordLemma51FiberSet r k M) :
    1 ≤ fordLemma51WeightProduct k r M c := by
  unfold fordLemma51WeightProduct
  exact Finset.one_le_prod fun j _hj =>
    one_le_fordLemma51CoordinateWeight hr hM hc j

/-- The first inequality after Ford's definition of `f_j`: the finite moment
`T` is bounded by the same finite sum with the complete product of literal
sinc-square weights inserted. -/
theorem fordLemma51MomentT_le_weightedFiberMoment
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    fordLemma51MomentT k M r s B t z ≤
      ∑ c ∈ fordLemma51FiberSet r k M,
        fordLemma51WeightProduct k r M c *
          ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) := by
  unfold fordLemma51MomentT
  apply Finset.sum_le_sum
  intro c hc
  calc
    ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) =
        1 * ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) := by
      rw [one_mul]
    _ ≤ fordLemma51WeightProduct k r M c *
          ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) := by
      gcongr
      exact one_le_fordLemma51WeightProduct hr hM hc

/-- Absolute summability of one of Ford's sinc-square coordinate weights.
This is derived from the exact tent Fourier coefficient, including the
removable zero-frequency value. -/
theorem summable_fordLemma51CoordinateWeight
    {r M j : ℕ} (hr : 0 < r) (hM : 0 < M) :
    Summable (fun n : ℤ =>
      (⟨fordSincSquareWeight r M j (n : ℝ),
        fordSincSquareWeight_nonneg r M j (n : ℝ)⟩ : ℝ≥0)) := by
  let A : ℝ := ((r * M ^ j : ℕ) : ℝ)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hw : 0 < 1 / (2 * A) := by positivity
  have hcoeff := summable_fordTentFourierCoefficient hw
  have hscaled := hcoeff.mul_left (((Real.pi ^ 2 * A / 2 : ℝ) : ℂ))
  have hcomplex : Summable (fun n : ℤ =>
      (fordSincSquareWeight r M j (n : ℝ) : ℂ)) := by
    apply hscaled.congr
    intro n
    rw [fordSincSquareWeight_eq_tentCoefficient hr hM]
  have hreal : Summable (fun n : ℤ =>
      fordSincSquareWeight r M j (n : ℝ)) := by
    have hnorm := hcomplex.norm
    convert hnorm using 1
    funext n
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fordSincSquareWeight_nonneg r M j (n : ℝ))]
  exact NNReal.summable_coe.mp hreal

/-- A finite Cartesian product of nonnegative summable families is
summable.  This is the exact Fubini lemma needed for Ford's `k` coordinate
lattice; it is stated independently because the coordinate functions depend
on their degree. -/
theorem summable_fin_pi_prod_nnnreal
    (k : ℕ) (f : (j : Fin k) → ℤ → ℝ≥0)
    (hf : ∀ j, Summable (f j)) :
    Summable (fun c : Fin k → ℤ => ∏ j : Fin k, f j (c j)) := by
  induction k with
  | zero => exact (hasSum_fintype _).summable
  | succ k ih =>
      let f0 : (j : Fin k) → ℤ → ℝ≥0 := fun j => f j.castSucc
      have h0 : Summable (fun c : Fin k → ℤ => ∏ j : Fin k, f0 j (c j)) :=
        ih f0 (fun j => hf j.castSucc)
      have hlast : Summable (f (Fin.last k)) := hf (Fin.last k)
      have h0R : Summable (fun c : Fin k → ℤ =>
          ((∏ j : Fin k, f0 j (c j) : ℝ≥0) : ℝ)) :=
        NNReal.summable_coe.mpr h0
      have hlastR : Summable (fun n : ℤ =>
          ((f (Fin.last k) n : ℝ≥0) : ℝ)) :=
        NNReal.summable_coe.mpr hlast
      have hprodR : Summable (fun p : (Fin k → ℤ) × ℤ =>
          ((∏ j : Fin k, f0 j (p.1 j) : ℝ≥0) : ℝ) *
            ((f (Fin.last k) p.2 : ℝ≥0) : ℝ)) :=
        h0R.mul_of_nonneg hlastR (fun _ => by positivity) (fun _ => by positivity)
      have hprod : Summable (fun p : (Fin k → ℤ) × ℤ =>
          (∏ j : Fin k, f0 j (p.1 j)) * f (Fin.last k) p.2) :=
        NNReal.summable_coe.mp (by simpa using hprodR)
      apply ((Fin.succFunEquiv ℤ k).symm.summable_iff).mp
      convert hprod using 1
      funext p
      simp only [Function.comp_apply]
      rw [Fin.prod_univ_castSucc]
      congr 1
      · apply Finset.prod_congr rfl
        intro j _hj
        change f j.castSucc
            (Fin.append p.1 (fun _ : Fin 1 => p.2) (Fin.castAdd 1 j)) =
          f j.castSucc (p.1 j)
        rw [Fin.append_left]
      · have hlastEq : Fin.last k = Fin.natAdd k (0 : Fin 1) := by
          ext
          simp
        rw [hlastEq]
        change f (Fin.natAdd k 0)
            (Fin.append p.1 (fun _ : Fin 1 => p.2) (Fin.natAdd k 0)) =
          f (Fin.natAdd k 0) p.2
        rw [Fin.append_right]

theorem summable_fordLemma51WeightProduct
    {r M k : ℕ} (hr : 0 < r) (hM : 0 < M) :
    Summable (fordLemma51WeightProduct k r M) := by
  unfold fordLemma51WeightProduct fordLemma51CoordinateWeight
  exact summable_fin_pi_prod_nnnreal k
    (fun j n =>
      ⟨fordSincSquareWeight r M ((j : ℕ) + 1) (n : ℝ),
        fordSincSquareWeight_nonneg r M ((j : ℕ) + 1) (n : ℝ)⟩)
    (fun j => summable_fordLemma51CoordinateWeight hr hM)

theorem fordLemma51FiberOscillatorySum_nnnorm_le_card
    (k M r : ℕ) (B : Finset ℕ) (t z : ℝ) (c : Fin k → ℤ) :
    ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ≤ B.card := by
  unfold fordLemma51FiberOscillatorySum
  calc
    ‖∑ b ∈ B,
        fordLemma51Epsilon k M r t z b *
          fordAdditiveCharacter (fordLemma51FiberPhase k t z b c)‖₊ ≤
        ∑ b ∈ B,
          ‖fordLemma51Epsilon k M r t z b *
            fordAdditiveCharacter (fordLemma51FiberPhase k t z b c)‖₊ :=
      nnnorm_sum_le B _
    _ = ∑ _b ∈ B, (1 : ℝ≥0) := by
      apply Finset.sum_congr rfl
      intro b _hb
      apply NNReal.eq
      rw [NNReal.coe_one, coe_nnnorm, norm_mul,
        norm_fordLemma51Epsilon, one_mul]
      unfold fordAdditiveCharacter
      rw [Complex.norm_exp]
      simp
    _ = B.card := by simp

/-- The all-lattice weighted moment is summable.  This is the convergence
fact that justifies the infinite sum and all subsequent rearrangements in
Ford's derivation of (5.4). -/
theorem summable_fordLemma51WeightedLatticeMoment
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    Summable (fun c : Fin k → ℤ =>
      fordLemma51WeightProduct k r M c *
        ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s)) := by
  have hw := summable_fordLemma51WeightProduct (k := k) hr hM
  have hwR : Summable (fun c : Fin k → ℤ =>
      (fordLemma51WeightProduct k r M c : ℝ)) := NNReal.summable_coe.mpr hw
  have hmajor : Summable (fun c : Fin k → ℤ =>
      (fordLemma51WeightProduct k r M c : ℝ) *
        ((B.card : ℝ≥0) ^ (2 * s) : ℝ)) :=
    hwR.mul_right (((B.card : ℝ≥0) ^ (2 * s) : ℝ))
  refine NNReal.summable_coe.mp (Summable.of_nonneg_of_le
    (f := fun c : Fin k → ℤ =>
      (fordLemma51WeightProduct k r M c : ℝ) *
        ((B.card : ℝ≥0) ^ (2 * s) : ℝ))
    (g := fun c : Fin k → ℤ =>
      ((fordLemma51WeightProduct k r M c *
        ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) : ℝ≥0) : ℝ))
    (fun _ => by positivity) ?_ hmajor)
  intro c
  push_cast
  gcongr
  exact fordLemma51FiberOscillatorySum_nnnorm_le_card k M r B t z c

/-- The finite power-vector sum is dominated by the convergent all-integer
lattice sum, exactly as in the first displayed line after the definition of
Ford's `f_j`. -/
theorem fordLemma51MomentT_le_weightedLatticeMoment
    {k M r s : ℕ} (hr : 0 < r) (hM : 0 < M)
    (B : Finset ℕ) (t z : ℝ) :
    fordLemma51MomentT k M r s B t z ≤
      ∑' c : Fin k → ℤ,
        fordLemma51WeightProduct k r M c *
          ‖fordLemma51FiberOscillatorySum k M r B t z c‖₊ ^ (2 * s) := by
  refine (fordLemma51MomentT_le_weightedFiberMoment hr hM B t z).trans ?_
  exact (summable_fordLemma51WeightedLatticeMoment hr hM B t z).sum_le_tsum
    (fordLemma51FiberSet r k M) (fun _ _ => bot_le)

#print axioms one_le_fordLemma51CoordinateWeight
#print axioms one_le_fordLemma51WeightProduct
#print axioms fordLemma51MomentT_le_weightedFiberMoment
#print axioms summable_fordLemma51CoordinateWeight
#print axioms summable_fin_pi_prod_nnnreal
#print axioms summable_fordLemma51WeightProduct
#print axioms fordLemma51FiberOscillatorySum_nnnorm_le_card
#print axioms summable_fordLemma51WeightedLatticeMoment
#print axioms fordLemma51MomentT_le_weightedLatticeMoment

end

end GafniTao
