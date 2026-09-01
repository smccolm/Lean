import GafniTao.FordZeroRepresentation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Ford's complete Vinogradov system

This file formalizes the finite counting side of equations (1.3)--(1.5) in
Ford's source.  A coordinate of `FordVinogradovTuple s Q` represents the
source integer `x_i` by the value `x_i.val + 1`, so its literal range is
`1 ≤ x_i ≤ Q`.  The power-vector has coordinates of degrees `1, ..., k`.

The normalized-Haar orthogonality calculation below proves the integral
identity (1.3).  Equation (1.4), shifted domination, and both lower-bound
terms in (1.5) are then proved from the same exact finite count.
-/

open Finset
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace GafniTao

noncomputable section

/-- The `s` source variables, each ranging over the integers `1, ..., Q`. -/
abbrev FordVinogradovTuple (s Q : ℕ) := Fin s → Fin Q

/-- The vector `(∑ᵢ xᵢ, ..., ∑ᵢ xᵢ^k)` attached to a source tuple. -/
def fordVinogradovPowerVector (s k Q : ℕ) (x : FordVinogradovTuple s Q) :
    Fin k → ℤ :=
  fun j => ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ ((j : ℕ) + 1)

/-- Ford's shifted solution count `J_{s,k}(P; h)` with `Q = floor P`. -/
def fordVinogradovShiftedCountNat
    (s k Q : ℕ) (h : Fin k → ℤ) : ℕ :=
  fordRepresentationCount (Finset.univ : Finset (FordVinogradovTuple s Q))
    (fordVinogradovPowerVector s k Q) h

/-- The combinatorial form (1.4) of Ford's complete Vinogradov mean value. -/
def fordVinogradovMomentNat (s k Q : ℕ) : ℕ :=
  fordVinogradovShiftedCountNat s k Q 0

/-- The source real-parameter convention, whose integer range ends at
`Q = floor P`. -/
def fordVinogradovMoment (s k : ℕ) (P : ℝ) : ℕ :=
  fordVinogradovMomentNat s k ⌊P⌋₊

/-- Ford's conventional abbreviation `k(k+1)/2`. -/
def fordVinogradovKappa (k : ℕ) : ℕ := k * (k + 1) / 2

/-- The first lower-bound term in (1.5), written without a negative natural
power: `(2s)⁻ᵏ Q^(2s-kappa)`. -/
def fordVinogradovLowerTerm (s k Q : ℕ) : ℝ :=
  (((2 * s : ℕ) : ℝ)⁻¹) ^ k *
    (Q : ℝ) ^ (2 * s - fordVinogradovKappa k)

/-- The exact source radius `s (Q^(j+1) - 1)` for the degree-`j+1`
displacement. -/
def fordVinogradovDisplacementRadius {k : ℕ} (s Q : ℕ) (j : Fin k) : ℕ :=
  s * (Q ^ ((j : ℕ) + 1) - 1)

/-- The finite displacement box used in Ford's count preceding (1.5). -/
def fordVinogradovDisplacementBox (s k Q : ℕ) :
    Finset (Fin k → ℤ) :=
  Fintype.piFinset fun j =>
    Finset.Icc (-((fordVinogradovDisplacementRadius s Q j : ℕ) : ℤ))
      ((fordVinogradovDisplacementRadius s Q j : ℕ) : ℤ)

theorem card_fordVinogradovTuple_univ (s Q : ℕ) :
    (Finset.univ : Finset (FordVinogradovTuple s Q)).card = Q ^ s := by
  simp [FordVinogradovTuple]

theorem fordVinogradovPowerVector_bounds
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) (j : Fin k) :
    (s : ℤ) ≤ fordVinogradovPowerVector s k Q x j ∧
      fordVinogradovPowerVector s k Q x j ≤
        (s : ℤ) * (Q : ℤ) ^ ((j : ℕ) + 1) := by
  let d : ℕ := (j : ℕ) + 1
  have htermLower (i : Fin s) :
      (1 : ℤ) ≤ ((x i : ℕ) + 1 : ℤ) ^ d := by
    apply one_le_pow₀
    omega
  have htermUpper (i : Fin s) :
      ((x i : ℕ) + 1 : ℤ) ^ d ≤ (Q : ℤ) ^ d := by
    have hbase : (x i : ℕ) + 1 ≤ Q := Nat.succ_le_iff.mpr (x i).isLt
    have hpow : ((x i : ℕ) + 1) ^ d ≤ Q ^ d := Nat.pow_le_pow_left hbase d
    exact_mod_cast hpow
  constructor
  · change (s : ℤ) ≤ ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d
    calc
      (s : ℤ) = ∑ _i : Fin s, (1 : ℤ) := by simp
      _ ≤ ∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d :=
        Finset.sum_le_sum fun i _hi => htermLower i
  · change (∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d) ≤
      (s : ℤ) * (Q : ℤ) ^ d
    calc
      (∑ i : Fin s, ((x i : ℕ) + 1 : ℤ) ^ d) ≤
          ∑ _i : Fin s, (Q : ℤ) ^ d :=
        Finset.sum_le_sum fun i _hi => htermUpper i
      _ = (s : ℤ) * (Q : ℤ) ^ d := by simp

theorem fordVinogradovPowerVector_sub_mem_box
    {s k Q : ℕ} (hQ : 1 ≤ Q)
    (x y : FordVinogradovTuple s Q) :
    fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y ∈
      fordVinogradovDisplacementBox s k Q := by
  classical
  rw [fordVinogradovDisplacementBox, Fintype.mem_piFinset]
  intro j
  simp only [Pi.sub_apply, Finset.mem_Icc]
  let d : ℕ := (j : ℕ) + 1
  have hx := fordVinogradovPowerVector_bounds x j
  have hy := fordVinogradovPowerVector_bounds y j
  have hQpow : 1 ≤ Q ^ d := Nat.one_le_pow d Q hQ
  have hRadius :
      ((fordVinogradovDisplacementRadius s Q j : ℕ) : ℤ) =
        (s : ℤ) * ((Q : ℤ) ^ d - 1) := by
    unfold fordVinogradovDisplacementRadius
    rw [Nat.cast_mul, Nat.cast_sub hQpow, Nat.cast_pow, Nat.cast_one]
  rw [hRadius]
  change
    -((s : ℤ) * ((Q : ℤ) ^ d - 1)) ≤
        fordVinogradovPowerVector s k Q x j -
          fordVinogradovPowerVector s k Q y j ∧
      fordVinogradovPowerVector s k Q x j -
          fordVinogradovPowerVector s k Q y j ≤
        (s : ℤ) * ((Q : ℤ) ^ d - 1)
  constructor <;> nlinarith

theorem fordVinogradovDisplacementImage_subset_box
    {s k Q : ℕ} (hQ : 1 ≤ Q) :
    ((Finset.univ : Finset (FordVinogradovTuple s Q)) ×ˢ Finset.univ).image
        (fun xy => fordVinogradovPowerVector s k Q xy.1 -
          fordVinogradovPowerVector s k Q xy.2) ⊆
      fordVinogradovDisplacementBox s k Q := by
  intro h hh
  rcases Finset.mem_image.mp hh with ⟨xy, hxy, rfl⟩
  exact fordVinogradovPowerVector_sub_mem_box hQ xy.1 xy.2

theorem card_int_Icc_neg_natCast (r : ℕ) :
    (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1 := by
  rw [Int.card_Icc]
  have h : (r : ℤ) + 1 - -(r : ℤ) = ((2 * r + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]

theorem card_fordVinogradovDisplacementBox (s k Q : ℕ) :
    (fordVinogradovDisplacementBox s k Q).card =
      ∏ j : Fin k, (2 * fordVinogradovDisplacementRadius s Q j + 1) := by
  unfold fordVinogradovDisplacementBox
  rw [Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j hj
  exact card_int_Icc_neg_natCast _

theorem fordVinogradovDisplacementFactor_le
    {s k Q : ℕ} (hs : 1 ≤ s) (hQ : 1 ≤ Q) (j : Fin k) :
    2 * fordVinogradovDisplacementRadius s Q j + 1 ≤
      (2 * s) * Q ^ ((j : ℕ) + 1) := by
  let d : ℕ := (j : ℕ) + 1
  have hQpow : 1 ≤ Q ^ d := Nat.one_le_pow d Q hQ
  unfold fordVinogradovDisplacementRadius
  have hsplit : Q ^ d = (Q ^ d - 1) + 1 := (Nat.sub_add_cancel hQpow).symm
  calc
    2 * (s * (Q ^ d - 1)) + 1 ≤
        2 * (s * (Q ^ d - 1)) + 2 * s := by omega
    _ = (2 * s) * ((Q ^ d - 1) + 1) := by ring
    _ = (2 * s) * Q ^ d := by rw [← hsplit]

theorem sum_fin_degrees (k : ℕ) :
    (∑ j : Fin k, ((j : ℕ) + 1)) = k * (k + 1) / 2 := by
  have hchoose : (∑ i ∈ Finset.range k, (i + 1)) = Nat.choose (k + 1) 2 := by
    cases k with
    | zero => simp
    | succ k =>
        simpa [Nat.choose_one_right, add_assoc] using
          (Nat.sum_range_add_choose k 1)
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i + 1),
    hchoose, Nat.choose_two_right]
  simp [Nat.mul_comm]

theorem card_fordVinogradovDisplacementBox_le
    {s k Q : ℕ} (hs : 1 ≤ s) (hQ : 1 ≤ Q) :
    (fordVinogradovDisplacementBox s k Q).card ≤
      (2 * s) ^ k * Q ^ (k * (k + 1) / 2) := by
  rw [card_fordVinogradovDisplacementBox]
  calc
    (∏ j : Fin k, (2 * fordVinogradovDisplacementRadius s Q j + 1)) ≤
        ∏ j : Fin k, ((2 * s) * Q ^ ((j : ℕ) + 1)) := by
      exact Finset.prod_le_prod' fun j _hj =>
        fordVinogradovDisplacementFactor_le hs hQ j
    _ = (2 * s) ^ k * Q ^ (k * (k + 1) / 2) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Finset.prod_pow_eq_pow_sum, sum_fin_degrees]

/-- Every point contributes a diagonal pair, for an arbitrary finite
representation problem. -/
theorem card_le_fordRepresentationCount_zero
    {β Γ : Type*} [DecidableEq β] [AddCommGroup Γ] [DecidableEq Γ]
    (B : Finset β) (F : β → Γ) :
    B.card ≤ fordRepresentationCount B F 0 := by
  classical
  rw [fordRepresentationCount_zero_eq_sum_fiber_sq]
  calc
    B.card = ∑ v ∈ B.image F, fordRepresentationFiberCount B F v := by
      apply Finset.card_eq_sum_card_fiberwise
      intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    _ ≤ ∑ v ∈ B.image F, fordRepresentationFiberCount B F v ^ 2 := by
      apply Finset.sum_le_sum
      intro v hv
      let n := fordRepresentationFiberCount B F v
      change n ≤ n ^ 2
      nlinarith [Nat.zero_le n]

/-- The total number of ordered pairs is at most the number of attained
displacements times the zero-displacement representation count. -/
theorem card_sq_le_displacementImage_mul_fordRepresentationCount_zero
    {β Γ : Type*} [DecidableEq β] [AddCommGroup Γ] [DecidableEq Γ]
    (B : Finset β) (F : β → Γ) :
    B.card ^ 2 ≤
      ((B ×ˢ B).image fun xy => F xy.1 - F xy.2).card *
        fordRepresentationCount B F 0 := by
  classical
  let D : β × β → Γ := fun xy => F xy.1 - F xy.2
  calc
    B.card ^ 2 = (B ×ˢ B).card := by simp [pow_two]
    _ = ∑ w ∈ (B ×ˢ B).image D,
          ((B ×ˢ B).filter fun xy => D xy = w).card :=
      Finset.card_eq_sum_card_image D (B ×ˢ B)
    _ = ∑ w ∈ (B ×ˢ B).image D, fordRepresentationCount B F w := by
      apply Finset.sum_congr rfl
      intro w hw
      rfl
    _ ≤ ∑ _w ∈ (B ×ˢ B).image D, fordRepresentationCount B F 0 := by
      apply Finset.sum_le_sum
      intro w hw
      exact ford_zeroRepresentationDominates B F w
    _ = ((B ×ˢ B).image D).card * fordRepresentationCount B F 0 := by
      simp

/-- The shifted count is dominated by the zero count, exactly as used below
equation (1.4). -/
theorem fordVinogradovShiftedCountNat_le
    (s k Q : ℕ) (h : Fin k → ℤ) :
    fordVinogradovShiftedCountNat s k Q h ≤
      fordVinogradovMomentNat s k Q := by
  exact ford_zeroRepresentationDominates
    (Finset.univ : Finset (FordVinogradovTuple s Q))
    (fordVinogradovPowerVector s k Q) h

/-- The counting inequality immediately preceding equation (1.5).  It keeps
Ford's exact factor `(2s)^k Q^(k(k+1)/2)`. -/
theorem ford_vinogradov_total_count_le
    {s k Q : ℕ} (hs : 1 ≤ s) (hQ : 1 ≤ Q) :
    Q ^ (2 * s) ≤
      ((2 * s) ^ k * Q ^ (k * (k + 1) / 2)) *
        fordVinogradovMomentNat s k Q := by
  let B : Finset (FordVinogradovTuple s Q) := Finset.univ
  let F : FordVinogradovTuple s Q → (Fin k → ℤ) :=
    fordVinogradovPowerVector s k Q
  let D : FordVinogradovTuple s Q × FordVinogradovTuple s Q → (Fin k → ℤ) :=
    fun xy => F xy.1 - F xy.2
  have hTotal :=
    card_sq_le_displacementImage_mul_fordRepresentationCount_zero B F
  have hImageSubset : (B ×ˢ B).image D ⊆
      fordVinogradovDisplacementBox s k Q := by
    simpa only [B, F, D] using
      fordVinogradovDisplacementImage_subset_box (s := s) (k := k) hQ
  have hImageCard : ((B ×ˢ B).image D).card ≤
      (2 * s) ^ k * Q ^ (k * (k + 1) / 2) :=
    (Finset.card_le_card hImageSubset).trans
      (card_fordVinogradovDisplacementBox_le hs hQ)
  calc
    Q ^ (2 * s) = (Q ^ s) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ = B.card ^ 2 := by simp only [B, card_fordVinogradovTuple_univ]
    _ ≤ ((B ×ˢ B).image D).card * fordRepresentationCount B F 0 := hTotal
    _ ≤ ((2 * s) ^ k * Q ^ (k * (k + 1) / 2)) *
          fordRepresentationCount B F 0 :=
      Nat.mul_le_mul_right _ hImageCard
    _ = ((2 * s) ^ k * Q ^ (k * (k + 1) / 2)) *
          fordVinogradovMomentNat s k Q := by rfl

/-- The first term of Ford's equation (1.5), in real-valued form. -/
theorem fordVinogradovLowerTerm_le_moment
    {s k Q : ℕ} (hs : 1 ≤ s) (hQ : 1 ≤ Q)
    (hkappa : fordVinogradovKappa k ≤ 2 * s) :
    fordVinogradovLowerTerm s k Q ≤
      (fordVinogradovMomentNat s k Q : ℝ) := by
  have hcount := ford_vinogradov_total_count_le (s := s) (k := k) hs hQ
  have hcast :
      (Q : ℝ) ^ (2 * s) ≤
        (((2 * s : ℕ) : ℝ) ^ k *
            (Q : ℝ) ^ fordVinogradovKappa k) *
          (fordVinogradovMomentNat s k Q : ℝ) := by
    exact_mod_cast hcount
  have ha : 0 < (((2 * s : ℕ) : ℝ) ^ k) := by positivity
  have hq : 0 < ((Q : ℝ) ^ fordVinogradovKappa k) := by positivity
  have hdiv :
      (Q : ℝ) ^ (2 * s) /
          ((((2 * s : ℕ) : ℝ) ^ k) *
            (Q : ℝ) ^ fordVinogradovKappa k) ≤
        (fordVinogradovMomentNat s k Q : ℝ) := by
    rw [div_le_iff₀ (mul_pos ha hq)]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hcast
  have hpow :
      (Q : ℝ) ^ (2 * s - fordVinogradovKappa k) *
          (Q : ℝ) ^ fordVinogradovKappa k =
        (Q : ℝ) ^ (2 * s) := by
    rw [← pow_add, Nat.sub_add_cancel hkappa]
  unfold fordVinogradovLowerTerm
  calc
    (((2 * s : ℕ) : ℝ)⁻¹) ^ k *
          (Q : ℝ) ^ (2 * s - fordVinogradovKappa k) =
        (Q : ℝ) ^ (2 * s) /
          ((((2 * s : ℕ) : ℝ) ^ k) *
            (Q : ℝ) ^ fordVinogradovKappa k) := by
      rw [inv_pow]
      field_simp [ne_of_gt ha, ne_of_gt hq]
      nlinarith
    _ ≤ (fordVinogradovMomentNat s k Q : ℝ) := hdiv

/-- Equation (1.5), combining the displacement-count and diagonal lower
bounds. -/
theorem ford_equation_1_5
    {s k : ℕ} {P : ℝ} (hs : 1 ≤ s) (hP : 1 ≤ P)
    (hkappa : fordVinogradovKappa k ≤ 2 * s) :
    max (fordVinogradovLowerTerm s k ⌊P⌋₊) ((⌊P⌋₊ : ℝ) ^ s) ≤
      (fordVinogradovMoment s k P : ℝ) := by
  have hQ : 1 ≤ ⌊P⌋₊ := Nat.floor_pos.mpr hP
  have hfirst : fordVinogradovLowerTerm s k ⌊P⌋₊ ≤
      (fordVinogradovMoment s k P : ℝ) := by
    simpa [fordVinogradovMoment] using
      fordVinogradovLowerTerm_le_moment hs hQ hkappa
  have hdiagonal : (⌊P⌋₊ : ℝ) ^ s ≤
      (fordVinogradovMoment s k P : ℝ) := by
    have hdiagNat : ⌊P⌋₊ ^ s ≤ fordVinogradovMomentNat s k ⌊P⌋₊ := by
      simpa [fordVinogradovShiftedCountNat, card_fordVinogradovTuple_univ] using
        card_le_fordRepresentationCount_zero
          (Finset.univ : Finset (FordVinogradovTuple s ⌊P⌋₊))
          (fordVinogradovPowerVector s k ⌊P⌋₊)
    unfold fordVinogradovMoment
    exact_mod_cast hdiagNat
  rcases le_total (fordVinogradovLowerTerm s k ⌊P⌋₊) ((⌊P⌋₊ : ℝ) ^ s) with
    hle | hle
  · rw [max_eq_right hle]
    exact hdiagonal
  · rw [max_eq_left hle]
    exact hfirst

/-- The diagonal lower bound in equation (1.5): `J_{s,k}(P) ≥ floor(P)^s`. -/
theorem ford_floor_pow_le_vinogradovMoment (s k : ℕ) {P : ℝ} :
    ⌊P⌋₊ ^ s ≤ fordVinogradovMoment s k P := by
  unfold fordVinogradovMoment fordVinogradovMomentNat
  simpa [fordVinogradovShiftedCountNat, card_fordVinogradovTuple_univ] using
    card_le_fordRepresentationCount_zero
      (Finset.univ : Finset (FordVinogradovTuple s ⌊P⌋₊))
      (fordVinogradovPowerVector s k ⌊P⌋₊)

/-! ## The normalized-Haar identity, equation (1.3) -/

/-- The degree vector contributed by one source integer `1 ≤ n ≤ Q`. -/
def fordVinogradovExponent {k Q : ℕ} (n : Fin Q) : Fin k → ℤ :=
  fun j => (((n : ℕ) + 1) ^ ((j : ℕ) + 1) : ℕ)

/-- One exponential monomial in Ford's complete Weyl sum. -/
def fordVinogradovMonomial {k Q : ℕ} (n : Fin Q)
    (α : UnitAddTorus (Fin k)) : ℂ :=
  UnitAddTorus.mFourier (fordVinogradovExponent n) α

/-- The complete Weyl sum over the literal integer range `1, ..., Q`. -/
def fordVinogradovWeylSum (k Q : ℕ) (α : UnitAddTorus (Fin k)) : ℂ :=
  ∑ n : Fin Q, fordVinogradovMonomial n α

/-- A nonzero Fourier character has normalized Haar integral zero; the zero
character has integral one. -/
theorem ford_integral_fourier_haar_eq (n : ℤ) :
    ∫ x : UnitAddCircle, fourier n x ∂AddCircle.haarAddCircle =
      if n = 0 then 1 else 0 := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  split_ifs with hn
  · subst n
    simp
  · exact integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
      (fourier_add_half_inv_index hn (by norm_num))

/-- Product orthogonality on the `k`-dimensional unit torus. -/
theorem ford_integral_mFourier_pi_haar_eq {k : ℕ} (h : Fin k → ℤ) :
    ∫ α : UnitAddTorus (Fin k), UnitAddTorus.mFourier h α
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      if h = 0 then 1 else 0 := by
  change (∫ α : UnitAddTorus (Fin k), ∏ i, fourier (h i) (α i)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod]
  simp_rw [ford_integral_fourier_haar_eq]
  split_ifs with hh
  · subst h
    simp
  · simp only [Finset.prod_ite_zero, Finset.prod_const_one]
    rw [if_neg]
    simpa [funext_iff] using hh

theorem fordVinogradovPowerVector_eq_sum_exponent
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) :
    fordVinogradovPowerVector s k Q x =
      ∑ i : Fin s, fordVinogradovExponent (x i) := by
  ext j
  simp [fordVinogradovPowerVector, fordVinogradovExponent]

theorem ford_prod_monomial_eq
    {s k Q : ℕ} (x : FordVinogradovTuple s Q) (α : UnitAddTorus (Fin k)) :
    ∏ i : Fin s, fordVinogradovMonomial (x i) α =
      UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α := by
  classical
  rw [fordVinogradovPowerVector_eq_sum_exponent]
  induction (Finset.univ : Finset (Fin s)) using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [UnitAddTorus.mFourier_add]
      exact congrArg (fun z => fordVinogradovMonomial (x a) α * z) ih

theorem ford_vinogradov_weyl_pow
    (s k Q : ℕ) (α : UnitAddTorus (Fin k)) :
    fordVinogradovWeylSum k Q α ^ s =
      ∑ x : FordVinogradovTuple s Q,
        UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α := by
  rw [fordVinogradovWeylSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  exact ford_prod_monomial_eq x α

theorem ford_conj_vinogradov_weyl_pow
    (s k Q : ℕ) (α : UnitAddTorus (Fin k)) :
    conj (fordVinogradovWeylSum k Q α) ^ s =
      ∑ y : FordVinogradovTuple s Q,
        UnitAddTorus.mFourier (-fordVinogradovPowerVector s k Q y) α := by
  have h := congrArg conj (ford_vinogradov_weyl_pow s k Q α)
  simpa only [map_pow, map_sum, UnitAddTorus.mFourier_neg] using h

theorem ford_pair_character
    {s k Q : ℕ} (x y : FordVinogradovTuple s Q)
    (α : UnitAddTorus (Fin k)) :
    UnitAddTorus.mFourier (fordVinogradovPowerVector s k Q x) α *
        UnitAddTorus.mFourier (-fordVinogradovPowerVector s k Q y) α =
      UnitAddTorus.mFourier
        (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α := by
  rw [sub_eq_add_neg, UnitAddTorus.mFourier_add]

/-- Complex-valued orthogonality form of Ford's equation (1.3). -/
theorem ford_vinogradov_torus_mean_eq (s k Q : ℕ) :
    ∫ α : UnitAddTorus (Fin k),
        fordVinogradovWeylSum k Q α ^ s *
          conj (fordVinogradovWeylSum k Q α) ^ s
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      (fordVinogradovMomentNat s k Q : ℂ) := by
  simp_rw [ford_vinogradov_weyl_pow, ford_conj_vinogradov_weyl_pow,
    Finset.sum_mul_sum]
  simp_rw [ford_pair_character]
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  have hchar (x y : FordVinogradovTuple s Q) :
      Integrable
        (fun α : UnitAddTorus (Fin k) =>
          UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) μ := by
    rw [← integrableOn_univ]
    have hc : Continuous (fun α : UnitAddTorus (Fin k) =>
        UnitAddTorus.mFourier
          (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) :=
      (UnitAddTorus.mFourier
        (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y)).continuous
    exact hc.continuousOn.integrableOn_compact isCompact_univ
  have hinner (x : FordVinogradovTuple s Q) :
      Integrable
        (fun α : UnitAddTorus (Fin k) =>
          ∑ y : FordVinogradovTuple s Q,
            UnitAddTorus.mFourier
              (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α) μ := by
    exact integrable_finsetSum Finset.univ fun y _hy => hchar x y
  change (∫ α : UnitAddTorus (Fin k),
      ∑ x : FordVinogradovTuple s Q,
        ∑ y : FordVinogradovTuple s Q,
          UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α ∂μ) = _
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun x _hx => hinner x)]
  calc
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            ∫ α : UnitAddTorus (Fin k),
              UnitAddTorus.mFourier
                (fordVinogradovPowerVector s k Q x -
                  fordVinogradovPowerVector s k Q y) α ∂μ := by
        apply Finset.sum_congr rfl
        intro x hx
        exact MeasureTheory.integral_finsetSum Finset.univ (fun y _hy => hchar x y)
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            if fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y = 0
            then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact ford_integral_mFourier_pi_haar_eq _
    _ = (fordVinogradovMomentNat s k Q : ℂ) := by
        simp only [fordVinogradovMomentNat, fordVinogradovShiftedCountNat,
          fordRepresentationCount, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
          Nat.cast_one, Nat.cast_zero]
        rw [Finset.sum_product]

theorem ford_pow_mul_conj_pow (z : ℂ) (s : ℕ) :
    z ^ s * conj z ^ s = ((‖z‖ : ℝ) : ℂ) ^ (2 * s) := by
  rw [← mul_pow, Complex.mul_conj']
  rw [← pow_mul]

theorem ford_vinogradov_torus_real_mean_eq (s k Q : ℕ) :
    ∫ α : UnitAddTorus (Fin k), ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      (fordVinogradovMomentNat s k Q : ℝ) := by
  apply Complex.ofReal_injective
  have hcast :
      (∫ α : UnitAddTorus (Fin k),
          ((‖fordVinogradovWeylSum k Q α‖ ^ (2 * s) : ℝ) : ℂ)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
        ((∫ α : UnitAddTorus (Fin k),
          ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) : ℝ) : ℂ) :=
    integral_ofReal
  rw [← hcast]
  simpa only [ford_pow_mul_conj_pow, Complex.ofReal_natCast, Complex.ofReal_pow] using
    ford_vinogradov_torus_mean_eq s k Q

/-- Ford's equation (1.3), with the paper's literal half-open unit cube and
Lebesgue measure. -/
theorem ford_equation_1_3 (s k Q : ℕ) :
    (∫ (α : Fin k → ℝ) in
        {α : Fin k → ℝ | ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1},
      ‖fordVinogradovWeylSum k Q (fun j => (α j : UnitAddCircle))‖ ^ (2 * s)) =
      (fordVinogradovMomentNat s k Q : ℝ) := by
  have hpre :=
    UnitAddTorus.integral_preimage
      (fun α : UnitAddTorus (Fin k) =>
        ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s))
      (fun _ : Fin k => 0)
  change
    (∫ α : UnitAddTorus (Fin k), ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
      ∫ (α : Fin k → ℝ) in
        {α : Fin k → ℝ | ∀ j, α j ∈ Set.Ioc (0 : ℝ) (0 + 1)},
        ‖fordVinogradovWeylSum k Q (fun j => (α j : UnitAddCircle))‖ ^ (2 * s) at hpre
  calc
    _ = ∫ α : UnitAddTorus (Fin k), ‖fordVinogradovWeylSum k Q α‖ ^ (2 * s)
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
      simpa only [zero_add] using hpre.symm
    _ = (fordVinogradovMomentNat s k Q : ℝ) :=
      ford_vinogradov_torus_real_mean_eq s k Q

/-- Every torus character used in the shifted identity is integrable against
the explicit product of normalized Haar measures. -/
theorem ford_integrable_mFourier_pi_haar {k : ℕ} (h : Fin k → ℤ) :
    Integrable (fun α : UnitAddTorus (Fin k) => UnitAddTorus.mFourier h α)
      (Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) := by
  rw [← integrableOn_univ]
  exact (UnitAddTorus.mFourier h).continuous.continuousOn.integrableOn_compact
    isCompact_univ

/-- The shifted character has Ford's literal negative sign. -/
theorem ford_pair_character_mul_shift
    {s k Q : ℕ} (x y : FordVinogradovTuple s Q) (h : Fin k → ℤ)
    (α : UnitAddTorus (Fin k)) :
    UnitAddTorus.mFourier
        (fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y) α *
        UnitAddTorus.mFourier (-h) α =
      UnitAddTorus.mFourier
        (fordVinogradovPowerVector s k Q x -
          fordVinogradovPowerVector s k Q y - h) α := by
  simpa only [sub_eq_add_neg] using
    (UnitAddTorus.mFourier_add
      (n := -h)
      (m := fordVinogradovPowerVector s k Q x - fordVinogradovPowerVector s k Q y)
      (x := α)).symm

/-- The shifted integral displayed immediately after equation (1.4). -/
theorem ford_vinogradov_shifted_torus_mean_eq
    (s k Q : ℕ) (h : Fin k → ℤ) :
    ∫ α : UnitAddTorus (Fin k),
        fordVinogradovWeylSum k Q α ^ s *
          conj (fordVinogradovWeylSum k Q α) ^ s *
          UnitAddTorus.mFourier (-h) α
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      (fordVinogradovShiftedCountNat s k Q h : ℂ) := by
  simp_rw [ford_vinogradov_weyl_pow, ford_conj_vinogradov_weyl_pow,
    Finset.sum_mul_sum]
  simp_rw [ford_pair_character, Finset.sum_mul]
  simp_rw [ford_pair_character_mul_shift]
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  have hchar (x y : FordVinogradovTuple s Q) :
      Integrable
        (fun α : UnitAddTorus (Fin k) =>
          UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x -
              fordVinogradovPowerVector s k Q y - h) α) μ :=
    ford_integrable_mFourier_pi_haar _
  have hinner (x : FordVinogradovTuple s Q) :
      Integrable
        (fun α : UnitAddTorus (Fin k) =>
          ∑ y : FordVinogradovTuple s Q,
            UnitAddTorus.mFourier
              (fordVinogradovPowerVector s k Q x -
                fordVinogradovPowerVector s k Q y - h) α) μ := by
    exact integrable_finsetSum Finset.univ fun y _hy => hchar x y
  change (∫ α : UnitAddTorus (Fin k),
      ∑ x : FordVinogradovTuple s Q,
        ∑ y : FordVinogradovTuple s Q,
          UnitAddTorus.mFourier
            (fordVinogradovPowerVector s k Q x -
              fordVinogradovPowerVector s k Q y - h) α ∂μ) = _
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun x _hx => hinner x)]
  calc
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            ∫ α : UnitAddTorus (Fin k),
              UnitAddTorus.mFourier
                (fordVinogradovPowerVector s k Q x -
                  fordVinogradovPowerVector s k Q y - h) α ∂μ := by
        apply Finset.sum_congr rfl
        intro x hx
        exact MeasureTheory.integral_finsetSum Finset.univ (fun y _hy => hchar x y)
    _ = ∑ x : FordVinogradovTuple s Q,
          ∑ y : FordVinogradovTuple s Q,
            if fordVinogradovPowerVector s k Q x -
                fordVinogradovPowerVector s k Q y - h = 0
            then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact ford_integral_mFourier_pi_haar_eq _
    _ = (fordVinogradovShiftedCountNat s k Q h : ℂ) := by
        simp only [fordVinogradovShiftedCountNat, fordRepresentationCount,
          Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hd : fordVinogradovPowerVector s k Q x -
            fordVinogradovPowerVector s k Q y = h
        · simp [hd]
        · have hz : fordVinogradovPowerVector s k Q x -
              fordVinogradovPowerVector s k Q y - h ≠ 0 := by
            intro hz
            exact hd (sub_eq_zero.mp hz)
          simp [hd, hz]

/-- Literal half-open-cube version of Ford's shifted Fourier-coefficient
identity, including the source factor `e(-α·h)`. -/
theorem ford_shifted_integral_identity
    (s k Q : ℕ) (h : Fin k → ℤ) :
    (∫ (α : Fin k → ℝ) in
        {α : Fin k → ℝ | ∀ j, α j ∈ Set.Ioc (0 : ℝ) 1},
      ((‖fordVinogradovWeylSum k Q (fun j => (α j : UnitAddCircle))‖ ^
          (2 * s) : ℝ) : ℂ) *
        UnitAddTorus.mFourier (-h) (fun j => (α j : UnitAddCircle))) =
      (fordVinogradovShiftedCountNat s k Q h : ℂ) := by
  let f : UnitAddTorus (Fin k) → ℂ := fun α =>
    ((‖fordVinogradovWeylSum k Q α‖ ^ (2 * s) : ℝ) : ℂ) *
      UnitAddTorus.mFourier (-h) α
  have hpre := UnitAddTorus.integral_preimage f (fun _ : Fin k => 0)
  change
    (∫ α : UnitAddTorus (Fin k), f α
      ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
      ∫ (α : Fin k → ℝ) in
        {α : Fin k → ℝ | ∀ j, α j ∈ Set.Ioc (0 : ℝ) (0 + 1)},
        f (fun j => (α j : UnitAddCircle)) at hpre
  calc
    _ = ∫ α : UnitAddTorus (Fin k), f α
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) := by
      simpa only [zero_add] using hpre.symm
    _ = (fordVinogradovShiftedCountNat s k Q h : ℂ) := by
      simpa only [f, Complex.ofReal_pow, ford_pow_mul_conj_pow] using
        ford_vinogradov_shifted_torus_mean_eq s k Q h

#print axioms card_le_fordRepresentationCount_zero
#print axioms card_sq_le_displacementImage_mul_fordRepresentationCount_zero
#print axioms fordVinogradovShiftedCountNat_le
#print axioms ford_vinogradov_total_count_le
#print axioms fordVinogradovLowerTerm_le_moment
#print axioms ford_equation_1_5
#print axioms ford_floor_pow_le_vinogradovMoment
#print axioms ford_integral_fourier_haar_eq
#print axioms ford_integral_mFourier_pi_haar_eq
#print axioms ford_vinogradov_torus_mean_eq
#print axioms ford_equation_1_3
#print axioms ford_vinogradov_shifted_torus_mean_eq
#print axioms ford_shifted_integral_identity

end

end GafniTao
