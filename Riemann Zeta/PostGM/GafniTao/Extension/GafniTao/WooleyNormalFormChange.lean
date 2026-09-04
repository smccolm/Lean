import GafniTao.WooleySection7TopExtraction

/-!
# Integral change to Wooley's tail-only normal form

The assertion preceding (7.6) that there is “no loss of generality” in
using (7.7) is a modular integral change of equations.  This file constructs
that change.  A left inverse to the low coefficient matrix is lifted from
`ZMod (p^B)` to integers.  Its transformed equations consist of one monomial,
a `p^c`-divisible tail beginning in degree `k+1`, a constant (which cancels
from equal-length tuple displacements), and an exact `p^B` error.
-/

open Finset Polynomial Matrix
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Integral lift of the modular row operation applied to a polynomial
system. -/
def wooleyNormalFormCombination {k : ℕ}
    (phi : WooleyPolynomialSystem k) (q : ℕ)
    (G : Matrix (Fin k) (Fin k) (ZMod q)) (i : Fin k) : Polynomial ℤ :=
  ∑ j : Fin k, C (wooleyZModMatrixIntLift G i j) * phi j

/-- Positive-degree part through degree `k` of a transformed equation. -/
def wooleyNormalFormPositiveLow {k : ℕ}
    (phi : WooleyPolynomialSystem k) (q : ℕ)
    (G : Matrix (Fin k) (Fin k) (ZMod q)) (i : Fin k) : Polynomial ℤ :=
  ∑ d : Fin k,
    C ((wooleyNormalFormCombination phi q G i).coeff ((d : ℕ) + 1)) *
      X ^ ((d : ℕ) + 1)

/-- The inverse low-coefficient matrix makes the transformed positive low
part exactly one monomial modulo the working modulus. -/
theorem wooleyNormalFormPositiveLow_map_eq_monomial
    {k p B : ℕ} {phi : WooleyPolynomialSystem k}
    (G : Matrix (Fin k) (Fin k) (ZMod (p ^ B)))
    (hG : G * Matrix.transpose
      (wooleyPolynomialSystemLowMatrixMod phi (p ^ B)) = 1)
    (i : Fin k) :
    Polynomial.map (Int.castRingHom (ZMod (p ^ B)))
        (wooleyNormalFormPositiveLow phi (p ^ B) G i) =
      X ^ ((i : ℕ) + 1) := by
  have hcoeff (d : Fin k) :
      ((wooleyNormalFormCombination phi (p ^ B) G i).coeff
          ((d : ℕ) + 1) : ZMod (p ^ B)) =
        if i = d then 1 else 0 := by
    have hentry := congrArg
      (fun A : Matrix (Fin k) (Fin k) (ZMod (p ^ B)) => A i d) hG
    unfold wooleyNormalFormCombination
    rw [← lcoeff_apply, map_sum]
    simp only [lcoeff_apply, coeff_C_mul]
    have hlow (j : Fin k) :
        ((phi j).coeff ((d : ℕ) + 1) : ZMod (p ^ B)) =
          wooleyPolynomialSystemLowMatrixMod phi (p ^ B) d j := by
      unfold wooleyPolynomialSystemLowMatrixMod
        wooleyPolynomialSystemLowMatrix
      rw [wooleyPolynomialLowPart_coeff]
      omega
    calc
      ((∑ j : Fin k,
          wooleyZModMatrixIntLift G i j *
            (phi j).coeff ((d : ℕ) + 1) : ℤ) : ZMod (p ^ B)) =
          ∑ j : Fin k,
            (wooleyZModMatrixIntLift G i j : ZMod (p ^ B)) *
              ((phi j).coeff ((d : ℕ) + 1) : ZMod (p ^ B)) := by
                push_cast
                rfl
      _ = ∑ j : Fin k,
            G i j * wooleyPolynomialSystemLowMatrixMod phi (p ^ B) d j := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [wooleyZModMatrixIntLift_cast, hlow]
      _ = if i = d then 1 else 0 := by
        simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
          using hentry
  unfold wooleyNormalFormPositiveLow
  simp only [Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X]
  calc
    (∑ d : Fin k,
        C (((wooleyNormalFormCombination phi (p ^ B) G i).coeff
          ((d : ℕ) + 1) : ℤ) : ZMod (p ^ B)) * X ^ ((d : ℕ) + 1)) =
      ∑ d : Fin k, C (if i = d then 1 else 0) *
        X ^ ((d : ℕ) + 1) := by
          apply Finset.sum_congr rfl
          intro d hd
          rw [hcoeff d]
    _ = X ^ ((i : ℕ) + 1) := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro d hd hdi
        simp [Ne.symm hdi]
      · simp

/-- The modular error in the low positive part is an exact integral
multiple of `p^B`. -/
theorem wooleyNormalFormPositiveLow_exists_error
    {k p B : ℕ} {phi : WooleyPolynomialSystem k}
    (G : Matrix (Fin k) (Fin k) (ZMod (p ^ B)))
    (hG : G * Matrix.transpose
      (wooleyPolynomialSystemLowMatrixMod phi (p ^ B)) = 1)
    (i : Fin k) :
    ∃ Error : Polynomial ℤ,
      wooleyNormalFormPositiveLow phi (p ^ B) G i =
        X ^ ((i : ℕ) + 1) + C ((p : ℤ) ^ B) * Error := by
  let f := wooleyNormalFormPositiveLow phi (p ^ B) G i -
    X ^ ((i : ℕ) + 1)
  have hmap : Polynomial.map (Int.castRingHom (ZMod (p ^ B))) f = 0 := by
    dsimp only [f]
    rw [Polynomial.map_sub,
      wooleyNormalFormPositiveLow_map_eq_monomial G hG]
    simp
  obtain ⟨Error, hError⟩ :=
    wooleyPolynomial_C_primePower_dvd_of_map_eq_zero f hmap
  refine ⟨Error, ?_⟩
  dsimp only [f] at hError
  calc
    wooleyNormalFormPositiveLow phi (p ^ B) G i =
        (wooleyNormalFormPositiveLow phi (p ^ B) G i -
          X ^ ((i : ℕ) + 1)) + X ^ ((i : ℕ) + 1) := by ring
    _ = C ((p : ℤ) ^ B) * Error + X ^ ((i : ℕ) + 1) := by rw [hError]
    _ = X ^ ((i : ℕ) + 1) + C ((p : ℤ) ^ B) * Error := by ring

/-- In a `p^c`-spaced system, every coefficient at degree at least `k+1`
is divisible by `p^c`. -/
theorem WooleyPolynomialSystem.Spaced.high_coeff_dvd
    {k p c : ℕ} {phi : WooleyPolynomialSystem k}
    (hphi : phi.Spaced p c) (j : Fin k) (n : ℕ) (hn : k + 1 ≤ n) :
    (p : ℤ) ^ c ∣ (phi j).coeff n := by
  obtain ⟨theta, htheta⟩ := hphi
  rw [htheta j, coeff_add, coeff_X_pow]
  have hne : n ≠ (j : ℕ) + 1 := by omega
  rw [if_neg hne, zero_add, coeff_C_mul]
  exact dvd_mul_right _ _

/-- The same high-degree divisibility is preserved by the lifted row
operation. -/
theorem wooleyNormalFormCombination_high_coeff_dvd
    {k p c q : ℕ} {phi : WooleyPolynomialSystem k}
    (hphi : phi.Spaced p c)
    (G : Matrix (Fin k) (Fin k) (ZMod q)) (i : Fin k)
    (n : ℕ) (hn : k + 1 ≤ n) :
    (p : ℤ) ^ c ∣ (wooleyNormalFormCombination phi q G i).coeff n := by
  unfold wooleyNormalFormCombination
  rw [← lcoeff_apply, map_sum]
  simp only [lcoeff_apply, coeff_C_mul]
  apply dvd_sum
  intro j hj
  exact dvd_mul_of_dvd_right (hphi.high_coeff_dvd j n hn) _

/-- A zero-constant polynomial with a scalar-divisible tail has the exact
tail-only form needed in (7.7). -/
theorem wooleyPolynomial_exists_positiveLow_add_scalar_X_tail
    (k : ℕ) (f : Polynomial ℤ) (z : ℤ) (hz : z ≠ 0)
    (hzero : f.coeff 0 = 0)
    (hhigh : ∀ n, k + 1 ≤ n → z ∣ f.coeff n) :
    ∃ theta : Polynomial ℤ,
      f = (∑ i : Fin k, C (f.coeff ((i : ℕ) + 1)) *
              X ^ ((i : ℕ) + 1)) +
        C z * X ^ (k + 1) * theta := by
  obtain ⟨Xi, hXi⟩ :=
    wooleyPolynomial_exists_positiveLow_add_scalarTail k f z hzero hhigh
  let low : Polynomial ℤ :=
    ∑ i : Fin k, C (f.coeff ((i : ℕ) + 1)) * X ^ ((i : ℕ) + 1)
  have hXiLow : ∀ n < k + 1, Xi.coeff n = 0 := by
    intro n hn
    have hcoeff := congrArg (fun g : Polynomial ℤ => g.coeff n) hXi
    have hlowCoeff : low.coeff n = f.coeff n := by
      dsimp only [low]
      rw [← lcoeff_apply, map_sum]
      simp only [lcoeff_apply, coeff_C_mul, coeff_X_pow]
      by_cases hn0 : n = 0
      · subst n
        simp [hzero]
      · let i : Fin k := ⟨n - 1, by omega⟩
        have hi : (i : ℕ) + 1 = n := by
          dsimp only [i]
          omega
        rw [Finset.sum_eq_single i]
        · simp [hi]
        · intro d hd hdi
          have hval : (d : ℕ) + 1 ≠ n := by
            intro heq
            apply hdi
            apply Fin.ext
            omega
          simp [Ne.symm hval]
        · simp
    simp only [coeff_add, coeff_C_mul] at hcoeff
    rw [hlowCoeff] at hcoeff
    have hmul : z * Xi.coeff n = 0 := by linarith
    exact (mul_eq_zero.mp hmul).resolve_left hz
  have hXdvd : X ^ (k + 1) ∣ Xi :=
    X_pow_dvd_iff.mpr hXiLow
  obtain ⟨theta, htheta⟩ := hXdvd
  refine ⟨theta, ?_⟩
  change f = low + C z * X ^ (k + 1) * theta
  calc
    f = low + C z * Xi := hXi
    _ = low + C z * (X ^ (k + 1) * theta) := by rw [htheta]
    _ = low + C z * X ^ (k + 1) * theta := by ring

/-- Exact source normal-form construction.  The resulting equation is
tail-only modulo `p^B`; constants and the displayed error are retained. -/
theorem WooleyPolynomialSystem.Spaced.exists_tail_normal_change
    {k p c B : ℕ} {phi : WooleyPolynomialSystem k}
    (hphi : phi.Spaced p c) (hc : 1 ≤ c) (hp : p ≠ 0) :
    ∃ G : Matrix (Fin k) (Fin k) (ZMod (p ^ B)),
      ∃ psi Error : WooleyPolynomialSystem k,
      ∀ i : Fin k,
        wooleyNormalFormCombination phi (p ^ B) G i =
          C ((wooleyNormalFormCombination phi (p ^ B) G i).coeff 0) +
            wooleySection7NormalSystem k p c psi i +
            C ((p : ℤ) ^ B) * Error i := by
  obtain ⟨G, hG⟩ :=
    hphi.exists_lowMatrixMod_transpose_leftInverse (B := B) hc
  choose lowError hlow using fun i : Fin k =>
    wooleyNormalFormPositiveLow_exists_error G hG i
  let f (i : Fin k) := wooleyNormalFormCombination phi (p ^ B) G i -
    C ((wooleyNormalFormCombination phi (p ^ B) G i).coeff 0)
  have hfzero (i : Fin k) : (f i).coeff 0 = 0 := by
    simp [f]
  have hfhigh (i : Fin k) (n : ℕ) (hn : k + 1 ≤ n) :
      (p : ℤ) ^ c ∣ (f i).coeff n := by
    simp only [f, coeff_sub, coeff_C]
    rw [if_neg (by omega : n ≠ 0), sub_zero]
    exact wooleyNormalFormCombination_high_coeff_dvd hphi G i n hn
  choose psi htail using fun i : Fin k =>
    wooleyPolynomial_exists_positiveLow_add_scalar_X_tail
      k (f i) ((p : ℤ) ^ c) (pow_ne_zero c (by exact_mod_cast hp))
        (hfzero i) (hfhigh i)
  refine ⟨G, psi, lowError, ?_⟩
  intro i
  have hpositive :
      (∑ d : Fin k, C ((f i).coeff ((d : ℕ) + 1)) *
        X ^ ((d : ℕ) + 1)) =
      wooleyNormalFormPositiveLow phi (p ^ B) G i := by
    unfold wooleyNormalFormPositiveLow
    apply Finset.sum_congr rfl
    intro d hd
    congr 2
    simp only [f, coeff_sub, coeff_C]
    rw [if_neg (by omega : (d : ℕ) + 1 ≠ 0), sub_zero]
  have hf := htail i
  rw [hpositive, hlow i] at hf
  dsimp only [f] at hf
  unfold wooleySection7NormalSystem
  calc
    wooleyNormalFormCombination phi (p ^ B) G i =
        C ((wooleyNormalFormCombination phi (p ^ B) G i).coeff 0) +
          (wooleyNormalFormCombination phi (p ^ B) G i -
            C ((wooleyNormalFormCombination phi (p ^ B) G i).coeff 0)) := by
              ring
    _ = _ := by rw [hf]; ring

/-- The integral left-minus-right displacement attached to a single
polynomial and two equal-length tuple pairs. -/
def wooleyIntegerMixedPolynomialDisplacement {I J : Type*}
    (R S : ℕ) (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (f : Polynomial ℤ) : ℤ :=
  wooleyIntegerTupleDisplacement R (fun x => f.eval (leftPoint x)) leftXY -
    wooleyIntegerTupleDisplacement S (fun x => f.eval (rightPoint x)) rightXY

theorem wooleyIntegerMixedPolynomialDisplacement_zero
    {I J : Type*} (R S : ℕ) (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J) :
    wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
      leftXY rightXY 0 = 0 := by
  simp [wooleyIntegerMixedPolynomialDisplacement,
    wooleyIntegerTupleDisplacement]

theorem wooleyIntegerMixedPolynomialDisplacement_add
    {I J : Type*} (R S : ℕ) (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (f g : Polynomial ℤ) :
    wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (f + g) =
      wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
          leftXY rightXY f +
        wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
          leftXY rightXY g := by
  unfold wooleyIntegerMixedPolynomialDisplacement
  rw [wooleyIntegerTupleDisplacement_polynomial_add,
    wooleyIntegerTupleDisplacement_polynomial_add]
  ring

theorem wooleyIntegerMixedPolynomialDisplacement_C_mul
    {I J : Type*} (R S : ℕ) (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (z : ℤ) (f : Polynomial ℤ) :
    wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (C z * f) =
      z * wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY f := by
  unfold wooleyIntegerMixedPolynomialDisplacement
  rw [wooleyIntegerTupleDisplacement_polynomial_C_mul,
    wooleyIntegerTupleDisplacement_polynomial_C_mul]
  ring

theorem wooleyIntegerMixedPolynomialDisplacement_C
    {I J : Type*} (R S : ℕ) (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (z : ℤ) :
    wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
      leftXY rightXY (C z) = 0 := by
  simp [wooleyIntegerMixedPolynomialDisplacement,
    wooleyIntegerTupleDisplacement]

/-- The mixed displacement is additive over a finite polynomial family. -/
theorem wooleyIntegerMixedPolynomialDisplacement_sum
    {I J L : Type*} [Fintype L]
    (R S : ℕ) (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (f : L → Polynomial ℤ) :
    wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (∑ l, f l) =
      ∑ l, wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (f l) := by
  classical
  let F : Polynomial ℤ →+ ℤ :=
    { toFun := wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY
      map_zero' := wooleyIntegerMixedPolynomialDisplacement_zero
        R S leftPoint rightPoint leftXY rightXY
      map_add' := wooleyIntegerMixedPolynomialDisplacement_add
        R S leftPoint rightPoint leftXY rightXY }
  exact _root_.map_sum F f Finset.univ

/-- A lifted modular row operation sends the mixed displacement to the same
integer linear combination of the original displacements. -/
theorem wooleyNormalFormCombination_mixed_displacement
    {I J : Type*} {k q R S : ℕ} (phi : WooleyPolynomialSystem k)
    (G : Matrix (Fin k) (Fin k) (ZMod q)) (i : Fin k)
    (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J) :
    wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (wooleyNormalFormCombination phi q G i) =
      ∑ j : Fin k, wooleyZModMatrixIntLift G i j *
        wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
          leftXY rightXY (phi j) := by
  unfold wooleyNormalFormCombination
  rw [wooleyIntegerMixedPolynomialDisplacement_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact wooleyIntegerMixedPolynomialDisplacement_C_mul
    R S leftPoint rightPoint leftXY rightXY _ _

/-- Divisibility of the source mixed displacement is inherited by every
lifted row combination. -/
theorem wooleyNormalFormCombination_mixed_displacement_dvd
    {I J : Type*} {k p B R S : ℕ} (phi : WooleyPolynomialSystem k)
    (G : Matrix (Fin k) (Fin k) (ZMod (p ^ B))) (i : Fin k)
    (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (hdiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (phi j)) :
    (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (wooleyNormalFormCombination phi (p ^ B) G i) := by
  rw [wooleyNormalFormCombination_mixed_displacement]
  apply dvd_sum
  intro j hj
  exact dvd_mul_of_dvd_right (hdiv j) _

/-- The exact normal-form equality therefore transfers the genuine source
mixed congruence to the tail-only system used in (7.7). -/
theorem wooleyTailNormalChange_mixed_displacement_dvd
    {I J : Type*} {k p c B R S : ℕ} (phi : WooleyPolynomialSystem k)
    (G : Matrix (Fin k) (Fin k) (ZMod (p ^ B)))
    (psi Error : WooleyPolynomialSystem k)
    (hchange : ∀ i : Fin k,
      wooleyNormalFormCombination phi (p ^ B) G i =
        C ((wooleyNormalFormCombination phi (p ^ B) G i).coeff 0) +
          wooleySection7NormalSystem k p c psi i +
          C ((p : ℤ) ^ B) * Error i)
    (leftPoint : I → ℤ) (rightPoint : J → ℤ)
    (leftXY : WooleyFiniteTuple R I × WooleyFiniteTuple R I)
    (rightXY : WooleyFiniteTuple S J × WooleyFiniteTuple S J)
    (hdiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (phi j)) (i : Fin k) :
    (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
        leftXY rightXY (wooleySection7NormalSystem k p c psi i) := by
  have hW := wooleyNormalFormCombination_mixed_displacement_dvd
    phi G i leftPoint rightPoint leftXY rightXY hdiv
  have hrel := congrArg
    (wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
      leftXY rightXY) (hchange i)
  rw [wooleyIntegerMixedPolynomialDisplacement_add,
    wooleyIntegerMixedPolynomialDisplacement_add,
    wooleyIntegerMixedPolynomialDisplacement_C,
    wooleyIntegerMixedPolynomialDisplacement_C_mul] at hrel
  have herror : (p : ℤ) ^ B ∣
      (p : ℤ) ^ B *
        wooleyIntegerMixedPolynomialDisplacement R S leftPoint rightPoint
          leftXY rightXY (Error i) := dvd_mul_right _ _
  rw [hrel] at hW
  have hsub := dvd_sub hW herror
  simpa only [zero_add, add_sub_cancel_right] using hsub

/-- Fourier system on the translated left progression for an arbitrary
source polynomial system. -/
def wooleySection7LeftFourierSystemOf {k : ℕ}
    (phi : WooleyPolynomialSystem k) (p a : ℕ) (h : ℤ) :
    WooleyPolynomialSystem k :=
  wooleyAffinePolynomialSystem phi (p ^ a) h

/-- Negated Fourier system on the right progression for an arbitrary source
polynomial system. -/
def wooleySection7RightFourierSystemOf {k : ℕ}
    (phi : WooleyPolynomialSystem k) (p b : ℕ) :
    WooleyPolynomialSystem k := fun j =>
  -(wooleyAffinePolynomialSystem phi (p ^ b) 0 j)

/-- The arbitrary-system Fourier displacement is exactly the reduction of
the corresponding integral left-minus-right displacement. -/
theorem wooleySection7OriginalDisplacementOf_eq_intCast
    {k p a b B R S : ℕ} (phi : WooleyPolynomialSystem k) (h : ℤ)
    (left right : WooleySourceSequence)
    (omega : WooleySourceMixedTuple R S left right) (j : Fin k) :
    wooleyEquation717OriginalDisplacement
        (wooleySection7LeftFourierSystemOf phi p a h)
        (wooleySection7RightFourierSystemOf phi p b)
        (p ^ B) R S left right omega j =
      ((wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + h)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        omega.1 omega.2 (phi j) : ℤ) : ZMod (p ^ B)) := by
  simp [wooleyEquation717OriginalDisplacement,
    wooleySourceTuplePolynomialDisplacement, wooleyTupleDisplacement,
    wooleyIntegerMixedPolynomialDisplacement,
    wooleyIntegerTupleDisplacement, wooleyPolynomialValue,
    wooleySection7LeftFourierSystemOf,
    wooleySection7RightFourierSystemOf,
    wooleyAffinePolynomialSystem_eval]
  ring

/-- Equation (7.17) for every source `p^c`-spaced system.  This theorem
discharges the paper's “no loss of generality” change to (7.7), transfers the
actual mixed congruence through that integral change, and only then invokes
the determinant/valuation construction of the uniformly chosen lower
system. -/
theorem wooley_equation_7_17_spaced_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal h : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : h = omegaVal * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      WooleyEquation717FiniteIdentity
        (wooleySection7LeftFourierSystemOf phi p a h)
        (wooleySection7RightFourierSystemOf phi p b)
        Psi (p ^ B)
        (p ^ wooleySection7BPrimeNat k r a b gamma)
        R S left right := by
  obtain ⟨G, psi, Error, hchange⟩ :=
    hphi.exists_tail_normal_change hc hpPrime.ne_zero
  obtain ⟨Psi, hPsi, hnormalForced⟩ :=
    wooleySection7_exists_uniform_equation_7_12
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal h homega hcop hsep hh psi left right
  refine ⟨Psi, hPsi, ?_⟩
  unfold WooleyEquation717FiniteIdentity
  apply wooley_equation_7_17_tuple
  intro tuple horiginal
  have hdiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + h)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        tuple.1 tuple.2 (phi j) := by
    intro j
    have hj := congrFun horiginal j
    rw [wooleySection7OriginalDisplacementOf_eq_intCast
      phi h left right tuple j] at hj
    simp only [Pi.zero_apply] at hj
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
    norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hj
    exact hj
  have hnormalDiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + h)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        tuple.1 tuple.2 (wooleySection7NormalSystem k p c psi j) := by
    intro j
    exact wooleyTailNormalChange_mixed_displacement_dvd
      phi G psi Error hchange
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + h)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        tuple.1 tuple.2 hdiv j
  apply hnormalForced tuple
  funext j
  rw [wooleySection7OriginalDisplacement_eq_intCast
    psi h left right tuple j]
  simp only [Pi.zero_apply]
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  exact hnormalDiv j

/-- Swapping the positive and negative halves of a tuple pair negates its
integral displacement. -/
theorem wooleyIntegerTupleDisplacement_swap
    {I : Type*} (R : ℕ) (value : I → ℤ)
    (xy : WooleyFiniteTuple R I × WooleyFiniteTuple R I) :
    wooleyIntegerTupleDisplacement R value (xy.2, xy.1) =
      -wooleyIntegerTupleDisplacement R value xy := by
  unfold wooleyIntegerTupleDisplacement
  ring

/-- The positive right-hand Fourier system appearing literally in the mixed
moment before the tuple-pair swap. -/
def wooleySection7RightPositiveFourierSystemOf {k : ℕ}
    (phi : WooleyPolynomialSystem k) (p b : ℕ) :
    WooleyPolynomialSystem k :=
  wooleyAffinePolynomialSystem phi (p ^ b) 0

/-- With positive phases on both moment factors, the original Fourier
displacement is reduction of the sum of the two integral tuple
displacements. -/
theorem wooleySection7PositiveDisplacementOf_eq_intCast
    {k p a b B R S : ℕ} (phi : WooleyPolynomialSystem k) (h : ℤ)
    (left right : WooleySourceSequence)
    (omega : WooleySourceMixedTuple R S left right) (j : Fin k) :
    wooleyEquation717OriginalDisplacement
        (wooleySection7LeftFourierSystemOf phi p a h)
        (wooleySection7RightPositiveFourierSystemOf phi p b)
        (p ^ B) R S left right omega j =
      ((wooleyIntegerTupleDisplacement R
          (fun x : ↑left.support =>
            (phi j).eval ((p : ℤ) ^ a * (x : ℤ) + h)) omega.1 +
        wooleyIntegerTupleDisplacement S
          (fun x : ↑right.support =>
            (phi j).eval ((p : ℤ) ^ b * (x : ℤ))) omega.2 : ℤ) :
        ZMod (p ^ B)) := by
  simp [wooleyEquation717OriginalDisplacement,
    wooleySourceTuplePolynomialDisplacement, wooleyTupleDisplacement,
    wooleyIntegerTupleDisplacement, wooleyPolynomialValue,
    wooleySection7LeftFourierSystemOf,
    wooleySection7RightPositiveFourierSystemOf,
    wooleyAffinePolynomialSystem_eval]

/-- Literal positive-phase equation (7.17).  The right tuple pair is swapped
inside the congruence argument, so the source equality becomes the
left-minus-right form used by the valuation extraction while the displayed
Fourier mean retains the two positive polynomial phases. -/
theorem wooley_equation_7_17_spaced_positive_native
    {k r p c a b B nu R S gamma : ℕ}
    [NeZero (p ^ B)]
    [NeZero (p ^ wooleySection7BPrimeNat k r a b gamma)]
    (hpPrime : p.Prime) (hc : 1 ≤ c) (hr : 1 ≤ r)
    (hrk : r < k) (hkp : k < p)
    (hMB : (k - r + 1) * b ≤ B)
    (hgammaK : gamma * k ≤ a)
    (hBPrime : (nu : ℤ) < wooleySection7BPrimeInt k r a b gamma)
    (omegaVal h : ℤ) (homega : omegaVal ≠ 0)
    (hcop : Nat.Coprime p omegaVal.natAbs)
    (hsep : h = omegaVal * (p : ℤ) ^ gamma) (hh : h ≠ 0)
    (phi : WooleyPolynomialSystem k) (hphi : phi.Spaced p c)
    (left right : WooleySourceSequence) :
    ∃ Psi : WooleyPolynomialSystem r,
      Psi.Spaced p (a - (k - r) * gamma) ∧
      WooleyEquation717FiniteIdentity
        (wooleySection7LeftFourierSystemOf phi p a h)
        (wooleySection7RightPositiveFourierSystemOf phi p b)
        Psi (p ^ B)
        (p ^ wooleySection7BPrimeNat k r a b gamma)
        R S left right := by
  obtain ⟨G, psi, Error, hchange⟩ :=
    hphi.exists_tail_normal_change hc hpPrime.ne_zero
  obtain ⟨Psi, hPsi, hnormalForced⟩ :=
    wooleySection7_exists_uniform_equation_7_12
      hpPrime hc hr hrk hkp hMB hgammaK hBPrime
        omegaVal h homega hcop hsep hh psi left right
  refine ⟨Psi, hPsi, ?_⟩
  unfold WooleyEquation717FiniteIdentity
  apply wooley_equation_7_17_tuple
  intro tuple horiginal
  let swapped : WooleySourceMixedTuple R S left right :=
    (tuple.1, (tuple.2.2, tuple.2.1))
  have hdiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + h)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        swapped.1 swapped.2 (phi j) := by
    intro j
    have hj := congrFun horiginal j
    rw [wooleySection7PositiveDisplacementOf_eq_intCast
      phi h left right tuple j] at hj
    simp only [Pi.zero_apply] at hj
    have hsum : (p : ℤ) ^ B ∣
        wooleyIntegerTupleDisplacement R
            (fun x : ↑left.support =>
              (phi j).eval ((p : ℤ) ^ a * (x : ℤ) + h)) tuple.1 +
          wooleyIntegerTupleDisplacement S
            (fun x : ↑right.support =>
              (phi j).eval ((p : ℤ) ^ b * (x : ℤ))) tuple.2 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hj
      norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hj
      exact hj
    unfold wooleyIntegerMixedPolynomialDisplacement
    dsimp only [swapped]
    rw [wooleyIntegerTupleDisplacement_swap, sub_neg_eq_add]
    exact hsum
  have hnormalDiv : ∀ j : Fin k, (p : ℤ) ^ B ∣
      wooleyIntegerMixedPolynomialDisplacement R S
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + h)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        swapped.1 swapped.2
          (wooleySection7NormalSystem k p c psi j) := by
    intro j
    exact wooleyTailNormalChange_mixed_displacement_dvd
      phi G psi Error hchange
        (fun x : ↑left.support => (p : ℤ) ^ a * (x : ℤ) + h)
        (fun x : ↑right.support => (p : ℤ) ^ b * (x : ℤ))
        swapped.1 swapped.2 hdiv j
  have hnormal : wooleyEquation717OriginalDisplacement
      (wooleySection7LeftFourierSystem k p c a psi h)
      (wooleySection7RightFourierSystem k p c b psi)
      (p ^ B) R S left right swapped = 0 := by
    funext j
    rw [wooleySection7OriginalDisplacement_eq_intCast
      psi h left right swapped j]
    simp only [Pi.zero_apply]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    exact hnormalDiv j
  have hins := hnormalForced swapped hnormal
  simpa only [swapped, wooleyEquation717InsertedDisplacement] using hins

#print axioms wooleyNormalFormPositiveLow_map_eq_monomial
#print axioms wooleyNormalFormPositiveLow_exists_error
#print axioms WooleyPolynomialSystem.Spaced.high_coeff_dvd
#print axioms wooleyNormalFormCombination_high_coeff_dvd
#print axioms wooleyPolynomial_exists_positiveLow_add_scalar_X_tail
#print axioms WooleyPolynomialSystem.Spaced.exists_tail_normal_change
#print axioms wooleyIntegerMixedPolynomialDisplacement_sum
#print axioms wooleyNormalFormCombination_mixed_displacement
#print axioms wooleyTailNormalChange_mixed_displacement_dvd
#print axioms wooleySection7OriginalDisplacementOf_eq_intCast
#print axioms wooley_equation_7_17_spaced_native
#print axioms wooleyIntegerTupleDisplacement_swap
#print axioms wooleySection7PositiveDisplacementOf_eq_intCast
#print axioms wooley_equation_7_17_spaced_positive_native

end

end GafniTao
