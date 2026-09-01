import GafniTao.FordSecondHolder
import GafniTao.FordVinogradovIntegral

/-!
# Ford Lemma 5.1: tuple and representation fibers

This file expands the `r`-th power in Ford's first Hölder step over the
literal tuples `1 ≤ aᵢ ≤ M`, before regrouping those tuples by their complete
Vinogradov power vector.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem ford_sum_Icc_one_eq_fin
    {R : Type*} [AddCommMonoid R] (M : ℕ) (f : ℕ → R) :
    (∑ a ∈ Finset.Icc 1 M, f a) = ∑ a : Fin M, f ((a : ℕ) + 1) := by
  have hset : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
    ext a
    simp
  rw [hset, Finset.sum_Ico_eq_sum_range]
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n + 1)) M]
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  omega

theorem fordAdditiveCharacter_add (x y : ℝ) :
    fordAdditiveCharacter (x + y) =
      fordAdditiveCharacter x * fordAdditiveCharacter y := by
  unfold fordAdditiveCharacter
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fordAdditiveCharacter_sum
    {ι : Type*} (S : Finset ι) (f : ι → ℝ) :
    fordAdditiveCharacter (∑ i ∈ S, f i) =
      ∏ i ∈ S, fordAdditiveCharacter (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fordAdditiveCharacter]
  | @insert a S ha ih =>
      simp only [sum_insert ha, prod_insert ha]
      rw [fordAdditiveCharacter_add, ih]

/-- The exact tuple expansion of the powered inner sum in Ford (5.3). -/
theorem fordLemma51InnerSum_pow_eq_tuple_sum
    (k M r : ℕ) (t z : ℝ) (b : ℕ) :
    fordLemma51InnerSum k M t z b ^ r =
      ∑ x : FordVinogradovTuple r M,
        ∏ i : Fin r,
          fordAdditiveCharacter
            (fordTaylorPolynomialPhase k t z
              ((((x i : ℕ) + 1) * b : ℕ) : ℝ)) := by
  unfold fordLemma51InnerSum
  rw [ford_sum_Icc_one_eq_fin]
  exact Fintype.sum_pow _ r

/-- Ford's phase `γ₁bc₁ + ⋯ + γₖbᵏcₖ` on a power-vector fiber. -/
def fordLemma51FiberPhase
    (k : ℕ) (t z : ℝ) (b : ℕ) (c : Fin k → ℤ) : ℝ :=
  ∑ j : Fin k,
    fordTaylorGamma t z (j : ℕ) * (b : ℝ) ^ ((j : ℕ) + 1) * (c j : ℝ)

theorem fordLemma51_tuple_phase_eq_fiber_phase
    (k M r : ℕ) (t z : ℝ) (b : ℕ) (x : FordVinogradovTuple r M) :
    (∑ i : Fin r,
      fordTaylorPolynomialPhase k t z
        ((((x i : ℕ) + 1) * b : ℕ) : ℝ)) =
      fordLemma51FiberPhase k t z b (fordVinogradovPowerVector r k M x) := by
  unfold fordTaylorPolynomialPhase fordLemma51FiberPhase fordVinogradovPowerVector
  push_cast
  simp_rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_pow]
  ring

theorem fordLemma51_tuple_character_eq_fiber_character
    (k M r : ℕ) (t z : ℝ) (b : ℕ) (x : FordVinogradovTuple r M) :
    (∏ i : Fin r,
      fordAdditiveCharacter
        (fordTaylorPolynomialPhase k t z
          ((((x i : ℕ) + 1) * b : ℕ) : ℝ))) =
      fordAdditiveCharacter
        (fordLemma51FiberPhase k t z b (fordVinogradovPowerVector r k M x)) := by
  rw [← fordAdditiveCharacter_sum Finset.univ]
  congr 1
  exact fordLemma51_tuple_phase_eq_fiber_phase k M r t z b x

/-- The finite set of power vectors attained by source tuples. -/
def fordLemma51FiberSet (r k M : ℕ) : Finset (Fin k → ℤ) :=
  (Finset.univ : Finset (FordVinogradovTuple r M)).image
    (fordVinogradovPowerVector r k M)

/-- Ford's representation number `n(c)`. -/
def fordLemma51RepresentationCount (r k M : ℕ) (c : Fin k → ℤ) : ℕ :=
  fordRepresentationFiberCount
    (Finset.univ : Finset (FordVinogradovTuple r M))
    (fordVinogradovPowerVector r k M) c

theorem fordLemma51_tuple_sum_eq_fiber_sum
    (k M r : ℕ) (t z : ℝ) (b : ℕ) :
    (∑ x : FordVinogradovTuple r M,
      fordAdditiveCharacter
        (fordLemma51FiberPhase k t z b (fordVinogradovPowerVector r k M x))) =
      ∑ c ∈ fordLemma51FiberSet r k M,
        (fordLemma51RepresentationCount r k M c : ℂ) *
          fordAdditiveCharacter (fordLemma51FiberPhase k t z b c) := by
  classical
  let B : Finset (FordVinogradovTuple r M) := Finset.univ
  let F : FordVinogradovTuple r M → (Fin k → ℤ) :=
    fordVinogradovPowerVector r k M
  let q : (Fin k → ℤ) → ℂ := fun c =>
    (fordRepresentationFiberCount B F c : ℂ) *
      fordAdditiveCharacter (fordLemma51FiberPhase k t z b c)
  let h : FordVinogradovTuple r M → ℂ := fun x =>
    fordAdditiveCharacter (fordLemma51FiberPhase k t z b (F x))
  have hfiber (x : FordVinogradovTuple r M) (hx : x ∈ B) :
      q (F x) = ∑ y ∈ B with F y = F x, h y := by
    calc
      q (F x) =
          ((B.filter fun y => F y = F x).card : ℂ) * h x := by
        rfl
      _ = ∑ _y ∈ B.filter (fun y => F y = F x), h x := by simp
      _ = ∑ y ∈ B.filter (fun y => F y = F x), h y := by
        apply Finset.sum_congr rfl
        intro y hy
        have hFy : F y = F x := (Finset.mem_filter.mp hy).2
        simp only [h, hFy]
  have hgroup := Finset.sum_image' h hfiber
  simpa only [B, F, q, h, fordLemma51FiberSet,
    fordLemma51RepresentationCount] using hgroup.symm

theorem fordLemma51InnerSum_pow_eq_fiber_sum
    (k M r : ℕ) (t z : ℝ) (b : ℕ) :
    fordLemma51InnerSum k M t z b ^ r =
      ∑ c ∈ fordLemma51FiberSet r k M,
        (fordLemma51RepresentationCount r k M c : ℂ) *
          fordAdditiveCharacter (fordLemma51FiberPhase k t z b c) := by
  rw [fordLemma51InnerSum_pow_eq_tuple_sum]
  calc
    (∑ x : FordVinogradovTuple r M,
      ∏ i : Fin r,
        fordAdditiveCharacter
          (fordTaylorPolynomialPhase k t z
            ((((x i : ℕ) + 1) * b : ℕ) : ℝ))) =
        ∑ x : FordVinogradovTuple r M,
          fordAdditiveCharacter
            (fordLemma51FiberPhase k t z b
              (fordVinogradovPowerVector r k M x)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact fordLemma51_tuple_character_eq_fiber_character k M r t z b x
    _ = _ := fordLemma51_tuple_sum_eq_fiber_sum k M r t z b

theorem fordLemma51_sum_representationCount (r k M : ℕ) :
    (∑ c ∈ fordLemma51FiberSet r k M,
      fordLemma51RepresentationCount r k M c) = M ^ r := by
  classical
  calc
    (∑ c ∈ fordLemma51FiberSet r k M,
        fordLemma51RepresentationCount r k M c) =
        (Finset.univ : Finset (FordVinogradovTuple r M)).card := by
      symm
      apply Finset.card_eq_sum_card_fiberwise
      intro x hx
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    _ = M ^ r := card_fordVinogradovTuple_univ r M

theorem fordLemma51_sum_representationCount_sq (r k M : ℕ) :
    (∑ c ∈ fordLemma51FiberSet r k M,
      fordLemma51RepresentationCount r k M c ^ 2) =
      fordVinogradovMomentNat r k M := by
  classical
  simpa only [fordLemma51FiberSet, fordLemma51RepresentationCount,
    fordVinogradovMomentNat, fordVinogradovShiftedCountNat] using
      (fordRepresentationCount_zero_eq_sum_fiber_sq
        (Finset.univ : Finset (FordVinogradovTuple r M))
        (fordVinogradovPowerVector r k M)).symm

#print axioms ford_sum_Icc_one_eq_fin
#print axioms fordAdditiveCharacter_sum
#print axioms fordLemma51InnerSum_pow_eq_tuple_sum
#print axioms fordLemma51_tuple_phase_eq_fiber_phase
#print axioms fordLemma51_tuple_character_eq_fiber_character
#print axioms fordLemma51_tuple_sum_eq_fiber_sum
#print axioms fordLemma51InnerSum_pow_eq_fiber_sum
#print axioms fordLemma51_sum_representationCount
#print axioms fordLemma51_sum_representationCount_sq

end

end GafniTao
