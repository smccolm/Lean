import GafniTao.FordKMaximal
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Ford Lemma 3.2: the unrestricted `K` Fourier identity

This file gives the exact normalized-torus realization of Ford's complete
count `K_s(P,Q;Ψ;q)`.  The one-variable polynomial and power sums are kept
separate, since the repeated-coordinate argument uses the polynomial sum at
both `α` and `2α`.
-/

open Finset
open scoped BigOperators
open MeasureTheory

namespace GafniTao

noncomputable section

def fordFamilyMoment {k : ℕ} {I A : Type*} [Fintype I]
    (M : A → Fin k → ℤ) (u : I → A) : Fin k → ℤ :=
  ∑ i : I, M (u i)

theorem ford_mFourier_genericFamilyMoment
    {k : ℕ} {I A : Type*} [Fintype I]
    (M : A → Fin k → ℤ) (u : I → A)
    (a : UnitAddTorus (Fin k)) :
    UnitAddTorus.mFourier (fordFamilyMoment M u) a =
      ∏ i : I, UnitAddTorus.mFourier (M (u i)) a := by
  classical
  unfold fordFamilyMoment
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp [UnitAddTorus.mFourier_zero]
  | @insert i t hi ih =>
      rw [Finset.sum_insert hi, UnitAddTorus.mFourier_add,
        Finset.prod_insert hi, ih]

theorem fordCharacterSum_familyMoment_eq_pow_card
    {k : ℕ} {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
    (M : A → Fin k → ℤ) (a : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordFamilyMoment M : (I → A) → Fin k → ℤ) a =
      fordCharacterSum M a ^ Fintype.card I := by
  classical
  let eI := Fintype.equivFin I
  let eFun : (I → A) ≃ (Fin (Fintype.card I) → A) :=
    Equiv.arrowCongr eI (Equiv.refl _)
  have hmoment : ∀ u : I → A,
      fordFamilyMoment M u = fordFamilyMoment M (eFun u) := by
    intro u
    funext j
    simp only [fordFamilyMoment, Finset.sum_apply]
    change (∑ x : I, M (u x) j) =
      ∑ x : Fin (Fintype.card I), M (u (eI.symm x)) j
    simpa using eI.sum_comp
      (fun x : Fin (Fintype.card I) ↦ M (u (eI.symm x)) j)
  calc
    fordCharacterSum
        (fordFamilyMoment M : (I → A) → Fin k → ℤ) a =
        ∑ u : Fin (Fintype.card I) → A,
          UnitAddTorus.mFourier (fordFamilyMoment M u) a := by
      unfold fordCharacterSum
      exact Fintype.sum_equiv eFun _ _ fun u ↦
        congrArg (fun V ↦ UnitAddTorus.mFourier V a) (hmoment u)
    _ = ∑ u : Fin (Fintype.card I) → A,
          ∏ i : Fin (Fintype.card I),
            UnitAddTorus.mFourier (M (u i)) a := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [ford_mFourier_genericFamilyMoment]
    _ = fordCharacterSum M a ^ Fintype.card I := by
      unfold fordCharacterSum
      rw [Fintype.sum_pow]

def fordPolynomialSingleMoment
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (x : Fin P) : Fin k → ℤ :=
  fun j ↦ (Ψ.poly j).eval (((x : ℕ) + 1 : ℕ) : ℤ)

def fordPowerSingleMoment (k Q q : ℕ) (x : Fin Q) : Fin k → ℤ :=
  fun j ↦ ((q ^ ((j : ℕ) + 1) *
    ((x : ℕ) + 1) ^ ((j : ℕ) + 1) : ℕ) : ℤ)

theorem fordPolynomialMoment_eq_family
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (z : FordBox k P) :
    fordPolynomialMoment Ψ z =
      fordFamilyMoment (fordPolynomialSingleMoment Ψ) z := by
  funext j
  simp [fordPolynomialMoment, fordPolynomialSumInt, fordFamilyMoment,
    fordPolynomialSingleMoment, fordBoxValue]

theorem fordS3BoxMoment_eq_family
    {k s Q q : ℕ} (x : FordBox s Q) :
    fordS3BoxMoment (k := k) q x =
      fordFamilyMoment (fordPowerSingleMoment k Q q) x := by
  funext j
  simp [fordS3BoxMoment, fordFamilyMoment, fordPowerSingleMoment]

def fordPolynomialFullWeylSum
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (a : UnitAddTorus (Fin k)) : ℂ :=
  fordCharacterSum (fordPolynomialSingleMoment (P := P) Ψ) a

def fordPowerFullWeylSum (k Q q : ℕ)
    (a : UnitAddTorus (Fin k)) : ℂ :=
  fordCharacterSum (fordPowerSingleMoment k Q q) a

theorem fordPolynomialBoxCharacterSum_eq_pow
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (a : UnitAddTorus (Fin k)) :
    fordCharacterSum (fordPolynomialMoment (P := P) Ψ) a =
      fordPolynomialFullWeylSum (P := P) Ψ a ^ k := by
  calc
    fordCharacterSum (fordPolynomialMoment (P := P) Ψ) a =
        fordCharacterSum
          (fordFamilyMoment (fordPolynomialSingleMoment (P := P) Ψ) :
            FordBox k P → Fin k → ℤ) a := by
      unfold fordCharacterSum
      apply Finset.sum_congr rfl
      intro z hz
      rw [fordPolynomialMoment_eq_family]
    _ = _ := fordCharacterSum_familyMoment_eq_pow_card
      (fordPolynomialSingleMoment (P := P) Ψ) a
      |>.trans (by simp [fordPolynomialFullWeylSum])

theorem fordPowerBoxCharacterSum_eq_pow
    (k s Q q : ℕ) (a : UnitAddTorus (Fin k)) :
    fordCharacterSum
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) a =
      fordPowerFullWeylSum k Q q a ^ s := by
  calc
    fordCharacterSum
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) a =
        fordCharacterSum
          (fordFamilyMoment (fordPowerSingleMoment k Q q) :
            FordBox s Q → Fin k → ℤ) a := by
      unfold fordCharacterSum
      apply Finset.sum_congr rfl
      intro x hx
      rw [fordS3BoxMoment_eq_family]
    _ = _ := fordCharacterSum_familyMoment_eq_pow_card
      (fordPowerSingleMoment k Q q) a
      |>.trans (by simp [fordPowerFullWeylSum])

def fordKCollisionEquiv
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    FordKSolution Ψ s P Q q ≃
      FordCharacterCollision
        (fordPolynomialMoment (P := P) Ψ)
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ) where
  toFun u := ⟨((u.1.1.1, u.1.2.1), (u.1.1.2, u.1.2.2)), by
    funext j
    have h := u.2 j
    unfold fordPolynomialDifference fordPowerDifference at h
    change fordPolynomialMoment Ψ u.1.1.1 j +
        fordS3BoxMoment q u.1.2.1 j =
      fordPolynomialMoment Ψ u.1.1.2 j +
        fordS3BoxMoment q u.1.2.2 j
    simp only [fordPolynomialMoment, fordS3BoxMoment,
      fordPolynomialSumInt, fordBoxValue, Finset.sum_sub_distrib] at h ⊢
    push_cast at h ⊢
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    linear_combination h⟩
  invFun u := ⟨((u.1.1.1, u.1.2.1), (u.1.1.2, u.1.2.2)), by
    intro j
    have h := congrFun u.2 j
    unfold fordPolynomialDifference fordPowerDifference
    change fordPolynomialMoment Ψ u.1.1.1 j +
        fordS3BoxMoment q u.1.1.2 j =
      fordPolynomialMoment Ψ u.1.2.1 j +
        fordS3BoxMoment q u.1.2.2 j at h
    simp only [fordPolynomialMoment, fordS3BoxMoment,
      fordPolynomialSumInt, fordBoxValue, Finset.sum_sub_distrib] at h ⊢
    push_cast at h ⊢
    rw [← Finset.mul_sum, ← Finset.mul_sum] at h
    linear_combination h⟩
  left_inv u := by rfl
  right_inv u := by rfl

theorem fordKCount_eq_characterCollision
    {k d T s P Q q : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    fordKCount Ψ s P Q q =
      Nat.card (FordCharacterCollision
        (fordPolynomialMoment (P := P) Ψ)
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)) := by
  unfold fordKCount
  calc
    Fintype.card {v : FordKVariables k s P Q // FordKEquation Ψ q v} =
        Nat.card (FordKSolution Ψ s P Q q) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card (FordCharacterCollision
        (fordPolynomialMoment (P := P) Ψ)
        (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)) :=
      Nat.card_congr (fordKCollisionEquiv Ψ)

def fordKFourier
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) : ℝ :=
  ∫ a : UnitAddTorus (Fin k),
    ‖fordPolynomialFullWeylSum (P := P) Ψ a‖ ^ (2 * k) *
      ‖fordPowerFullWeylSum k Q q a‖ ^ (2 * s)
    ∂fordTorusMeasure k

theorem fordKFourier_eq_count
    {k d T : ℕ} (Ψ : FordIntegerPolynomialSystem k d T)
    (s P Q q : ℕ) :
    fordKFourier Ψ s P Q q = (fordKCount Ψ s P Q q : ℝ) := by
  rw [fordKCount_eq_characterCollision]
  rw [← ford_character_collision_mean_eq
    (fordPolynomialMoment (P := P) Ψ)
    (fordS3BoxMoment (k := k) q : FordBox s Q → Fin k → ℤ)]
  unfold fordKFourier
  apply integral_congr_ae
  filter_upwards [] with a
  rw [fordPolynomialBoxCharacterSum_eq_pow,
    fordPowerBoxCharacterSum_eq_pow]
  simp only [norm_pow, ← pow_mul]
  congr 2 <;> omega

theorem continuous_fordPolynomialFullWeylSum
    {k d T P : ℕ} (Ψ : FordIntegerPolynomialSystem k d T) :
    Continuous (fordPolynomialFullWeylSum (P := P) Ψ) := by
  unfold fordPolynomialFullWeylSum fordCharacterSum
  fun_prop

theorem continuous_fordPowerFullWeylSum (k Q q : ℕ) :
    Continuous (fordPowerFullWeylSum k Q q) := by
  unfold fordPowerFullWeylSum fordCharacterSum
  fun_prop

#print axioms fordKFourier_eq_count
#print axioms fordCharacterSum_familyMoment_eq_pow_card

end

end GafniTao
