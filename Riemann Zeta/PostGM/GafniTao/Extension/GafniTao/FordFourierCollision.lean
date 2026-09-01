import GafniTao.FordVinogradovIntegral

/-!
# A finite torus-collision identity

This file packages the normalized-Haar calculation repeatedly used in
Ford's Section 3.  It is deliberately stated for two genuine finite moment
families: the integral of the product of their squared Weyl sums is exactly
the number of ordered additive collisions between the two families.
-/

open Finset
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace GafniTao

noncomputable section

def fordCharacterSum {k : ℕ} {A : Type*} [Fintype A]
    (M : A → Fin k → ℤ) (α : UnitAddTorus (Fin k)) : ℂ :=
  ∑ a : A, UnitAddTorus.mFourier (M a) α

def FordCharacterCollision {k : ℕ} {A B : Type*}
    (M : A → Fin k → ℤ) (N : B → Fin k → ℤ) :=
  {x : (A × B) × (A × B) // M x.1.1 + N x.1.2 = M x.2.1 + N x.2.2}

instance fordCharacterCollisionFinite
    {k : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (M : A → Fin k → ℤ) (N : B → Fin k → ℤ) :
    Finite (FordCharacterCollision M N) :=
  Finite.of_injective Subtype.val Subtype.val_injective

theorem ford_conj_characterSum {k : ℕ} {A : Type*} [Fintype A]
    (M : A → Fin k → ℤ) (α : UnitAddTorus (Fin k)) :
    conj (fordCharacterSum M α) =
      ∑ a : A, UnitAddTorus.mFourier (-M a) α := by
  unfold fordCharacterSum
  simp only [map_sum, UnitAddTorus.mFourier_neg]

theorem ford_characterSum_norm_sq_complex
    {k : ℕ} {A : Type*} [Fintype A]
    (M : A → Fin k → ℤ) (α : UnitAddTorus (Fin k)) :
    ((‖fordCharacterSum M α‖ ^ 2 : ℝ) : ℂ) =
      ∑ a : A, ∑ a' : A,
        UnitAddTorus.mFourier (M a - M a') α := by
  calc
    ((‖fordCharacterSum M α‖ ^ 2 : ℝ) : ℂ) =
        fordCharacterSum M α * conj (fordCharacterSum M α) := by
      rw [Complex.mul_conj']
      norm_num
    _ = _ := by
      rw [ford_conj_characterSum]
      unfold fordCharacterSum
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro a' ha'
      rw [sub_eq_add_neg, UnitAddTorus.mFourier_add]

theorem ford_two_character_norm_product_complex
    {k : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (M : A → Fin k → ℤ) (N : B → Fin k → ℤ)
    (α : UnitAddTorus (Fin k)) :
    (((‖fordCharacterSum M α‖ ^ 2) *
        (‖fordCharacterSum N α‖ ^ 2) : ℝ) : ℂ) =
      ∑ a : A, ∑ b : B, ∑ a' : A, ∑ b' : B,
        UnitAddTorus.mFourier
          ((M a + N b) - (M a' + N b')) α := by
  calc
    (((‖fordCharacterSum M α‖ ^ 2) *
        (‖fordCharacterSum N α‖ ^ 2) : ℝ) : ℂ) =
      ((‖fordCharacterSum M α‖ ^ 2 : ℝ) : ℂ) *
        ((‖fordCharacterSum N α‖ ^ 2 : ℝ) : ℂ) := by norm_num
    _ = _ := by
      rw [ford_characterSum_norm_sq_complex,
        ford_characterSum_norm_sq_complex, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a' ha'
      apply Finset.sum_congr rfl
      intro b' hb'
      rw [← UnitAddTorus.mFourier_add]
      congr 1
      abel_nf

theorem ford_character_collision_mean_eq
    {k : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (M : A → Fin k → ℤ) (N : B → Fin k → ℤ) :
    ∫ α : UnitAddTorus (Fin k),
        ‖fordCharacterSum M α‖ ^ 2 * ‖fordCharacterSum N α‖ ^ 2
        ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) =
      (Nat.card (FordCharacterCollision M N) : ℝ) := by
  letI : Fintype (FordCharacterCollision M N) := Fintype.ofFinite _
  apply Complex.ofReal_injective
  have hcast :
      (∫ α : UnitAddTorus (Fin k),
          (((‖fordCharacterSum M α‖ ^ 2) *
            (‖fordCharacterSum N α‖ ^ 2) : ℝ) : ℂ)
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)) =
        ((∫ α : UnitAddTorus (Fin k),
          ‖fordCharacterSum M α‖ ^ 2 * ‖fordCharacterSum N α‖ ^ 2
          ∂Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle) : ℝ) : ℂ) :=
    integral_ofReal
  rw [← hcast]
  simp_rw [ford_two_character_norm_product_complex]
  rw [Complex.ofReal_natCast]
  rw [Nat.card_eq_fintype_card]
  unfold FordCharacterCollision
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  let μ : Measure (UnitAddTorus (Fin k)) :=
    Measure.pi (fun _ : Fin k => AddCircle.haarAddCircle)
  have hchar (a : A) (a' : A) (b : B) (b' : B) :
      Integrable (fun α : UnitAddTorus (Fin k) =>
        UnitAddTorus.mFourier ((M a + N b) - (M a' + N b')) α) μ :=
    ford_integrable_mFourier_pi_haar _
  have hlast (a : A) (b : B) (a' : A) : Integrable
      (fun α : UnitAddTorus (Fin k) => ∑ b' : B,
        UnitAddTorus.mFourier ((M a + N b) - (M a' + N b')) α) μ :=
    integrable_finsetSum Finset.univ fun b' _ => hchar a a' b b'
  have hthird (a : A) (b : B) : Integrable
      (fun α : UnitAddTorus (Fin k) => ∑ a' : A, ∑ b' : B,
        UnitAddTorus.mFourier ((M a + N b) - (M a' + N b')) α) μ :=
    integrable_finsetSum Finset.univ fun a' _ => hlast a b a'
  have hsecond (a : A) : Integrable
      (fun α : UnitAddTorus (Fin k) => ∑ b : B, ∑ a' : A, ∑ b' : B,
        UnitAddTorus.mFourier ((M a + N b) - (M a' + N b')) α) μ :=
    integrable_finsetSum Finset.univ fun b _ => hthird a b
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun a _ => hsecond a)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun b _ => hthird a b)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Fintype.sum_prod_type]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun a' _ => hlast a b a')]
  apply Finset.sum_congr rfl
  intro a' ha'
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun b' _ => hchar a a' b b')]
  apply Finset.sum_congr rfl
  intro b' hb'
  rw [ford_integral_mFourier_pi_haar_eq]
  by_cases h : M a + N b = M a' + N b'
  · simp [h]
  · have hz : (M a + N b) - (M a' + N b') ≠ 0 := by
      exact fun hz => h (sub_eq_zero.mp hz)
    simp [h, hz]

#print axioms ford_character_collision_mean_eq

end

end GafniTao
