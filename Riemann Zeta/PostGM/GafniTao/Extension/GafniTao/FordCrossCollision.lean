import GafniTao.FordS4Diagonal

/-!
# Cross-family torus collision identity

Ford's boundary argument compares two character families of different
arities.  The normalized torus integral below counts their exact cross
collisions; this is the asymmetric companion to
`ford_character_collision_mean_eq`.
-/

open Finset
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace GafniTao

noncomputable section

def FordCrossCharacterCollision {k : ℕ} {A B : Type*}
    (M : A → Fin k → ℤ) (N : B → Fin k → ℤ) :=
  {x : A × B // M x.1 = N x.2}

instance fordCrossCharacterCollisionFinite
    {k : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (M : A → Fin k → ℤ) (N : B → Fin k → ℤ) :
    Finite (FordCrossCharacterCollision M N) :=
  Finite.of_injective Subtype.val Subtype.val_injective

theorem ford_cross_character_product_complex
    {k : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (M : A → Fin k → ℤ) (N : B → Fin k → ℤ)
    (α : UnitAddTorus (Fin k)) :
    fordCharacterSum M α * conj (fordCharacterSum N α) =
      ∑ a : A, ∑ b : B,
        UnitAddTorus.mFourier (M a - N b) α := by
  rw [ford_conj_characterSum]
  unfold fordCharacterSum
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← UnitAddTorus.mFourier_add]
  congr 1

theorem ford_cross_character_mean_eq
    {k : ℕ} {A B : Type*} [Fintype A] [Fintype B]
    (M : A → Fin k → ℤ) (N : B → Fin k → ℤ) :
    ∫ α : UnitAddTorus (Fin k),
        fordCharacterSum M α * conj (fordCharacterSum N α)
        ∂fordTorusMeasure k =
      ((Nat.card (FordCrossCharacterCollision M N) : ℝ) : ℂ) := by
  letI : Fintype (FordCrossCharacterCollision M N) := Fintype.ofFinite _
  simp_rw [ford_cross_character_product_complex]
  rw [MeasureTheory.integral_finsetSum]
  · rw [Nat.card_eq_fintype_card]
    unfold FordCrossCharacterCollision
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones]
    push_cast
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a ha
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [ford_integral_mFourier_pi_haar_eq]
      by_cases hab : M a = N b
      · simp [hab]
      · have hne : M a - N b ≠ 0 := fun hzero ↦ hab (sub_eq_zero.mp hzero)
        simp [hab, hne]
    · intro b hb
      exact ford_integrable_mFourier_pi_haar _
  · intro a ha
    exact integrable_finsetSum Finset.univ fun b _ ↦
      ford_integrable_mFourier_pi_haar _

#print axioms ford_cross_character_mean_eq

end

end GafniTao
