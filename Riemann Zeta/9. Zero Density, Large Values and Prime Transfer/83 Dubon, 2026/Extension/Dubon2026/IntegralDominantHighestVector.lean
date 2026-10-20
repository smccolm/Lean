import Dubon2026.IntegralWeightLongestPermutation

/-! An actual highest-weight vector in the literal integral induction.
Translate the proved dominant vector by the original longest permutation.
Its exact right upper-Borel character is the original weight, over every
coefficient algebra, and evaluation at the longest matrix is one.
This discharges existence of the source highest vector. Uniqueness of its
line, generation and irreducibility remain separate obligations in the
highest-weight identification needed by BLGG Section 3.2 / Theorem 2.6.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] {n : ℕ}

/-- The actual highest regular vector is the longest right translate of the original dominant minor vector. -/
def integralDominantHighestRegular (lam : Fin (n + 1) → ℤ) :
    GeneralLinearRegularFunctions R (n + 1) :=
  generalLinearRegularRightTranslate (integralWeightLongest R (n + 1))
    (integralDominantInducedVector R lam)

/-- The longest translate still satisfies the literal source defining covariance. -/
theorem integralDominantHighestRegular_mem (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam) :
    integralDominantHighestRegular R lam ∈ generalLinearIntegralInducedSubmodule R (n + 1) lam :=
  generalLinearIntegralInducedSubmodule_stable R (n + 1) lam _
    (integralDominantInducedVector_mem R lam hlam)

/-- Evaluating the original highest regular vector is exactly evaluation of the original dominant vector after the longest matrix. -/
theorem integralDominantHighestRegular_eval
    {A : Type u} [CommRing A] [Algebra R A] (lam : Fin (n + 1) → ℤ)
    (g : GeneralLinearGroup (Fin (n + 1)) A) :
    generalLinearRegularEval g (integralDominantHighestRegular R lam) =
      generalLinearRegularEval (g * integralWeightLongest A (n + 1))
        (integralDominantInducedVector R lam) := by
  have h := AlgHom.congr_fun
    (generalLinearRegularEval_rightTranslate (integralWeightLongest R (n + 1)) g)
    (integralDominantInducedVector R lam)
  simpa only [AlgHom.comp_apply, integralWeightLongest_map] using h

/-- The actual highest regular vector evaluates to one at the actual longest matrix. -/
theorem integralDominantHighestRegular_longest (lam : Fin (n + 1) → ℤ) :
    generalLinearRegularEval (integralWeightLongest R (n + 1))
      (integralDominantHighestRegular R lam) = 1 := by
  rw [integralDominantHighestRegular_eval, integralWeightLongest_mul_self,
    integralDominantInducedVector_one]

/-- The original highest vector has the precise highest-weight upper-Borel character on the right over every original coefficient algebra. -/
theorem integralDominantHighestRegular_right_borel
    {A : Type u} [CommRing A] [Algebra R A] (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam)
    (g : GeneralLinearGroup (Fin (n + 1)) A) (b : generalLinearBorel A (n + 1)) :
    generalLinearRegularEval (g * b.val) (integralDominantHighestRegular R lam) =
      ((∏ i : Fin (n + 1), generalLinearBorelDiagonalUnit b i ^ lam i : Aˣ) : A) *
        generalLinearRegularEval g (integralDominantHighestRegular R lam) := by
  have he : g * b.val * integralWeightLongest A (n + 1) =
      (g * integralWeightLongest A (n + 1)) *
        integralWeightTranspose (integralWeightLongestBorel A (n + 1) b).val := by
    change g * b.val * integralWeightLongest A (n + 1) =
      (g * integralWeightLongest A (n + 1)) * integralWeightTranspose
        (integralWeightTranspose (integralWeightLongest A (n + 1) * b.val *
          integralWeightLongest A (n + 1)))
    rw [integralWeightTranspose_involutive]
    symm
    calc
      _ = g * (integralWeightLongest A (n + 1) * integralWeightLongest A (n + 1)) *
          b.val * integralWeightLongest A (n + 1) := by simp only [mul_assoc]
      _ = _ := by rw [integralWeightLongest_mul_self, mul_one]
  simp only [integralDominantHighestRegular_eval]
  rw [he, integralDominantInducedVector_right_transpose_borel lam hlam,
    integralWeightLongestBorel_character]

/-- The literal source induced module contains the constructed original highest vector. -/
def integralDominantHighestVector (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam) :
    generalLinearIntegralInducedSubmodule R (n + 1) lam :=
  ⟨integralDominantHighestRegular R lam, integralDominantHighestRegular_mem R lam hlam⟩

/-- The constructed original highest vector is nonzero, without assuming irreducibility or highest-weight classification. -/
theorem integralDominantHighestVector_ne_zero [Nontrivial R]
    (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam) : integralDominantHighestVector R lam hlam ≠ 0 := by
  intro h
  have he := integralDominantHighestRegular_longest R lam
  have hz : integralDominantHighestRegular R lam = 0 := congrArg Subtype.val h
  rw [hz, map_zero] at he
  exact zero_ne_one he

/-- The actual source induction has a nonzero original vector of the precise highest weight over every coefficient algebra. -/
theorem integralDominantInduced_exists_highestVector [Nontrivial R]
    (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam) :
    ∃ v : generalLinearIntegralInducedSubmodule R (n + 1) lam, v ≠ 0 ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A]
        (g : GeneralLinearGroup (Fin (n + 1)) A) (b : generalLinearBorel A (n + 1)),
        generalLinearRegularEval (g * b.val) v.val =
          ((∏ i : Fin (n + 1), generalLinearBorelDiagonalUnit b i ^ lam i : Aˣ) : A) *
            generalLinearRegularEval g v.val := by
  refine ⟨integralDominantHighestVector R lam hlam, integralDominantHighestVector_ne_zero R lam hlam, ?_⟩
  intro A _ _ g b
  exact integralDominantHighestRegular_right_borel R lam hlam g b

end
end Dubon2026
