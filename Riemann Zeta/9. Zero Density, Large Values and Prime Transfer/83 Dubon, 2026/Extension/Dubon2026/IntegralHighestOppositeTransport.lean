import Dubon2026.IntegralHighestWeightAction

/-! Transport the actual highest-character condition to the opposite line.
All identities retain the original longest matrix, original coefficient
algebras, and the original right-translation action.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] (n : ℕ)

/-- The exact highest character of the reversed Borel matrix is the original reversed-weight character. -/
theorem integralWeightLongestBorel_highest_character
    (lam : Fin n → ℤ) (b : generalLinearBorel R n) :
    (∏ i : Fin n, generalLinearBorelDiagonalUnit (integralWeightLongestBorel R n b) i ^ lam i) =
      generalLinearBorelWeight lam b := by
  simp only [integralWeightLongestBorel_diagonal, generalLinearBorelWeight_apply]
  exact Fintype.prod_equiv Fin.revPerm _ _ (fun i => by simp)

/-- The original longest matrix interchanges the exact lower-Borel matrix and its actual upper transform. -/
theorem integralWeightLongestBorel_transport (b : generalLinearBorel R n) :
    integralWeightTranspose b.val * integralWeightLongest R n =
      integralWeightLongest R n * (integralWeightLongestBorel R n b).val := by
  have hc : integralWeightLongest R n * (integralWeightLongestBorel R n b).val *
      integralWeightLongest R n = integralWeightTranspose b.val := by
    apply Units.ext
    ext i j
    rw [integralWeightLongest_conjugate]
    change (integralWeightLongest R n * b.val * integralWeightLongest R n).val j.rev i.rev =
      b.val.val j i
    rw [integralWeightLongest_conjugate, Fin.rev_rev, Fin.rev_rev]
  rw [← hc, mul_assoc, integralWeightLongest_mul_self, mul_one]

/-- Original right translation by the longest matrix takes the all-algebra highest-character condition to the exact opposite-character condition. -/
theorem integralWeightLongestTranslate_opposite (lam : Fin n → ℤ)
    (q : GeneralLinearRegularFunctions R n)
    (hq : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n),
        generalLinearRegularEval (g * b.val) q =
          ((∏ i : Fin n, generalLinearBorelDiagonalUnit b i ^ lam i : Aˣ) : A) *
            generalLinearRegularEval g q)
    (A : Type u) [CommRing A] [Algebra R A]
    (g : GeneralLinearGroup (Fin n) A) (b : generalLinearBorel A n) :
    generalLinearRegularEval (g * integralWeightTranspose b.val)
        (generalLinearRegularRightTranslate (integralWeightLongest R n) q) =
      (generalLinearBorelWeight lam b : A) *
        generalLinearRegularEval g
          (generalLinearRegularRightTranslate (integralWeightLongest R n) q) := by
  have hl := AlgHom.congr_fun
    (generalLinearRegularEval_rightTranslate (integralWeightLongest R n)
      (g * integralWeightTranspose b.val)) q
  have hr := AlgHom.congr_fun
    (generalLinearRegularEval_rightTranslate (integralWeightLongest R n) g) q
  simp only [AlgHom.comp_apply, integralWeightLongest_map] at hl hr
  rw [hl, hr, mul_assoc, integralWeightLongestBorel_transport, ← mul_assoc,
    hq A (g * integralWeightLongest A n) (integralWeightLongestBorel A n b),
    integralWeightLongestBorel_highest_character]

end
end Dubon2026
