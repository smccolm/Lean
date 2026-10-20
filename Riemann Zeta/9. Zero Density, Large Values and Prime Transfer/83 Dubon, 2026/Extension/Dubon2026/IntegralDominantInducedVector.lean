import Dubon2026.IntegralDominantWeightDecomposition
import Dubon2026.IntegralInducedWeightProducts

/-! An explicit nonzero vector in every original dominant integral induced
module. It is the actual product of trailing minors to the nonnegative
adjacent weight differences, multiplied by the original determinant to
the last integral weight. This proves source coefficient nonzeroness,
without an assumed irreducible representation or stable lattice.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] {n : ℕ}

/-- The original regular-function vector for a dominant weight: trailing minors to the actual adjacent differences and the original last-weight determinant power. -/
def integralDominantInducedVector (lam : Fin (n + 1) → ℤ) :
    GeneralLinearRegularFunctions R (n + 1) :=
  ((generalLinearRegularDeterminantUnit (R := R) (n := n + 1) ^ lam (0 : Fin (n + 1)).rev :
      (GeneralLinearRegularFunctions R (n + 1))ˣ) : GeneralLinearRegularFunctions R (n + 1)) *
    ∏ j : Fin n, integralInducedFundamentalVector R (n + 1) j.succ ^
      integralDominantWeightExponent lam j

/-- The explicit dominant vector satisfies the literal source Borel covariance over every coefficient algebra. -/
theorem integralDominantInducedVector_mem (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam) :
    integralDominantInducedVector R lam ∈ generalLinearIntegralInducedSubmodule R (n + 1) lam := by
  have hp := generalLinearIntegralInduced_prod (R := R) Finset.univ
    (fun j : Fin n => fun i => (integralDominantWeightExponent lam j : ℤ) *
      integralInducedFundamentalWeight (n + 1) j.succ i)
    (fun j => integralInducedFundamentalVector R (n + 1) j.succ ^ integralDominantWeightExponent lam j)
    (fun j _ => generalLinearIntegralInduced_pow _ _ (integralInducedFundamentalVector_mem R (n + 1) j.succ))
  have ht := generalLinearIntegralInduced_determinant_twist
    (fun i => ∑ j : Fin n, (integralDominantWeightExponent lam j : ℤ) *
      integralInducedFundamentalWeight (n + 1) j.succ i)
    (lam (0 : Fin (n + 1)).rev) hp
  have hw : (fun i => (∑ j : Fin n, (integralDominantWeightExponent lam j : ℤ) *
      integralInducedFundamentalWeight (n + 1) j.succ i) + lam (0 : Fin (n + 1)).rev) = lam :=
    funext fun i => (integralDominantWeight_decomposition lam hlam i).symm
  rw [hw] at ht
  exact ht

/-- The actual dominant vector evaluates to one at the original identity matrix. -/
theorem integralDominantInducedVector_one (lam : Fin (n + 1) → ℤ) :
    generalLinearRegularEval (1 : GeneralLinearGroup (Fin (n + 1)) R)
      (integralDominantInducedVector R lam) = 1 := by
  rw [integralDominantInducedVector, map_mul, generalLinearRegularEval_determinant_zpow, map_prod]
  simp only [map_one, one_zpow, Units.val_one, map_pow, integralInducedFundamentalVector_one,
    one_pow, Finset.prod_const_one, one_mul]

/-- The original dominant-weight vector is nonzero over every nontrivial original coefficient ring. -/
theorem integralDominantInducedVector_ne_zero [Nontrivial R] (lam : Fin (n + 1) → ℤ) :
    integralDominantInducedVector R lam ≠ 0 := by
  intro h
  have he := integralDominantInducedVector_one R lam
  rw [h, map_zero] at he
  exact zero_ne_one he

/-- Every actual source dominant-weight induced module is nontrivial, witnessed by its original regular-function vector. -/
theorem integralDominantInduced_nontrivial [Nontrivial R]
    (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam) :
    Nontrivial (generalLinearIntegralInducedSubmodule R (n + 1) lam) := by
  let v : generalLinearIntegralInducedSubmodule R (n + 1) lam :=
    ⟨integralDominantInducedVector R lam, integralDominantInducedVector_mem R lam hlam⟩
  refine ⟨⟨v, 0, ?_⟩⟩
  intro h
  exact integralDominantInducedVector_ne_zero R lam (congrArg Subtype.val h)

end
end Dubon2026
