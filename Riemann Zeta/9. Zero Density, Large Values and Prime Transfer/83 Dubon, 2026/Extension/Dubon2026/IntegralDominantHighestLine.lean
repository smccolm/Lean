import Dubon2026.IntegralInducedOppositeLine
import Dubon2026.IntegralHighestOppositeTransport

/-! The exact original highest line of the literal source induction.
Every original induced vector with the all-algebra highest character is
its value at the longest matrix times the explicitly constructed vector.
This proves uniqueness and normalization of the required highest line;
generation and characteristic-zero irreducibility remain separate.
-/

namespace Dubon2026
noncomputable section
open Matrix

universe u
variable (R : Type u) [CommRing R] [IsDomain R] {n : ℕ}

/-- Every actual source induced vector of the exact algebraic highest character is the longest-value multiple of the original constructed highest vector. -/
theorem integralDominantHighestLine_eq (lam : Fin (n + 1) → ℤ) (hlam : Antitone lam)
    (q : generalLinearIntegralInducedSubmodule R (n + 1) lam)
    (hq : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin (n + 1)) A) (b : generalLinearBorel A (n + 1)),
        generalLinearRegularEval (g * b.val) q.val =
          ((∏ i : Fin (n + 1), generalLinearBorelDiagonalUnit b i ^ lam i : Aˣ) : A) *
            generalLinearRegularEval g q.val) :
    q = generalLinearRegularEval (integralWeightLongest R (n + 1)) q.val •
      integralDominantHighestVector R lam hlam := by
  let W := integralWeightLongest R (n + 1)
  let p : generalLinearIntegralInducedSubmodule R (n + 1) lam :=
    ⟨generalLinearRegularRightTranslate W q.val,
      generalLinearIntegralInducedSubmodule_stable R (n + 1) lam W q.property⟩
  have hp := integralInduced_opposite_character_eq_dominant R lam hlam p
    (integralWeightLongestTranslate_opposite R (n + 1) lam q.val hq)
  have he : generalLinearRegularEval (1 : GeneralLinearGroup (Fin (n + 1)) R) p.val =
      generalLinearRegularEval W q.val := by
    have h := AlgHom.congr_fun (generalLinearRegularEval_rightTranslate W
      (1 : GeneralLinearGroup (Fin (n + 1)) R)) q.val
    simpa only [AlgHom.comp_apply, W, integralWeightLongest_map, one_mul] using h
  rw [he] at hp
  have ht := congrArg (generalLinearRegularRightTranslate W) hp
  have hWW : (generalLinearRegularRightTranslate W).comp
      (generalLinearRegularRightTranslate W) =
        AlgHom.id R (GeneralLinearRegularFunctions R (n + 1)) := by
    rw [← generalLinearRegularRightTranslate_mul,
      integralWeightLongest_mul_self, generalLinearRegularRightTranslate_one]
  have hqq : generalLinearRegularRightTranslate W p.val = q.val :=
    AlgHom.congr_fun hWW q.val
  rw [hqq] at ht
  apply Subtype.ext
  change q.val = generalLinearRegularEval W q.val • integralDominantHighestRegular R lam
  simpa only [Algebra.smul_def, map_mul, AlgHom.commutes,
    W, integralDominantHighestRegular] using ht

/-- The exact highest vector is uniquely normalized by evaluation at the original longest matrix. -/
theorem integralDominantHighestLine_normalized_unique (lam : Fin (n + 1) → ℤ)
    (hlam : Antitone lam)
    (q : generalLinearIntegralInducedSubmodule R (n + 1) lam)
    (hq : ∀ (A : Type u) [CommRing A] [Algebra R A]
      (g : GeneralLinearGroup (Fin (n + 1)) A) (b : generalLinearBorel A (n + 1)),
        generalLinearRegularEval (g * b.val) q.val =
          ((∏ i : Fin (n + 1), generalLinearBorelDiagonalUnit b i ^ lam i : Aˣ) : A) *
            generalLinearRegularEval g q.val)
    (he : generalLinearRegularEval (integralWeightLongest R (n + 1)) q.val = 1) :
    q = integralDominantHighestVector R lam hlam := by
  rw [integralDominantHighestLine_eq R lam hlam q hq, he, one_smul]

end
end Dubon2026
