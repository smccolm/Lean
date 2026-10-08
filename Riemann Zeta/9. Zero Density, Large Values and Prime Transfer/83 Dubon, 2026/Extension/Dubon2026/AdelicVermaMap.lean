import Dubon2026.PolynomialCyclicMap
import Dubon2026.VermaPolynomialLieAction
import Dubon2026.VermaPolynomialWeights
import Dubon2026.AdelicLowestWeightJets

/-! # Polynomial Verma action on the original adelic cusp generator -/

namespace Dubon2026

noncomputable section
open Polynomial Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- Evaluate original polynomial operators at the actual raising derivative of the original cusp generator. -/
def adelicVermaMap : ℂ[X] →ₗ[ℂ] adelicRealSmoothSubmodule f :=
  polynomialCyclicMap (adelicComplexSl2Action f compactSl2E) (adelicSmoothGenerator f)

/-- Original polynomial monomials map to the literal original adelic raising derivatives. -/
theorem adelicVermaMap_X_pow (n : ℕ) : adelicVermaMap f (X ^ n) = adelicRaisingJet f n :=
  polynomialCyclicMap_X_pow _ _ n

/-- The original constant polynomial maps to the actual original cusp generator. -/
theorem adelicVermaMap_one : adelicVermaMap f 1 = adelicSmoothGenerator f :=
  polynomialCyclicMap_one _ _

/-- The original cusp map intertwines the actual compact Cartan operator at highest weight -k. -/
theorem adelicVermaMap_H (hf : f ≠ 0) (p : ℂ[X]) :
    adelicVermaMap f (vermaPolynomialLieAction (-(k : ℂ)) compactSl2H p) =
      adelicComplexSl2Action f compactSl2H (adelicVermaMap f p) := by
  have he : (adelicVermaMap f).comp (vermaPolynomialLieAction (-(k : ℂ)) compactSl2H) =
      (adelicComplexSl2Action f compactSl2H).comp (adelicVermaMap f) := by
    apply polynomialLinearMap_eq_of_X_pow
    intro n
    simp only [LinearMap.comp_apply, vermaPolynomialLieAction_H, LinearMap.neg_apply,
      vermaPolynomialH_X_pow, map_neg, map_smul, adelicVermaMap_X_pow,
      ← adelicSmoothComplexLie_apply, adelicRaisingJet_weight f hf]
    rw [← neg_smul (-(k : ℂ) - 2 * n) (adelicRaisingJet f n)]
    congr 1
    ring
  exact LinearMap.congr_fun he p

/-- The actual polynomial shift intertwines with the original raising derivative. -/
theorem adelicVermaMap_E (p : ℂ[X]) :
    adelicVermaMap f (vermaPolynomialLieAction (-(k : ℂ)) compactSl2E p) =
      adelicComplexSl2Action f compactSl2E (adelicVermaMap f p) := by
  have he : (adelicVermaMap f).comp (vermaPolynomialLieAction (-(k : ℂ)) compactSl2E) =
      (adelicComplexSl2Action f compactSl2E).comp (adelicVermaMap f) := by
    apply polynomialLinearMap_eq_of_X_pow
    intro n
    simp only [LinearMap.comp_apply, vermaPolynomialLieAction_E, vermaPolynomialF_X_pow,
      adelicVermaMap_X_pow, ← adelicSmoothComplexLie_apply, adelicRaisingJet_raise]
  exact LinearMap.congr_fun he p

/-- The actual polynomial differential operator intertwines with the original lowering derivative. -/
theorem adelicVermaMap_F (hf : f ≠ 0) (p : ℂ[X]) :
    adelicVermaMap f (vermaPolynomialLieAction (-(k : ℂ)) compactSl2F p) =
      adelicComplexSl2Action f compactSl2F (adelicVermaMap f p) := by
  have he : (adelicVermaMap f).comp (vermaPolynomialLieAction (-(k : ℂ)) compactSl2F) =
      (adelicComplexSl2Action f compactSl2F).comp (adelicVermaMap f) := by
    apply polynomialLinearMap_eq_of_X_pow
    intro n
    cases n with
    | zero =>
        simp only [LinearMap.comp_apply, pow_zero, vermaPolynomialLieAction_F,
          (vermaPolynomial_generator (-(k : ℂ))).2, map_zero, adelicVermaMap_one,
          ← adelicSmoothComplexLie_apply, adelicSmoothGenerator_lowering_zero]
    | succ n =>
        simp only [LinearMap.comp_apply, vermaPolynomialLieAction_F,
          vermaPolynomialE_X_pow_succ, map_smul, adelicVermaMap_X_pow,
          ← adelicSmoothComplexLie_apply, adelicRaisingJet_lower f hf]
  exact LinearMap.congr_fun he p

/-- The original polynomial cusp map intertwines every genuine complex matrix infinitesimal. -/
theorem adelicVermaMap_matrix (hf : f ≠ 0) (x : ComplexSl2) (p : ℂ[X]) :
    adelicVermaMap f (vermaPolynomialLieAction (-(k : ℂ)) x p) =
      adelicComplexSl2Action f x (adelicVermaMap f p) := by
  rw [compactSl2_decomposition x]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    adelicVermaMap_H f hf, adelicVermaMap_E, adelicVermaMap_F f hf]

end
end Dubon2026
