import Dubon2026.VermaPolynomialMaps
import Dubon2026.VermaPolynomialLieAction
import Dubon2026.UniversalEnvelopingInduction
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Exact coefficient evaluation throughout the genuine matrix enveloping action -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

/-- Changing actual coefficients intertwines the genuine entire complex matrix action. -/
theorem vermaPolynomialLieAction_map (φ : R →ₐ[ℂ] S) (μ : R) (x : ComplexSl2) (p : R[X]) :
    Polynomial.mapAlgHom φ (vermaPolynomialLieAction μ x p) =
      vermaPolynomialLieAction (φ μ) x (Polynomial.mapAlgHom φ p) := by
  have hH : Polynomial.mapAlgHom φ (vermaPolynomialH μ p) =
      vermaPolynomialH (φ μ) (Polynomial.mapAlgHom φ p) := vermaPolynomial_map_H φ.toRingHom μ p
  have hE : Polynomial.mapAlgHom φ (vermaPolynomialE μ p) =
      vermaPolynomialE (φ μ) (Polynomial.mapAlgHom φ p) := vermaPolynomial_map_E φ.toRingHom μ p
  have hF : Polynomial.mapAlgHom φ (vermaPolynomialF p) =
      vermaPolynomialF (Polynomial.mapAlgHom φ p) := vermaPolynomial_map_F φ.toRingHom p
  rw [compactSl2_decomposition x]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    vermaPolynomialLieAction_H, vermaPolynomialLieAction_E, vermaPolynomialLieAction_F,
    LinearMap.neg_apply, map_neg, hH, hE, hF]

/-- Original coefficient evaluation intertwines every element of the genuine universal enveloping algebra. -/
theorem vermaPolynomialEnvelopingAction_map (φ : R →ₐ[ℂ] S) (μ : R)
    (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) (p : R[X]) :
    Polynomial.mapAlgHom φ (vermaPolynomialEnvelopingAction μ z p) =
      vermaPolynomialEnvelopingAction (φ μ) z (Polynomial.mapAlgHom φ p) := by
  induction z using universalEnveloping_induction generalizing p with
  | hscalar c =>
      rw [AlgHom.commutes, AlgHom.commutes]
      change Polynomial.mapAlgHom φ (c • p) = c • Polynomial.mapAlgHom φ p
      exact map_smul _ _ _
  | hgenerator x =>
      rw [vermaPolynomialEnvelopingAction_generator, vermaPolynomialEnvelopingAction_generator]
      exact vermaPolynomialLieAction_map φ μ x p
  | hadd x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | hmul x y hx hy => simp only [map_mul, Module.End.mul_apply, hx, hy]

end
end Dubon2026
