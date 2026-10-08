import Dubon2026.VermaPolynomialWeights
import Dubon2026.CompactSl2LieHom
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Tactic.NoncommRing

/-! # The actual compact matrix Lie algebra and its enveloping algebra on polynomial Verma modules -/

namespace Dubon2026

noncomputable section
open Polynomial

private theorem neg_first_commutator {A : Type*} [Ring A] (x y : A) :
    (-x) * y - y * (-x) = -(x * y - y * x) := by noncomm_ring

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- The genuine original compact matrices act on the actual polynomial Verma module, with reversed Cartan and raising conventions matching the original cusp derivatives. -/
def vermaPolynomialLieAction (μ : R) : ComplexSl2 →ₗ⁅ℂ⁆ Module.End R R[X] := by
  apply compactSl2LieHom (-vermaPolynomialH μ) vermaPolynomialF (vermaPolynomialE μ)
  · calc
      _ = -(vermaPolynomialE μ * vermaPolynomialF - vermaPolynomialF * vermaPolynomialE μ) :=
        by noncomm_ring
      _ = -vermaPolynomialH μ := congrArg Neg.neg (vermaPolynomial_E_F μ)
  · calc
      _ = -(vermaPolynomialH μ * vermaPolynomialF - vermaPolynomialF * vermaPolynomialH μ) :=
        neg_first_commutator (vermaPolynomialH μ) vermaPolynomialF
      _ = -((-2 : R) • vermaPolynomialF) := congrArg Neg.neg (vermaPolynomial_H_F μ)
      _ = (2 : ℂ) • vermaPolynomialF := by
        rw [neg_smul (2 : R) (vermaPolynomialF : Module.End R R[X]), neg_neg,
          two_smul R, two_smul ℂ]
  · calc
      _ = -(vermaPolynomialH μ * vermaPolynomialE μ - vermaPolynomialE μ * vermaPolynomialH μ) :=
        neg_first_commutator (vermaPolynomialH μ) (vermaPolynomialE μ)
      _ = -((2 : R) • vermaPolynomialE μ) := congrArg Neg.neg (vermaPolynomial_H_E μ)
      _ = -((2 : ℂ) • vermaPolynomialE μ) := by rw [two_smul, two_smul]

/-- The actual compact Cartan acts by minus the genuine Verma Cartan. -/
theorem vermaPolynomialLieAction_H (μ : R) :
    vermaPolynomialLieAction μ compactSl2H = -vermaPolynomialH μ :=
  compactSl2LinearMap_H _ _ _

/-- The actual compact raising matrix acts by multiplication by the original polynomial variable. -/
theorem vermaPolynomialLieAction_E (μ : R) :
    vermaPolynomialLieAction μ compactSl2E = vermaPolynomialF :=
  compactSl2LinearMap_E _ _ _

/-- The actual compact lowering matrix acts by the genuine Verma derivative operator. -/
theorem vermaPolynomialLieAction_F (μ : R) :
    vermaPolynomialLieAction μ compactSl2F = vermaPolynomialE μ :=
  compactSl2LinearMap_F _ _ _

/-- The actual matrix action lifts to the genuine universal enveloping algebra, retaining linearity over the original coefficient ring. -/
def vermaPolynomialEnvelopingAction (μ : R) :
    UniversalEnvelopingAlgebra ℂ ComplexSl2 →ₐ[ℂ] Module.End R R[X] :=
  UniversalEnvelopingAlgebra.lift ℂ (vermaPolynomialLieAction μ)

/-- The enveloping action agrees with the original actual matrix action on every generator. -/
theorem vermaPolynomialEnvelopingAction_generator (μ : R) (x : ComplexSl2) :
    vermaPolynomialEnvelopingAction μ (UniversalEnvelopingAlgebra.ι ℂ x) = vermaPolynomialLieAction μ x :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ (vermaPolynomialLieAction μ) x

end
end Dubon2026
