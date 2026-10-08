import Dubon2026.PolynomialCyclicMap
import Dubon2026.VermaPolynomialLieAction
import Dubon2026.VermaPolynomialWeights
import Dubon2026.EnvelopingIntertwiner

/-! # Genuine Verma intertwiners from original compact primitive vectors -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Evaluate genuine Verma polynomials on an original compact primitive vector using its actual raising operator. -/
def primitiveVermaMap (ρ : ComplexSl2 →ₗ⁅ℂ⁆ Module.End ℂ V) (v : V) : ℂ[X] →ₗ[ℂ] V :=
  polynomialCyclicMap (ρ compactSl2E) v

/-- The original primitive-vector evaluation intertwines every actual traceless matrix action. -/
theorem primitiveVermaMap_matrix (ρ : ComplexSl2 →ₗ⁅ℂ⁆ Module.End ℂ V) (v : V) (μ : ℂ)
    (hv : v ≠ 0) (hH : ρ compactSl2H v = (-μ) • v) (hF : ρ compactSl2F v = 0)
    (x : ComplexSl2) (p : ℂ[X]) :
    primitiveVermaMap ρ v (vermaPolynomialLieAction μ x p) = ρ x (primitiveVermaMap ρ v p) := by
  letI : LieRingModule ComplexSl2 V := LieRingModule.compLieHom V ρ
  letI : LieModule ℂ ComplexSl2 V := LieModule.compLieHom V ρ
  have hp : IsSl2Triple.HasPrimitiveVectorWith compactSl2Triple.symm v μ :=
    { ne_zero := hv
      lie_h := by
        change ρ (-compactSl2H) v = μ • v
        rw [map_neg, LinearMap.neg_apply, hH, neg_smul, neg_neg]
      lie_e := hF }
  have hCartan (n : ℕ) :
      ρ compactSl2H ((ρ compactSl2E ^ n) v) = (-(μ - 2 * n)) • ((ρ compactSl2E ^ n) v) := by
    have he := hp.lie_h_pow_toEnd_f n
    change ρ (-compactSl2H) ((ρ compactSl2E ^ n) v) = (μ - 2 * n) • ((ρ compactSl2E ^ n) v) at he
    rw [map_neg, LinearMap.neg_apply] at he
    exact (neg_eq_iff_eq_neg.mp he).trans (neg_smul _ _).symm
  have hLower (n : ℕ) :
      ρ compactSl2F ((ρ compactSl2E ^ (n + 1)) v) =
        (((n : ℂ) + 1) * (μ - n)) • ((ρ compactSl2E ^ n) v) := hp.lie_e_pow_succ_toEnd_f n
  have hpow (n : ℕ) : primitiveVermaMap ρ v (X ^ n) = ((ρ compactSl2E ^ n) v) :=
    polynomialCyclicMap_X_pow _ _ n
  have hbasis : ∀ y ∈ ({compactSl2H, compactSl2E, compactSl2F} : Set ComplexSl2),
      (primitiveVermaMap ρ v).comp (vermaPolynomialLieAction μ y) =
        (ρ y).comp (primitiveVermaMap ρ v) := by
    intro y hy
    rcases hy with rfl | rfl | rfl
    · apply polynomialLinearMap_eq_of_X_pow
      intro n
      simp only [LinearMap.comp_apply, vermaPolynomialLieAction_H, LinearMap.neg_apply,
        vermaPolynomialH_X_pow, map_neg, map_smul, hpow, hCartan, neg_smul]
    · apply polynomialLinearMap_eq_of_X_pow
      intro n
      simp only [LinearMap.comp_apply, vermaPolynomialLieAction_E,
        vermaPolynomialF_X_pow, hpow]
      rw [pow_succ', Module.End.mul_apply]
    · apply polynomialLinearMap_eq_of_X_pow
      intro n
      cases n with
      | zero =>
          simp only [LinearMap.comp_apply, pow_zero, vermaPolynomialLieAction_F,
            (vermaPolynomial_generator μ).2, map_zero]
          change 0 = ρ compactSl2F (polynomialCyclicMap (ρ compactSl2E) v 1)
          rw [polynomialCyclicMap_one, hF]
      | succ n =>
          simp only [LinearMap.comp_apply, vermaPolynomialLieAction_F,
            vermaPolynomialE_X_pow_succ, map_smul, hpow, hLower]
  have h₁ := LinearMap.congr_fun (hbasis compactSl2H (by simp)) p
  have h₂ := LinearMap.congr_fun (hbasis compactSl2E (by simp)) p
  have h₃ := LinearMap.congr_fun (hbasis compactSl2F (by simp)) p
  rw [compactSl2_decomposition x]
  simpa only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply] using
    congrArg₂ (fun a b : V => a + b)
      (congrArg₂ (fun a b : V => a + b)
        (congrArg (fun w : V => (Complex.I / 2 * (x.val 0 1 - x.val 1 0)) • w) h₁)
        (congrArg (fun w : V => (x.val 0 0 - Complex.I / 2 * (x.val 0 1 + x.val 1 0)) • w) h₂))
      (congrArg (fun w : V => (x.val 0 0 + Complex.I / 2 * (x.val 0 1 + x.val 1 0)) • w) h₃)

/-- Original primitive-vector evaluation intertwines every genuine enveloping-algebra element. -/
theorem primitiveVermaMap_enveloping (ρ : ComplexSl2 →ₗ⁅ℂ⁆ Module.End ℂ V) (v : V) (μ : ℂ)
    (hv : v ≠ 0) (hH : ρ compactSl2H v = (-μ) • v) (hF : ρ compactSl2F v = 0)
    (z : UniversalEnvelopingAlgebra ℂ ComplexSl2) (p : ℂ[X]) :
    primitiveVermaMap ρ v (vermaPolynomialEnvelopingAction μ z p) =
      UniversalEnvelopingAlgebra.lift ℂ ρ z (primitiveVermaMap ρ v p) := by
  apply universalEnveloping_intertwine _ _ _ _ z p
  intro x q
  rw [vermaPolynomialEnvelopingAction_generator, UniversalEnvelopingAlgebra.lift_ι_apply]
  exact primitiveVermaMap_matrix ρ v μ hv hH hF x q

end
end Dubon2026
