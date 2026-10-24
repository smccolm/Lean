import Dubon2026.SourceCurveLocalDifferentials
import Dubon2026.SourceCurveOrders
import Mathlib.Algebra.Polynomial.Derivative

/-! The indexed conjugate-uniformizer polynomial for the DUB-17/18 wild
different estimate. It retains multiplicities, so no unproved freeness
of the uniformizer orbit is used. Native product and differentiation
identities replace the external proof's auxiliary multiset lemmas. -/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial
variable {K F G : Type*} [Field K] [Field F] [Algebra K F] [Group G] [Fintype G]

/-- The polynomial indexed by every group element, including repeated conjugates. -/
def conjugateUniformizerPolynomial (ρ : G →* (F ≃ₐ[K] F)) (t : F) : F[X] :=
  ∏ σ : G, (X - C (ρ σ t))

theorem conjugateUniformizerPolynomial_eval (ρ : G →* (F ≃ₐ[K] F)) (t : F) :
    (conjugateUniformizerPolynomial ρ t).eval t = 0 := by
  classical
  rw [conjugateUniformizerPolynomial, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ (1 : G)) (by simp)

theorem conjugateUniformizerPolynomial_map (ρ : G →* (F ≃ₐ[K] F)) (t : F) (τ : G) :
    (conjugateUniformizerPolynomial ρ t).map (ρ τ).toRingHom =
      conjugateUniformizerPolynomial ρ t := by
  classical
  simp only [conjugateUniformizerPolynomial, Polynomial.map_prod,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  exact Fintype.prod_bijective (fun σ => τ * σ) (Group.mulLeft_bijective τ)
    _ _ (fun σ => by simp only [map_mul, AlgEquiv.mul_apply]; rfl)

theorem conjugateUniformizerPolynomial_derivative_eval [DecidableEq G]
    (ρ : G →* (F ≃ₐ[K] F)) (t : F) :
    (conjugateUniformizerPolynomial ρ t).derivative.eval t =
      ∏ σ ∈ Finset.univ.erase (1 : G), (t - ρ σ t) := by
  have hfac : conjugateUniformizerPolynomial ρ t =
      (X - C (ρ 1 t)) * ∏ σ ∈ Finset.univ.erase (1 : G), (X - C (ρ σ t)) :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ _)).symm
  rw [hfac, derivative_mul]
  simp only [eval_add, eval_mul, derivative_X_sub_C, one_mul,
    eval_sub, eval_X, eval_C, map_one, AlgEquiv.one_apply, sub_self,
    zero_mul, add_zero, eval_prod]

theorem conjugateUniformizerPolynomial_coeff_mem (ρ : G →* (F ≃ₐ[K] F)) (t : F)
    (A : Subring F) (ht : ∀ σ, ρ σ t ∈ A) (k : ℕ) :
    (conjugateUniformizerPolynomial ρ t).coeff k ∈ A := by
  let f : A[X] := ∏ σ : G, (X - C (⟨ρ σ t, ht σ⟩ : A))
  have he : f.map A.subtype = conjugateUniformizerPolynomial ρ t := by
    simp only [f, conjugateUniformizerPolynomial, Polynomial.map_prod,
      Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Subring.coe_subtype]
  rw [← he, coeff_map]
  exact (f.coeff k).2

end
end Dubon2026.SourceCurve
