import Dubon2026.FiniteEigenPolynomialKernel
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.RepresentationTheory.Intertwining

/-! # Finite multiplicity from the actual eigenspaces of one group operator -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- An actual operator intertwiner also intertwines every genuine polynomial in the operators. -/
theorem linearMap_aeval_intertwines (S : Module.End ℂ V) (T : Module.End ℂ W)
    (L : V →ₗ[ℂ] W) (hL : ∀ x, L (S x) = T (L x)) (p : Polynomial ℂ) (x : V) :
    L (aeval S p x) = aeval T p (L x) := by
  have hpow (n : ℕ) : ∀ y, L ((S ^ n) y) = (T ^ n) (L y) := by
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hL, ih]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, hpow]

/-- Genuine intertwiners from any finite-dimensional complex representation have finite multiplicity when every eigenspace of one actual target group operator is finite-dimensional. -/
theorem finiteDimensional_intertwining_of_eigenspaces
    {G : Type*} [Monoid G] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (g : G)
    (hg : ∀ c : ℂ, FiniteDimensional ℂ (Module.End.eigenspace (σ g) c)) :
    FiniteDimensional ℂ (Representation.IntertwiningMap ρ σ) := by
  let P := LinearMap.ker (aeval (σ g) (ρ g).charpoly)
  letI : FiniteDimensional ℂ P :=
    finiteDimensional_polynomial_kernel_of_eigenspaces (σ g) hg _ (ρ g).charpoly_monic
  have hm (u : Representation.IntertwiningMap ρ σ) (x : V) : u x ∈ P := by
    have he := linearMap_aeval_intertwines (ρ g) (σ g) u.toLinearMap
      (Representation.IntertwiningMap.isIntertwining ρ σ u g) (ρ g).charpoly x
    rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at he
    exact he.symm
  let L : Representation.IntertwiningMap ρ σ →ₗ[ℂ] (V →ₗ[ℂ] P) :=
    { toFun := fun u => u.toLinearMap.codRestrict P (hm u)
      map_add' := by intro u v; ext x; rfl
      map_smul' := by intro c u; ext x; rfl }
  apply FiniteDimensional.of_injective L
  intro u v huv
  apply Representation.IntertwiningMap.ext
  ext x
  exact congrArg (fun l : V →ₗ[ℂ] P => (l x).val) huv

end
end Dubon2026
