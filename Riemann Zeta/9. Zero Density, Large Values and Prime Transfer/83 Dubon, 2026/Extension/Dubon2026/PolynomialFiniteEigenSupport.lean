import Dubon2026.PolynomialEndIntertwiner
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! # An actual polynomial annihilator forces finite support in distinct eigen-coordinates -/

namespace Dubon2026

noncomputable section
open Polynomial

/-- A nonzero original annihilating polynomial forces only finitely many nonzero coordinates in a genuine family of distinct dual eigenvectors. -/
theorem polynomialAnnihilator_finite_eigen_support {V ι : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (L : ι → V →ₗ[ℂ] ℂ) (μ : ι → ℂ) (hμ : Function.Injective μ)
    (hL : ∀ i v, L i (T v) = μ i * L i v) (p : ℂ[X]) (hp : p ≠ 0)
    (v : V) (hv : aeval T p v = 0) : Set.Finite {i | L i v ≠ 0} := by
  classical
  have hroot (i : ι) (hi : L i v ≠ 0) : p.eval (μ i) = 0 := by
    let S : Module.End ℂ ℂ := μ i • LinearMap.id
    have he := polynomialEnd_intertwine T S (L i) (hL i) p v
    have hs : S (L i v) = μ i • L i v := rfl
    rw [hv, map_zero, Module.End.aeval_apply_of_mem_apply_eq_smul hs, smul_eq_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_right hi
  have hfin : Set.Finite (μ ⁻¹' (p.roots.toFinset : Set ℂ)) :=
    p.roots.toFinset.finite_toSet.preimage hμ.injOn
  apply hfin.subset
  intro i hi
  change μ i ∈ p.roots.toFinset
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
  exact hroot i hi

end
end Dubon2026
