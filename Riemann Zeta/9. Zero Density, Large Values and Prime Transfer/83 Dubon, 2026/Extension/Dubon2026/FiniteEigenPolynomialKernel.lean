import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Finite polynomial kernels from genuine finite-dimensional complex eigenspaces -/

namespace Dubon2026

noncomputable section
open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)

/-- A monic polynomial in an original complex operator has finite-dimensional kernel whenever its actual eigenspaces do. -/
theorem finiteDimensional_polynomial_kernel_of_eigenspaces
    (hT : ∀ c : ℂ, FiniteDimensional ℂ (Module.End.eigenspace T c))
    (p : Polynomial ℂ) (hp : p.Monic) : FiniteDimensional ℂ (LinearMap.ker (aeval T p)) := by
  have hprod : ∀ s : Multiset ℂ,
      FiniteDimensional ℂ (LinearMap.ker (aeval T ((s.map (fun c => X - C c)).prod))) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, map_one]
      change FiniteDimensional ℂ (LinearMap.ker (LinearMap.id : V →ₗ[ℂ] V))
      rw [LinearMap.ker_id]
      infer_instance
    | cons c s ih =>
      letI := ih
      have hfactor : FiniteDimensional ℂ (LinearMap.ker (aeval T (X - C c))) := by
        rw [map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
          ← Module.End.eigenspace_def]
        exact hT c
      letI := hfactor
      rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Module.End.mul_eq_comp, LinearMap.ker_comp]
      infer_instance
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp]
  exact hprod p.roots

end
end Dubon2026
