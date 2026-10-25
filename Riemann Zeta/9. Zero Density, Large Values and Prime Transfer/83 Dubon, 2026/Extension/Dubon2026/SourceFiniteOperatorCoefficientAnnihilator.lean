import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! DUB-17/18 -> coefficient-field primitive projector. Scalar extension
of the already finite integral Hecke algebra gives a polynomial over the
chosen coefficient field for the finite squared shifted operator. -/
namespace Dubon2026
noncomputable section
open Polynomial TensorProduct
variable {K L A V I : Type*} [Field K] [Field L] [Ring A] [Module.Finite ℤ A]
  [AddCommGroup V] [Module L V]

theorem finite_operator_coefficient_annihilator (ι : K →+* L)
    (φ : A →+* Module.End L V) (s : Finset I) (t : I → A) (a : I → K) :
    ∃ P : K[X], P.Monic ∧
      aeval (∑ i ∈ s, (φ (t i) - ι (a i) • 1) ^ 2) (P.map ι) = 0 := by
  let B := Module.End L V
  letI : Algebra ℤ B := inferInstance
  letI := Algebra.compHom B ι
  letI : IsScalarTower ℤ K B := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let ψ : K ⊗[ℤ] A →ₐ[K] B := (AlgHom.liftEquiv ℤ K A B) φ.toIntAlgHom
  let z : K ⊗[ℤ] A := ∑ i ∈ s, ((1 : K) ⊗ₜ[ℤ] t i - a i • 1) ^ 2
  have hz : ψ z = ∑ i ∈ s, (φ (t i) - ι (a i) • 1) ^ 2 := by
    simp only [z, map_sum, map_pow, map_sub, map_smul, map_one, ψ,
      AlgHom.liftEquiv_tmul, one_smul, RingHom.toIntAlgHom_apply]
    rfl
  have hi := (IsIntegral.of_finite K z).map ψ
  rw [hz] at hi
  obtain ⟨P, hP, hPH⟩ := hi
  refine ⟨P, hP, ?_⟩
  simpa only [aeval_def, eval₂_map] using hPH

end
end Dubon2026
