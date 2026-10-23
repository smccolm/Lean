import Dubon2026.SourceFaithfulMatrixBaseChange
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-! DUB-17/18 -> prescribed primitive eigensystem -> specialize the
actual p-adic operator algebra. Faithful integral matrices identify this
generated algebra with the native scalar extension, so every integral
character extends while retaining its values on the original operators. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct
variable {A : Type*} [Ring A] {n : ℕ}
variable (M : A →+* Matrix (Fin n) (Fin n) ℤ)
variable (K : Type*) [Field K]

theorem integralMatrixBaseChange_range :
    (integralMatrixBaseChange M K).range =
      Algebra.adjoin K (Set.range fun a => (M a).map (Int.cast : ℤ → K)) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subalgebra.zero_mem _
    | tmul c a =>
      change integralMatrixBaseChange M K (c ⊗ₜ[ℤ] a) ∈ _
      rw [integralMatrixBaseChange_tmul]
      apply Subalgebra.smul_mem
      exact Algebra.subset_adjoin ⟨a, rfl⟩
    | add x y hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  · apply Algebra.adjoin_le
    rintro _ ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ[ℤ] a, (integralMatrixBaseChange_tmul M K 1 a).trans (one_smul K _)⟩

variable [CharZero K]

/-- The faithful tensor presentation of the algebra of original integral matrices. -/
def integralMatrixTensorEquiv (hM : Function.Injective M) :
    K ⊗[ℤ] A ≃ₐ[K]
      Algebra.adjoin K (Set.range fun a => (M a).map (Int.cast : ℤ → K)) :=
  (AlgEquiv.ofInjective (integralMatrixBaseChange M K)
    (integralMatrixBaseChange_injective M K hM)).trans
    (Subalgebra.equivOfEq _ _ (integralMatrixBaseChange_range M K))

theorem integralMatrixTensorEquiv_generator (hM : Function.Injective M) (a : A) :
    integralMatrixTensorEquiv M K hM (1 ⊗ₜ[ℤ] a) =
      ⟨(M a).map (Int.cast : ℤ → K), Algebra.subset_adjoin ⟨a, rfl⟩⟩ := by
  apply Subtype.ext
  change integralMatrixBaseChange M K (1 ⊗ₜ[ℤ] a) = _
  rw [integralMatrixBaseChange_tmul, one_smul]

variable {E : Type*} [CommRing E] [Algebra K E]

/-- Extend an integral character to the generated matrix algebra over the coefficient field. -/
def integralMatrixSpecialization (hM : Function.Injective M) (χ : A →+* E) :
    Algebra.adjoin K (Set.range fun a => (M a).map (Int.cast : ℤ → K)) →ₐ[K] E :=
  (AlgHom.liftEquiv ℤ K A E χ.toIntAlgHom).comp
    (integralMatrixTensorEquiv M K hM).symm.toAlgHom

theorem integralMatrixSpecialization_generator (hM : Function.Injective M)
    (χ : A →+* E) (a : A) :
    integralMatrixSpecialization M K hM χ
      ⟨(M a).map (Int.cast : ℤ → K), Algebra.subset_adjoin ⟨a, rfl⟩⟩ = χ a := by
  rw [← integralMatrixTensorEquiv_generator M K hM a]
  change AlgHom.liftEquiv ℤ K A E χ.toIntAlgHom
    ((integralMatrixTensorEquiv M K hM).symm
      (integralMatrixTensorEquiv M K hM (1 ⊗ₜ[ℤ] a))) = _
  rw [AlgEquiv.symm_apply_apply, AlgHom.liftEquiv_tmul, one_smul]
  rfl

end
end Dubon2026
