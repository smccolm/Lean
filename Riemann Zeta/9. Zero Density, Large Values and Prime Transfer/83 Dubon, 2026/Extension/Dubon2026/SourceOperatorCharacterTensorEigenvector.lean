import Dubon2026.SourceCommutingPrescribedEigenvector
import Dubon2026.SourceFaithfulCharacterFiber
import Mathlib.RingTheory.TensorProduct.Basic

/-! A prescribed Hecke character is realized on a nonzero tensor eigenvector.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual modular Galois association -> residual H1 eigensystem
-> nonzero tensor eigenclass with the already constructed original character.

Adapted from anthropics/fermats-last-theorem, revision
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_Module_exists_ne_zero_forall_baseChange_eq_smul_of_algHom.lean
(Apache-2.0; retained LICENSE and NOTICE).
SourceBinaryH1HeckeCommute proves the original full H1 Hecke commutativity;
SourceOriginalResidualH1Eigensystem consumes it without an extra premise.
-/

namespace Dubon2026
noncomputable section
open scoped TensorProduct
open TensorProduct


variable {M : Type*} [AddCommGroup M] [Module ℤ M] [Module.Finite ℤ M]
  {F : Type*} [Field F] {ι : Type*}

open scoped IsMulCommutative in

private theorem characterTensorEigenvector (t : ι → Module.End ℤ M) (A : Subalgebra ℤ (Module.End ℤ M)) [IsMulCommutative ↥A]
    (htA : ∀ i, t i ∈ A) (χ : ↥A →ₐ[ℤ] F) :
    ∃ y : F ⊗[ℤ] M, y ≠ 0 ∧ ∀ i, (t i).baseChange F y = χ ⟨t i, htA i⟩ • y := by
  cases Subsingleton.elim (inferInstance : Module ℤ M) (AddCommGroup.toIntModule M)
  letI : CommRing ↥A := inferInstance
  haveI : Module.Finite (↥A) M := Module.Finite.of_restrictScalars_finite ℤ (↥A) M
  letI : Algebra (↥A) F := (χ : ↥A →+* F).toAlgebra
  haveI : IsScalarTower ℤ (↥A) F := IsScalarTower.of_algebraMap_eq fun r => (χ.commutes r).symm
  haveI : Nontrivial (F ⊗[↥A] M) := sourceFaithfulModule_nontrivial_characterFiber

  let π : F ⊗[ℤ] M →ₗ[F] F ⊗[↥A] M := TensorProduct.mapOfCompatibleSMul (↥A) ℤ F F M
  have hπ : Function.Surjective π := TensorProduct.mapOfCompatibleSMul_surjective (↥A) ℤ F F M
  have key : ∀ (a : ↥A) (c : F) (m : M), (a • c) ⊗ₜ[↥A] m = c ⊗ₜ[↥A] (a • m) := fun a c m =>
    Quotient.sound' <| AddConGen.Rel.of _ _ <| TensorProduct.Eqv.of_smul _ _ _
  have hπt : ∀ i y, π ((t i).baseChange F y) = χ ⟨t i, htA i⟩ • π y := by
    intro i y
    induction y using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, smul_zero]
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | tmul c m =>
      rw [LinearMap.baseChange_tmul]
      change c ⊗ₜ[↥A] ((⟨t i, htA i⟩ : ↥A) • m) = χ ⟨t i, htA i⟩ • (c ⊗ₜ[↥A] m)
      rw [← key, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
      rfl

  haveI : Module.Finite F (F ⊗[ℤ] M) := Module.Finite.base_change ℤ F M
  have hP : LinearMap.ker π ≠ ⊤ := by
    intro h
    obtain ⟨q, hq⟩ := exists_ne (0 : F ⊗[↥A] M)
    obtain ⟨y, rfl⟩ := hπ q
    have : y ∈ LinearMap.ker π := by rw [h]; trivial
    exact hq (LinearMap.mem_ker.mp this)
  have hcomm : ∀ i j, Commute ((t i).baseChange F) ((t j).baseChange F) := by
    intro i j
    have hij : t i * t j = t j * t i :=
      Subtype.ext_iff.mp (mul_comm (⟨t i, htA i⟩ : ↥A) (⟨t j, htA j⟩ : ↥A))
    change (t i).baseChange F * (t j).baseChange F = (t j).baseChange F * (t i).baseChange F
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← LinearMap.baseChange_comp,
      ← LinearMap.baseChange_comp, ← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, hij]
  exact sourceCommutingOperators_exists_prescribedEigenvector (fun i => (t i).baseChange F) hcomm (fun i => χ ⟨t i, htA i⟩)
    (LinearMap.ker π) hP (fun i y => by rw [LinearMap.mem_ker, map_sub, map_smul, hπt, sub_self])

/-- Every character of an actual finite-module algebra of commuting operators
occurs on a nonzero tensor eigenvector, with the prescribed value on every generator. -/
theorem sourceOperatorCharacter_exists_tensorEigenvector (t : ι → Module.End ℤ M) (ht : ∀ i j, Commute (t i) (t j))
    (χ : ↥(Algebra.adjoin ℤ (Set.range t)) →ₐ[ℤ] F) :
    ∃ y : F ⊗[ℤ] M, y ≠ 0 ∧
      ∀ i, (t i).baseChange F y = χ ⟨t i, Algebra.subset_adjoin ⟨i, rfl⟩⟩ • y :=
  haveI : IsMulCommutative ↥(Algebra.adjoin ℤ (Set.range t)) := Algebra.isMulCommutative_adjoin ℤ (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩; exact (ht i j).eq)
  characterTensorEigenvector t _ (fun i => Algebra.subset_adjoin (Set.mem_range_self i)) χ


end
end Dubon2026
