import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! The original parabolic Hecke span has a nonzero supported character fiber.
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


/-- A finite module has a nonzero character fiber when its annihilator maps to zero. -/
theorem sourceModule_nontrivial_characterFiber_of_annihilator {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] [Module.Finite A M] {F : Type*} [Field F] [Algebra A F]
    (hann : Module.annihilator A M ≤ RingHom.ker (algebraMap A F)) :
    Nontrivial (F ⊗[A] M) := by
  let p : PrimeSpectrum A := ⟨RingHom.ker (algebraMap A F), RingHom.ker_isPrime _⟩
  haveI : p.asIdeal.IsPrime := p.2
  have hsupp : p ∈ Module.support A M := by
    exact Module.mem_support_iff_of_finite.mpr hann
  haveI hnt : Nontrivial (p.asIdeal.ResidueField ⊗[A] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct p).mp hsupp

  have hunit : p.asIdeal.primeCompl ≤ (IsUnit.submonoid F).comap (algebraMap A F) := by
    intro a ha
    change IsUnit (algebraMap A F a)
    exact isUnit_iff_ne_zero.mpr ha
  letI : Algebra p.asIdeal.ResidueField F :=
    (Ideal.ResidueField.lift p.asIdeal (algebraMap A F) le_rfl hunit).toAlgebra
  haveI : IsScalarTower A p.asIdeal.ResidueField F := IsScalarTower.of_algebraMap_eq fun a =>
    (Ideal.ResidueField.lift_algebraMap p.asIdeal (algebraMap A F) le_rfl hunit a).symm
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A p.asIdeal.ResidueField F F M
  obtain ⟨⟨I, b⟩⟩ :=
    (inferInstance : Module.Free p.asIdeal.ResidueField (p.asIdeal.ResidueField ⊗[A] M))
  haveI : Nonempty I := b.index_nonempty
  let B := b.baseChange F
  have hB : B (Classical.arbitrary I) ≠ 0 := B.ne_zero _
  exact ⟨⟨e (B (Classical.arbitrary I)), 0, by simpa using hB⟩⟩


end
end Dubon2026
