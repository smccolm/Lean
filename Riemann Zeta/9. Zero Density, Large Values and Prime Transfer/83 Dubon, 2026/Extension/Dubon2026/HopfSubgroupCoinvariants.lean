import Dubon2026.PIDKernelRetraction
import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite

/-! # Original invariant coordinates for an actual subgroup coaction -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing B] [Bialgebra R B]

/-- Restrict the second original comultiplication coordinate along the actual subgroup coordinate map. -/
def hopfSubgroupRightCoaction (q : A →ₐc[R] B) : A →ₐ[R] A ⊗[R] B :=
  (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom).comp (Bialgebra.comulAlgHom R A)

/-- The actual invariant coordinate subalgebra is the equalizer of subgroup coaction and the original unit inclusion. -/
def hopfSubgroupCoinvariants (q : A →ₐc[R] B) : Subalgebra R A :=
  AlgHom.equalizer (hopfSubgroupRightCoaction q) Algebra.TensorProduct.includeLeft

/-- Membership in the invariant algebra is the genuine original coaction identity. -/
theorem hopfSubgroupCoinvariants_mem (q : A →ₐc[R] B) (a : A) :
    a ∈ hopfSubgroupCoinvariants q ↔
      (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom) (Coalgebra.comul a) =
        a ⊗ₜ[R] (1 : B) := by
  rfl

/-- The invariant module is the kernel of the literal difference of the two original coordinate maps. -/
theorem hopfSubgroupCoinvariants_kernel (q : A →ₐc[R] B) :
    (hopfSubgroupCoinvariants q).toSubmodule =
      LinearMap.ker ((hopfSubgroupRightCoaction q).toLinearMap -
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toLinearMap) := by
  ext a
  change hopfSubgroupRightCoaction q a = a ⊗ₜ[R] (1 : B) ↔
    hopfSubgroupRightCoaction q a - a ⊗ₜ[R] (1 : B) = 0
  exact sub_eq_zero.symm

/-- The genuine original invariant coordinates are finite free over the original PID, as a submodule of the finite free original coordinate algebra. -/
theorem hopfSubgroupCoinvariants_finite_free [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R A] [Module.Free R A] (q : A →ₐc[R] B) :
    Module.Finite R (hopfSubgroupCoinvariants q) ∧
      Module.Free R (hopfSubgroupCoinvariants q) := by
  exact ⟨inferInstanceAs (Module.Finite R (hopfSubgroupCoinvariants q).toSubmodule),
    inferInstanceAs (Module.Free R (hopfSubgroupCoinvariants q).toSubmodule)⟩

/-- The original invariant-coordinate inclusion has a genuine linear retraction over the PID, derived from the actual coaction-difference kernel and torsion-free tensor target. -/
theorem hopfSubgroupCoinvariants_exists_retraction [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R A] [Module.Free R A] [Module.Free R B] (q : A →ₐc[R] B) :
    ∃ p : A →ₗ[R] hopfSubgroupCoinvariants q,
      p.comp (hopfSubgroupCoinvariants q).val.toLinearMap = LinearMap.id := by
  let f := (hopfSubgroupRightCoaction q).toLinearMap -
    (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B).toLinearMap
  obtain ⟨p, hp⟩ := pidKernel_exists_retraction f
  have hk := hopfSubgroupCoinvariants_kernel q
  let j := LinearEquiv.ofEq (LinearMap.ker f) (hopfSubgroupCoinvariants q).toSubmodule hk.symm
  refine ⟨j.toLinearMap.comp p, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx : x.val ∈ LinearMap.ker f := by
    rw [← hk]
    exact x.property
  change (j (p x.val)).val = x.val
  simpa only [j, LinearEquiv.coe_ofEq_apply, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.id_apply] using
    congrArg Subtype.val (LinearMap.congr_fun hp ⟨x.val, hx⟩)

end
end Dubon2026
