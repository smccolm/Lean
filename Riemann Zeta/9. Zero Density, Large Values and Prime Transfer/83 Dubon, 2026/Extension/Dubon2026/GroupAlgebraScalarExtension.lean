import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Actual scalar extension of a possibly noncommutative group algebra -/

namespace Dubon2026

noncomputable section
open Module
open scoped TensorProduct

variable {G R S : Type*} [Group G] [CommRing R] [CommRing S] [Algebra R S]

/-- The genuine scalar-extension homomorphism on the original group algebra. -/
def groupAlgebraScalarExtension : S ⊗[R] MonoidAlgebra R G →ₐ[S] MonoidAlgebra S G :=
  AlgHom.liftEquiv R S (MonoidAlgebra R G) (MonoidAlgebra S G)
    (MonoidAlgebra.mapAlgHom G (Algebra.ofId R S))

/-- A simple tensor has its exact coefficient-extension formula. -/
theorem groupAlgebraScalarExtension_tmul (a : S) (x : MonoidAlgebra R G) :
    groupAlgebraScalarExtension (a ⊗ₜ[R] x) =
      a • MonoidAlgebra.mapRingHom G (algebraMap R S) x := rfl

/-- The actual scalar-extension homomorphism carries the original tensor basis to the original group basis. -/
theorem groupAlgebraScalarExtension_basis (g : G) :
    groupAlgebraScalarExtension ((MonoidAlgebra.basis G R).baseChange S g) =
      MonoidAlgebra.basis G S g := by
  simp [Basis.baseChange_apply, groupAlgebraScalarExtension_tmul]

/-- Scalar extension is an actual algebra isomorphism for every group, without a commutativity restriction. -/
def groupAlgebraScalarExtensionEquiv :
    S ⊗[R] MonoidAlgebra R G ≃ₐ[S] MonoidAlgebra S G := by
  let e := ((MonoidAlgebra.basis G R).baseChange S).equiv
    (MonoidAlgebra.basis G S) (Equiv.refl G)
  have he : (groupAlgebraScalarExtension (G := G) (R := R) (S := S)).toLinearMap =
      e.toLinearMap := by
    apply ((MonoidAlgebra.basis G R).baseChange S).ext
    intro g
    exact (groupAlgebraScalarExtension_basis (R := R) (S := S) g).trans
      (Basis.equiv_apply ((MonoidAlgebra.basis G R).baseChange S) g
        (MonoidAlgebra.basis G S) (Equiv.refl G)).symm
  apply AlgEquiv.ofBijective groupAlgebraScalarExtension
  change Function.Bijective
    (groupAlgebraScalarExtension (G := G) (R := R) (S := S)).toLinearMap
  rw [he]
  exact e.bijective

/-- The algebra isomorphism preserves the same original simple-tensor formula. -/
theorem groupAlgebraScalarExtensionEquiv_tmul (a : S) (x : MonoidAlgebra R G) :
    groupAlgebraScalarExtensionEquiv (a ⊗ₜ[R] x) =
      a • MonoidAlgebra.mapRingHom G (algebraMap R S) x :=
  groupAlgebraScalarExtension_tmul a x

/-- The original tensor identification is natural under every coefficient-algebra homomorphism. -/
theorem groupAlgebraScalarExtensionEquiv_natural {T : Type*} [CommRing T] [Algebra R T]
    (ψ : S →ₐ[R] T) (x : S ⊗[R] MonoidAlgebra R G) :
    MonoidAlgebra.mapRingHom G ψ.toRingHom (groupAlgebraScalarExtensionEquiv x) =
      groupAlgebraScalarExtensionEquiv
        (Algebra.TensorProduct.map ψ (AlgHom.id R (MonoidAlgebra R G)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        groupAlgebraScalarExtensionEquiv_tmul]
      ext g
      change ψ (a * algebraMap R S (x g)) = ψ a * algebraMap R T (x g)
      rw [map_mul, ψ.commutes]

end
end Dubon2026
