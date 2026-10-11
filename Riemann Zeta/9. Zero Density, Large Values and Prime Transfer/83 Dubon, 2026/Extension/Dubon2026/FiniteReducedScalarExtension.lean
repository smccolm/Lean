import Dubon2026.FiniteReducedTensorPointSeparation
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic

/-! # Reducedness of the actual geometric scalar extensions -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

/-- A genuine finite reduced algebra over the original perfect field remains reduced after arbitrary field extension. The proof uses the derived formal étaleness of that same algebra and its actual tensor base change. -/
theorem finiteReducedAlgebra_scalarExtension_isReduced
    {F K A : Type*} [Field F] [PerfectField F] [Field K] [Algebra F K]
    [CommRing A] [Algebra F A] [Module.Finite F A] [IsReduced A] :
    IsReduced (K ⊗[F] A) := by
  letI := finiteReducedAlgebra_formallyEtale (F := F) (A := A)
  exact Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[F] A)

/-- If the original finite coordinate algebra has reduced generic fiber over the perfect field, then its actual geometric fiber is reduced. The literal iterated tensor product is identified with the original geometric scalar extension by the pinned base-change cancellation equivalence. -/
theorem finiteReducedGenericFiber_geometric_isReduced
    {R F K A : Type*} [CommRing R] [Field F] [PerfectField F]
    [Algebra R F] [Field K] [Algebra R K] [Algebra F K] [IsScalarTower R F K]
    [CommRing A] [Algebra R A] [Module.Finite R A] [IsReduced (F ⊗[R] A)] :
    IsReduced (K ⊗[R] A) := by
  letI := finiteReducedAlgebra_scalarExtension_isReduced (F := F) (K := K) (A := F ⊗[R] A)
  let e := Algebra.TensorProduct.cancelBaseChange R F K K A
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- Flat scalar extension of an actual subalgebra injects into the same original extended coordinate algebra and therefore inherits its reducedness. -/
theorem reducedScalarExtension_subalgebra
    {R S A : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [CommRing A] [Algebra R A] [IsReduced (S ⊗[R] A)] (C : Subalgebra R A) :
    IsReduced (S ⊗[R] C) := by
  let i := Algebra.TensorProduct.map (AlgHom.id S S) C.val
  have hi : Function.Injective i :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := S) C.val.toLinearMap
      Subtype.val_injective
  exact isReduced_of_injective i.toRingHom hi

end
end Dubon2026
