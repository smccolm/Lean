import Mathlib.RingTheory.Bialgebra.Equiv
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Genuine bialgebra comparison through original faithful coordinate inclusions -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B C : Type*} [CommRing R]
  [CommRing A] [Bialgebra R A] [Module.Free R A]
  [CommRing B] [Bialgebra R B]
  [CommRing C] [Bialgebra R C] [Module.Free R C]

omit [Module.Free R A] [Module.Free R C] in
/-- An original coordinate comparison through genuine bialgebra maps preserves the original counit. -/
theorem bialgebraCoordinateComparison_counit
    (i : C →ₐc[R] A) (j : B →ₐc[R] A) (e : B ≃ₐ[R] C)
    (h : i.toAlgHom.comp e.toAlgHom = j.toAlgHom) :
    (Bialgebra.counitAlgHom R C).comp e.toAlgHom = Bialgebra.counitAlgHom R B := by
  apply AlgHom.ext
  intro b
  calc
    _ = Coalgebra.counit (i (e b)) := (CoalgHomClass.counit_comp_apply i (e b)).symm
    _ = Coalgebra.counit (j b) := congrArg (Coalgebra.counit (R := R)) (AlgHom.congr_fun h b)
    _ = _ := CoalgHomClass.counit_comp_apply j b

/-- The original tensor-coordinate injection reflects the comultiplication diagram for a genuine algebra comparison. Thus the coordinate comparison respects the actual coalgebra operations, without assuming that compatibility. -/
theorem bialgebraCoordinateComparison_comul
    (i : C →ₐc[R] A) (hi : Function.Injective i) (j : B →ₐc[R] A) (e : B ≃ₐ[R] C)
    (h : i.toAlgHom.comp e.toAlgHom = j.toAlgHom) :
    (Algebra.TensorProduct.map e.toAlgHom e.toAlgHom).comp (Bialgebra.comulAlgHom R B) =
      (Bialgebra.comulAlgHom R C).comp e.toAlgHom := by
  have hit : Function.Injective (Algebra.TensorProduct.map i.toAlgHom i.toAlgHom) :=
    TensorProduct.map_injective_of_flat_flat i.toLinearMap i.toLinearMap hi hi
  have ht : (Algebra.TensorProduct.map i.toAlgHom i.toAlgHom).comp
      (Algebra.TensorProduct.map e.toAlgHom e.toAlgHom) =
        Algebra.TensorProduct.map j.toAlgHom j.toAlgHom := by
    apply Algebra.TensorProduct.ext'
    intro b c
    change i (e b) ⊗ₜ[R] i (e c) = j b ⊗ₜ[R] j c
    rw [show i (e b) = j b from AlgHom.congr_fun h b,
      show i (e c) = j c from AlgHom.congr_fun h c]
  apply AlgHom.ext
  intro b
  apply hit
  calc
    _ = (Algebra.TensorProduct.map j.toAlgHom j.toAlgHom) (Coalgebra.comul b) :=
      AlgHom.congr_fun ht _
    _ = Coalgebra.comul (j b) := CoalgHomClass.map_comp_comul_apply j b
    _ = Coalgebra.comul (i (e b)) :=
      congrArg (Coalgebra.comul (R := R)) (AlgHom.congr_fun h b).symm
    _ = _ := (CoalgHomClass.map_comp_comul_apply i (e b)).symm

/-- The actual algebra comparison through original faithful bialgebra inclusions is a genuine bialgebra equivalence, with both coalgebra diagrams derived. -/
def bialgebraCoordinateComparison
    (i : C →ₐc[R] A) (hi : Function.Injective i) (j : B →ₐc[R] A) (e : B ≃ₐ[R] C)
    (h : i.toAlgHom.comp e.toAlgHom = j.toAlgHom) : B ≃ₐc[R] C :=
  BialgEquiv.ofAlgEquiv e (bialgebraCoordinateComparison_counit i j e h)
    (bialgebraCoordinateComparison_comul i hi j e h)

end
end Dubon2026
