import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-! # Genuine coordinate inclusions in the tensor product Hopf algebra -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing B] [HopfAlgebra R B]

/-- The first original coordinate algebra includes into the actual tensor product as a bialgebra map. -/
def hopfTensorIncludeLeft : A →ₐc[R] A ⊗[R] B :=
  (Bialgebra.TensorProduct.map (BialgHom.id R A) (Bialgebra.unitBialgHom R B)).comp
    (Bialgebra.TensorProduct.rid R R A).symm.toBialgHom

/-- The first coordinate inclusion is the genuine tensor with the second unit. -/
theorem hopfTensorIncludeLeft_apply (a : A) :
    hopfTensorIncludeLeft (R := R) (B := B) a = a ⊗ₜ[R] (1 : B) := by
  change a ⊗ₜ[R] algebraMap R B 1 = _
  rw [map_one]

/-- The second original coordinate algebra includes into the actual tensor product as a bialgebra map. -/
def hopfTensorIncludeRight : B →ₐc[R] A ⊗[R] B :=
  (Bialgebra.TensorProduct.map (Bialgebra.unitBialgHom R A) (BialgHom.id R B)).comp
    (Bialgebra.TensorProduct.lid R B).symm.toBialgHom

/-- The second coordinate inclusion is the genuine tensor with the first unit. -/
theorem hopfTensorIncludeRight_apply (b : B) :
    hopfTensorIncludeRight (R := R) (A := A) b = (1 : A) ⊗ₜ[R] b := by
  change algebraMap R A 1 ⊗ₜ[R] b = _
  rw [map_one]

end
end Dubon2026
