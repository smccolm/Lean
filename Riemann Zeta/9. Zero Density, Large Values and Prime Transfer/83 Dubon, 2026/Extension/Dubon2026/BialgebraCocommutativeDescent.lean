import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.RingTheory.Flat.Basic

/-! # Cocommutativity through actual faithful or surjective coordinate maps -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing B] [Bialgebra R B]

/-- Actual flat tensor faithfulness reflects cocommutativity through an injective original bialgebra map. -/
theorem bialgebraIsCocomm_of_injective [Module.Flat R A] [Module.Flat R B]
    [Coalgebra.IsCocomm R B] (q : A →ₐc[R] B) (hq : Function.Injective q) :
    Coalgebra.IsCocomm R A := by
  have hi : Function.Injective (TensorProduct.map q.toLinearMap q.toLinearMap) :=
    TensorProduct.map_injective_of_flat_flat q.toLinearMap q.toLinearMap hq hq
  constructor
  apply LinearMap.ext
  intro a
  apply hi
  change TensorProduct.map q.toLinearMap q.toLinearMap
    (TensorProduct.comm R A A (Coalgebra.comul a)) =
      TensorProduct.map q.toLinearMap q.toLinearMap (Coalgebra.comul a)
  rw [TensorProduct.map_comm]
  have hd : TensorProduct.map q.toLinearMap q.toLinearMap (Coalgebra.comul a) =
      Coalgebra.comul (q a) := CoalgHomClass.map_comp_comul_apply q a
  rw [hd, Coalgebra.comm_comul]

/-- Actual surjective coordinate maps carry cocommutativity to the original quotient bialgebra. -/
theorem bialgebraIsCocomm_of_surjective [Coalgebra.IsCocomm R A]
    (q : A →ₐc[R] B) (hq : Function.Surjective q) : Coalgebra.IsCocomm R B := by
  constructor
  apply LinearMap.ext
  intro b
  obtain ⟨a, rfl⟩ := hq b
  have hd : TensorProduct.map q.toLinearMap q.toLinearMap (Coalgebra.comul a) =
      Coalgebra.comul (q a) := CoalgHomClass.map_comp_comul_apply q a
  change TensorProduct.comm R B B (Coalgebra.comul (q a)) = Coalgebra.comul (q a)
  rw [← hd, ← TensorProduct.map_comm, Coalgebra.comm_comul]

end
end Dubon2026
