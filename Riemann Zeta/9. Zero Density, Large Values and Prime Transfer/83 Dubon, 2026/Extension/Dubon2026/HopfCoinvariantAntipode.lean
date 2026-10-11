import Dubon2026.HopfSubgroupCoinvariants
import Dubon2026.HopfAntipodeCoordinateDiagrams

/-! # Original antipode preserves actual subgroup-invariant coordinates -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A] [CommRing B] [HopfAlgebra R B]

/-- Original cocommutativity and the genuine subgroup coordinate map imply that the original antipode preserves its actual invariant coordinate algebra. -/
theorem hopfCoinvariant_antipode_mem (q : A →ₐc[R] B) (a : A)
    (ha : a ∈ hopfSubgroupCoinvariants q) :
    HopfAlgebra.antipode R a ∈ hopfSubgroupCoinvariants q := by
  rw [hopfSubgroupCoinvariants_mem] at ha ⊢
  let sa := commutativeHopfAntipode (R := R) (A := A)
  let sb := commutativeHopfAntipode (R := R) (A := B)
  have h : (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom).comp
        (Algebra.TensorProduct.map sa sa) =
      (Algebra.TensorProduct.map sa sb).comp
        (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    exact congrArg (fun z => sa x ⊗ₜ[R] z) (hopfCoordinateMap_antipode q y)
  calc
    _ = (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom)
        ((Algebra.TensorProduct.map sa sa) (Coalgebra.comul a)) := by
      rw [hopfCocommutative_antipode_comul]
    _ = (Algebra.TensorProduct.map sa sb)
        ((Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom) (Coalgebra.comul a)) :=
      AlgHom.congr_fun h _
    _ = (Algebra.TensorProduct.map sa sb) (a ⊗ₜ[R] (1 : B)) := by rw [ha]
    _ = _ := by simp [sa, sb, commutativeHopfAntipode_apply]

/-- The actual invariant-coordinate antipode is the restriction of the original antipode algebra map. -/
def hopfCoinvariantAntipode (q : A →ₐc[R] B) :
    hopfSubgroupCoinvariants q →ₐ[R] hopfSubgroupCoinvariants q :=
  ((commutativeHopfAntipode (R := R)).comp (hopfSubgroupCoinvariants q).val).codRestrict
    (hopfSubgroupCoinvariants q) (fun a => hopfCoinvariant_antipode_mem q a a.property)

/-- The genuine restricted antipode retains the exact original coordinate diagram. -/
theorem hopfCoinvariantAntipode_coordinate (q : A →ₐc[R] B) :
    (hopfSubgroupCoinvariants q).val.comp (hopfCoinvariantAntipode q) =
      (commutativeHopfAntipode (R := R)).comp (hopfSubgroupCoinvariants q).val := by
  rfl

end
end Dubon2026
