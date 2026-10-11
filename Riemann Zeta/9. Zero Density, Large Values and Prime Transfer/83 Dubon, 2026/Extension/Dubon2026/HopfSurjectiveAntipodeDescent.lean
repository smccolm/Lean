import Dubon2026.CommutativeHopfPointsGroup
import Mathlib.RingTheory.Bialgebra.Hom

/-! # Original antipode identities descend through a genuine coordinate surjection -/

namespace Dubon2026
noncomputable section
open WithConv

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing B] [Bialgebra R B]

/-- A compatible descended coordinate antipode satisfies the original left antipode identity, by surjectivity and the actual source Hopf inverse law. -/
theorem hopfSurjectiveAntipode_left (q : A →ₐc[R] B) (hq : Function.Surjective q)
    (s : B →ₐ[R] B)
    (hs : s.comp q.toAlgHom = q.toAlgHom.comp (commutativeHopfAntipode (R := R))) :
    LinearMap.mul' R B ∘ₗ s.toLinearMap.rTensor B ∘ₗ Coalgebra.comul =
      Algebra.linearMap R B ∘ₗ Coalgebra.counit := by
  apply LinearMap.ext
  intro b
  obtain ⟨a, rfl⟩ := hq b
  change (toConv s * toConv (AlgHom.id R B)) (q a) =
    (1 : WithConv (B →ₐ[R] B)) (q a)
  calc
    _ = (toConv (s.comp q.toAlgHom) * toConv ((AlgHom.id R B).comp q.toAlgHom)) a :=
      AlgHom.congr_fun (AlgHom.convMul_comp_bialgHom_distrib
        (toConv s) (toConv (AlgHom.id R B)) q) a
    _ = (1 : WithConv (A →ₐ[R] B)) a := by
      rw [hs, AlgHom.id_comp]
      exact congrArg (fun f : WithConv (A →ₐ[R] B) => f a)
        (commutativeHopfPoints_inverse_mul (toConv q.toAlgHom))
    _ = _ := by
      change algebraMap R B (Coalgebra.counit a) = algebraMap R B (Coalgebra.counit (q a))
      rw [CoalgHomClass.counit_comp_apply]

/-- The same actual coordinate compatibility derives the right antipode identity from the source point group's genuine right inverse law. -/
theorem hopfSurjectiveAntipode_right (q : A →ₐc[R] B) (hq : Function.Surjective q)
    (s : B →ₐ[R] B)
    (hs : s.comp q.toAlgHom = q.toAlgHom.comp (commutativeHopfAntipode (R := R))) :
    LinearMap.mul' R B ∘ₗ s.toLinearMap.lTensor B ∘ₗ Coalgebra.comul =
      Algebra.linearMap R B ∘ₗ Coalgebra.counit := by
  letI : Group (WithConv (A →ₐ[R] B)) := commutativeHopfPointsGroup
  have hi : toConv q.toAlgHom *
      toConv (q.toAlgHom.comp (commutativeHopfAntipode (R := R))) = 1 :=
    mul_inv_cancel (toConv q.toAlgHom)
  apply LinearMap.ext
  intro b
  obtain ⟨a, rfl⟩ := hq b
  change (toConv (AlgHom.id R B) * toConv s) (q a) =
    (1 : WithConv (B →ₐ[R] B)) (q a)
  calc
    _ = (toConv ((AlgHom.id R B).comp q.toAlgHom) * toConv (s.comp q.toAlgHom)) a :=
      AlgHom.congr_fun (AlgHom.convMul_comp_bialgHom_distrib
        (toConv (AlgHom.id R B)) (toConv s) q) a
    _ = (1 : WithConv (A →ₐ[R] B)) a := by
      rw [hs, AlgHom.id_comp]
      exact congrArg (fun f : WithConv (A →ₐ[R] B) => f a) hi
    _ = _ := by
      change algebraMap R B (Coalgebra.counit a) = algebraMap R B (Coalgebra.counit (q a))
      rw [CoalgHomClass.counit_comp_apply]

/-- Construct the Hopf structure on the actual target bialgebra from the original surjection and descended antipode, deriving both Hopf identities. -/
abbrev hopfSurjectiveAntipodeDescent (q : A →ₐc[R] B) (hq : Function.Surjective q)
    (s : B →ₐ[R] B)
    (hs : s.comp q.toAlgHom = q.toAlgHom.comp (commutativeHopfAntipode (R := R))) :
    HopfAlgebra R B where
  toBialgebra := inferInstance
  antipode := s.toLinearMap
  mul_antipode_rTensor_comul := hopfSurjectiveAntipode_left q hq s hs
  mul_antipode_lTensor_comul := hopfSurjectiveAntipode_right q hq s hs

end
end Dubon2026
