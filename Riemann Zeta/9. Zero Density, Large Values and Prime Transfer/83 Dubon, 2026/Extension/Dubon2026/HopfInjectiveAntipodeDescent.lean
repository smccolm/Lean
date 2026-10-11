import Dubon2026.CommutativeHopfPointsGroup
import Mathlib.RingTheory.Bialgebra.Hom

/-! # Original Hopf identities restrict through genuine coordinate inclusions -/

namespace Dubon2026
noncomputable section
open WithConv

variable {R A B : Type*} [CommRing R] [CommRing A] [HopfAlgebra R A]
  [CommRing B] [Bialgebra R B]

/-- The original left antipode identity restricts to actual subcoordinates through an injective bialgebra map and the literal original antipode diagram. -/
theorem hopfInjectiveAntipode_left (q : B →ₐc[R] A) (hq : Function.Injective q)
    (s : B →ₐ[R] B)
    (hs : q.toAlgHom.comp s = (commutativeHopfAntipode (R := R) (A := A)).comp q.toAlgHom) :
    LinearMap.mul' R B ∘ₗ s.toLinearMap.rTensor B ∘ₗ Coalgebra.comul =
      Algebra.linearMap R B ∘ₗ Coalgebra.counit := by
  apply LinearMap.ext
  intro b
  apply hq
  change q ((toConv s * toConv (AlgHom.id R B)) b) =
    q ((1 : WithConv (B →ₐ[R] B)) b)
  calc
    _ = (toConv (q.toAlgHom.comp s) * toConv (q.toAlgHom.comp (AlgHom.id R B))) b :=
      AlgHom.congr_fun (AlgHom.comp_convMul_distrib q.toAlgHom
        (toConv s) (toConv (AlgHom.id R B))) b
    _ = (toConv ((commutativeHopfAntipode (R := R) (A := A)).comp q.toAlgHom) *
        toConv ((AlgHom.id R A).comp q.toAlgHom)) b := by
      rw [hs, AlgHom.comp_id, AlgHom.id_comp]
    _ = (toConv (commutativeHopfAntipode (R := R) (A := A)) * toConv (AlgHom.id R A)) (q b) :=
      (AlgHom.congr_fun (AlgHom.convMul_comp_bialgHom_distrib
        (toConv (commutativeHopfAntipode (R := R) (A := A))) (toConv (AlgHom.id R A)) q) b).symm
    _ = (1 : WithConv (A →ₐ[R] A)) (q b) := by
      exact congrArg (fun f : WithConv (A →ₐ[R] A) => f (q b))
        (commutativeHopfPoints_inverse_mul (toConv (AlgHom.id R A)))
    _ = _ := by simp only [AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply,
      AlgHomClass.commutes]

/-- The original right antipode identity restricts through the same actual coordinate inclusion. -/
theorem hopfInjectiveAntipode_right (q : B →ₐc[R] A) (hq : Function.Injective q)
    (s : B →ₐ[R] B)
    (hs : q.toAlgHom.comp s = (commutativeHopfAntipode (R := R) (A := A)).comp q.toAlgHom) :
    LinearMap.mul' R B ∘ₗ s.toLinearMap.lTensor B ∘ₗ Coalgebra.comul =
      Algebra.linearMap R B ∘ₗ Coalgebra.counit := by
  letI : Group (WithConv (A →ₐ[R] A)) := commutativeHopfPointsGroup
  have hi : toConv (AlgHom.id R A) * toConv (commutativeHopfAntipode (R := R) (A := A)) = 1 :=
    mul_inv_cancel (toConv (AlgHom.id R A))
  apply LinearMap.ext
  intro b
  apply hq
  change q ((toConv (AlgHom.id R B) * toConv s) b) =
    q ((1 : WithConv (B →ₐ[R] B)) b)
  calc
    _ = (toConv (q.toAlgHom.comp (AlgHom.id R B)) * toConv (q.toAlgHom.comp s)) b :=
      AlgHom.congr_fun (AlgHom.comp_convMul_distrib q.toAlgHom
        (toConv (AlgHom.id R B)) (toConv s)) b
    _ = (toConv ((AlgHom.id R A).comp q.toAlgHom) *
        toConv ((commutativeHopfAntipode (R := R) (A := A)).comp q.toAlgHom)) b := by
      rw [hs, AlgHom.comp_id, AlgHom.id_comp]
    _ = (toConv (AlgHom.id R A) * toConv (commutativeHopfAntipode (R := R) (A := A))) (q b) :=
      (AlgHom.congr_fun (AlgHom.convMul_comp_bialgHom_distrib
        (toConv (AlgHom.id R A)) (toConv (commutativeHopfAntipode (R := R) (A := A))) q) b).symm
    _ = (1 : WithConv (A →ₐ[R] A)) (q b) := by rw [hi]
    _ = _ := by simp only [AlgHom.convOne_apply, CoalgHomClass.counit_comp_apply,
      AlgHomClass.commutes]

/-- Construct the genuine Hopf structure on actual subcoordinates, deriving both antipode laws from the original Hopf algebra. -/
abbrev hopfInjectiveAntipodeDescent (q : B →ₐc[R] A) (hq : Function.Injective q)
    (s : B →ₐ[R] B)
    (hs : q.toAlgHom.comp s = (commutativeHopfAntipode (R := R) (A := A)).comp q.toAlgHom) :
    HopfAlgebra R B where
  toBialgebra := inferInstance
  antipode := s.toLinearMap
  mul_antipode_rTensor_comul := hopfInjectiveAntipode_left q hq s hs
  mul_antipode_lTensor_comul := hopfInjectiveAntipode_right q hq s hs

end
end Dubon2026
