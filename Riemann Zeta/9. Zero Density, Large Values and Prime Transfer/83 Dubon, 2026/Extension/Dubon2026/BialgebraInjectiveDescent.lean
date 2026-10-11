import Mathlib.RingTheory.Bialgebra.Hom
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic

/-! # Original bialgebra identities restrict through genuine free coordinate inclusions -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A] [Module.Free R A]
  [CommRing B] [Algebra R B] [Module.Free R B]

/-- Coassociativity restricts to actual free subcoordinates when their displayed comultiplication is compatible with the original one. -/
theorem bialgebraInjective_coassoc (q : B →ₐ[R] A) (hq : Function.Injective q)
    (d : B →ₐ[R] B ⊗[R] B)
    (hd : (Algebra.TensorProduct.map q q).comp d = (Bialgebra.comulAlgHom R A).comp q) :
    (Algebra.TensorProduct.assoc R R R B B B).toAlgHom.comp
      ((Algebra.TensorProduct.map d (.id R B)).comp d) =
      (Algebra.TensorProduct.map (.id R B) d).comp d := by
  let q₂ := Algebra.TensorProduct.map q q
  let q₃ := Algebra.TensorProduct.map q q₂
  let da := Bialgebra.comulAlgHom R A
  have hq₂ : Function.Injective q₂ :=
    TensorProduct.map_injective_of_flat_flat q.toLinearMap q.toLinearMap hq hq
  have hq₃ : Function.Injective q₃ :=
    TensorProduct.map_injective_of_flat_flat q.toLinearMap q₂.toLinearMap hq hq₂
  have hleft : (Algebra.TensorProduct.map da (.id R A)).comp q₂ =
      (Algebra.TensorProduct.map q₂ q).comp (Algebra.TensorProduct.map d (.id R B)) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    exact congrArg (fun z => z ⊗ₜ[R] q y) (AlgHom.congr_fun hd x).symm
  have hright : (Algebra.TensorProduct.map (.id R A) da).comp q₂ =
      q₃.comp (Algebra.TensorProduct.map (.id R B) d) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    exact congrArg (fun z => q x ⊗ₜ[R] z) (AlgHom.congr_fun hd y).symm
  have hassoc : (Algebra.TensorProduct.assoc R R R A A A).toAlgHom.comp
      (Algebra.TensorProduct.map q₂ q) =
      q₃.comp (Algebra.TensorProduct.assoc R R R B B B).toAlgHom := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext_threefold
    intro x y z
    rfl
  apply AlgHom.ext
  intro b
  apply hq₃
  change q₃ ((Algebra.TensorProduct.assoc R R R B B B)
    ((Algebra.TensorProduct.map d (.id R B)) (d b))) =
      q₃ ((Algebra.TensorProduct.map (.id R B) d) (d b))
  calc
    _ = (Algebra.TensorProduct.assoc R R R A A A)
        ((Algebra.TensorProduct.map q₂ q) ((Algebra.TensorProduct.map d (.id R B)) (d b))) :=
      (AlgHom.congr_fun hassoc _).symm
    _ = (Algebra.TensorProduct.assoc R R R A A A)
        ((Algebra.TensorProduct.map da (.id R A)) (q₂ (d b))) :=
      congrArg (Algebra.TensorProduct.assoc R R R A A A) (AlgHom.congr_fun hleft _).symm
    _ = (Algebra.TensorProduct.assoc R R R A A A)
        ((Algebra.TensorProduct.map da (.id R A)) (da (q b))) := by
      rw [show q₂ (d b) = da (q b) from AlgHom.congr_fun hd b]
    _ = (Algebra.TensorProduct.map (.id R A) da) (da (q b)) := Coalgebra.coassoc_apply (q b)
    _ = (Algebra.TensorProduct.map (.id R A) da) (q₂ (d b)) := by
      rw [show q₂ (d b) = da (q b) from AlgHom.congr_fun hd b]
    _ = _ := AlgHom.congr_fun hright _

omit [Module.Free R A] in
/-- The original left counit law restricts through the actual injective coordinate map. -/
theorem bialgebraInjective_leftCounit (q : B →ₐ[R] A) (hq : Function.Injective q)
    (d : B →ₐ[R] B ⊗[R] B) (e : B →ₐ[R] R)
    (hd : (Algebra.TensorProduct.map q q).comp d = (Bialgebra.comulAlgHom R A).comp q)
    (he : e = (Bialgebra.counitAlgHom R A).comp q) :
    (Algebra.TensorProduct.map e (.id R B)).comp d =
      (Algebra.TensorProduct.lid R B).symm := by
  have hi : Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R) q) :=
    TensorProduct.map_injective_of_flat_flat (LinearMap.id : R →ₗ[R] R) q.toLinearMap
      Function.injective_id hq
  have h : (Algebra.TensorProduct.map (.id R R) q).comp (Algebra.TensorProduct.map e (.id R B)) =
      (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (.id R A)).comp
        (Algebra.TensorProduct.map q q) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    exact congrArg (fun z => z ⊗ₜ[R] q y) (AlgHom.congr_fun he x)
  apply AlgHom.ext
  intro b
  apply hi
  calc
    _ = (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (.id R A))
        ((Algebra.TensorProduct.map q q) (d b)) := AlgHom.congr_fun h _
    _ = (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (.id R A))
        (Coalgebra.comul (q b)) := congrArg
          (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (.id R A))
          (AlgHom.congr_fun hd b)
    _ = 1 ⊗ₜ[R] q b := Coalgebra.rTensor_counit_comul (q b)
    _ = _ := rfl

omit [Module.Free R B] in
/-- The original right counit law restricts through the actual injective coordinate map. -/
theorem bialgebraInjective_rightCounit (q : B →ₐ[R] A) (hq : Function.Injective q)
    (d : B →ₐ[R] B ⊗[R] B) (e : B →ₐ[R] R)
    (hd : (Algebra.TensorProduct.map q q).comp d = (Bialgebra.comulAlgHom R A).comp q)
    (he : e = (Bialgebra.counitAlgHom R A).comp q) :
    (Algebra.TensorProduct.map (.id R B) e).comp d =
      (Algebra.TensorProduct.rid R R B).symm := by
  have hi : Function.Injective (Algebra.TensorProduct.map q (AlgHom.id R R)) :=
    TensorProduct.map_injective_of_flat_flat q.toLinearMap (LinearMap.id : R →ₗ[R] R)
      hq Function.injective_id
  have h : (Algebra.TensorProduct.map q (.id R R)).comp (Algebra.TensorProduct.map (.id R B) e) =
      (Algebra.TensorProduct.map (.id R A) (Bialgebra.counitAlgHom R A)).comp
        (Algebra.TensorProduct.map q q) := by
    apply Algebra.TensorProduct.ext'
    intro x y
    exact congrArg (fun z => q x ⊗ₜ[R] z) (AlgHom.congr_fun he y)
  apply AlgHom.ext
  intro b
  apply hi
  calc
    _ = (Algebra.TensorProduct.map (.id R A) (Bialgebra.counitAlgHom R A))
        ((Algebra.TensorProduct.map q q) (d b)) := AlgHom.congr_fun h _
    _ = (Algebra.TensorProduct.map (.id R A) (Bialgebra.counitAlgHom R A))
        (Coalgebra.comul (q b)) := congrArg
          (Algebra.TensorProduct.map (.id R A) (Bialgebra.counitAlgHom R A))
          (AlgHom.congr_fun hd b)
    _ = q b ⊗ₜ[R] 1 := Coalgebra.lTensor_counit_comul (q b)
    _ = _ := rfl

/-- Construct the actual bialgebra on the original free subcoordinates from the genuine compatible coordinate maps, deriving every coalgebra identity. -/
abbrev bialgebraInjectiveDescent (q : B →ₐ[R] A) (hq : Function.Injective q)
    (d : B →ₐ[R] B ⊗[R] B) (e : B →ₐ[R] R)
    (hd : (Algebra.TensorProduct.map q q).comp d = (Bialgebra.comulAlgHom R A).comp q)
    (he : e = (Bialgebra.counitAlgHom R A).comp q) : Bialgebra R B :=
  Bialgebra.ofAlgHom d e (bialgebraInjective_coassoc q hq d hd)
    (bialgebraInjective_leftCounit q hq d e hd he)
    (bialgebraInjective_rightCounit q hq d e hd he)

end
end Dubon2026
