import Mathlib.RingTheory.Bialgebra.Hom

/-! # Coalgebra identities descend through the original surjective coordinate map -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A]
  [CommRing B] [Algebra R B]

/-- A surjective original coordinate map and its genuine comultiplication compatibility derive coassociativity on the target. -/
theorem bialgebraSurjective_coassoc (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (d : B →ₐ[R] B ⊗[R] B)
    (hd : d.comp q = (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom R A)) :
    (Algebra.TensorProduct.assoc R R R B B B).toAlgHom.comp
      ((Algebra.TensorProduct.map d (.id R B)).comp d) =
      (Algebra.TensorProduct.map (.id R B) d).comp d := by
  let q₂ := Algebra.TensorProduct.map q q
  let q₃ := Algebra.TensorProduct.map q q₂
  let da := Bialgebra.comulAlgHom R A
  have hleft : (Algebra.TensorProduct.map d (.id R B)).comp q₂ =
      (Algebra.TensorProduct.map q₂ q).comp (Algebra.TensorProduct.map da (.id R A)) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    exact congrArg (fun x => x ⊗ₜ[R] q b) (AlgHom.congr_fun hd a)
  have hright : (Algebra.TensorProduct.map (.id R B) d).comp q₂ =
      q₃.comp (Algebra.TensorProduct.map (.id R A) da) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    exact congrArg (fun x => q a ⊗ₜ[R] x) (AlgHom.congr_fun hd b)
  have hassoc : (Algebra.TensorProduct.assoc R R R B B B).toAlgHom.comp
      (Algebra.TensorProduct.map q₂ q) =
      q₃.comp (Algebra.TensorProduct.assoc R R R A A A).toAlgHom := by
    apply AlgHom.toLinearMap_injective
    apply TensorProduct.ext_threefold
    intro a b c
    rfl
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hq b
  change (Algebra.TensorProduct.assoc R R R B B B)
    ((Algebra.TensorProduct.map d (.id R B)) (d (q a))) =
      (Algebra.TensorProduct.map (.id R B) d) (d (q a))
  rw [show d (q a) = q₂ (da a) from AlgHom.congr_fun hd a]
  calc
    _ = (Algebra.TensorProduct.assoc R R R B B B)
        ((Algebra.TensorProduct.map q₂ q)
          ((Algebra.TensorProduct.map da (.id R A)) (da a))) :=
      congrArg (Algebra.TensorProduct.assoc R R R B B B) (AlgHom.congr_fun hleft (da a))
    _ = q₃ ((Algebra.TensorProduct.assoc R R R A A A)
        ((Algebra.TensorProduct.map da (.id R A)) (da a))) :=
      AlgHom.congr_fun hassoc _
    _ = q₃ ((Algebra.TensorProduct.map (.id R A) da) (da a)) :=
      congrArg q₃ (Coalgebra.coassoc_apply a)
    _ = _ := (AlgHom.congr_fun hright (da a)).symm

/-- Genuine counit compatibility and surjectivity derive the original left counit law on the target. -/
theorem bialgebraSurjective_leftCounit (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (d : B →ₐ[R] B ⊗[R] B) (e : B →ₐ[R] R)
    (hd : d.comp q = (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom R A))
    (he : e.comp q = Bialgebra.counitAlgHom R A) :
    (Algebra.TensorProduct.map e (.id R B)).comp d =
      (Algebra.TensorProduct.lid R B).symm := by
  have h : (Algebra.TensorProduct.map e (.id R B)).comp (Algebra.TensorProduct.map q q) =
      (Algebra.TensorProduct.map (.id R R) q).comp
        (Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (.id R A)) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    exact congrArg (fun x => x ⊗ₜ[R] q b) (AlgHom.congr_fun he a)
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hq b
  change (Algebra.TensorProduct.map e (.id R B)) (d (q a)) = 1 ⊗ₜ[R] q a
  rw [show d (q a) = (Algebra.TensorProduct.map q q) (Coalgebra.comul a) from
    AlgHom.congr_fun hd a]
  calc
    _ = (Algebra.TensorProduct.map (.id R R) q)
        ((Algebra.TensorProduct.map (Bialgebra.counitAlgHom R A) (.id R A))
          (Coalgebra.comul a)) := AlgHom.congr_fun h _
    _ = (Algebra.TensorProduct.map (.id R R) q) (1 ⊗ₜ[R] a) :=
      congrArg (Algebra.TensorProduct.map (.id R R) q) (Coalgebra.rTensor_counit_comul a)
    _ = _ := rfl

/-- Genuine counit compatibility and surjectivity derive the original right counit law on the target. -/
theorem bialgebraSurjective_rightCounit (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (d : B →ₐ[R] B ⊗[R] B) (e : B →ₐ[R] R)
    (hd : d.comp q = (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom R A))
    (he : e.comp q = Bialgebra.counitAlgHom R A) :
    (Algebra.TensorProduct.map (.id R B) e).comp d =
      (Algebra.TensorProduct.rid R R B).symm := by
  have h : (Algebra.TensorProduct.map (.id R B) e).comp (Algebra.TensorProduct.map q q) =
      (Algebra.TensorProduct.map q (.id R R)).comp
        (Algebra.TensorProduct.map (.id R A) (Bialgebra.counitAlgHom R A)) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    exact congrArg (fun x => q a ⊗ₜ[R] x) (AlgHom.congr_fun he b)
  apply AlgHom.ext
  intro b
  obtain ⟨a, rfl⟩ := hq b
  change (Algebra.TensorProduct.map (.id R B) e) (d (q a)) = q a ⊗ₜ[R] 1
  rw [show d (q a) = (Algebra.TensorProduct.map q q) (Coalgebra.comul a) from
    AlgHom.congr_fun hd a]
  calc
    _ = (Algebra.TensorProduct.map q (.id R R))
        ((Algebra.TensorProduct.map (.id R A) (Bialgebra.counitAlgHom R A))
          (Coalgebra.comul a)) := AlgHom.congr_fun h _
    _ = (Algebra.TensorProduct.map q (.id R R)) (a ⊗ₜ[R] 1) :=
      congrArg (Algebra.TensorProduct.map q (.id R R)) (Coalgebra.lTensor_counit_comul a)
    _ = _ := rfl

/-- The coalgebra axioms are derived through the original surjection; the target comultiplication and counit are the same given algebra maps. -/
abbrev bialgebraSurjectiveDescent (q : A →ₐ[R] B) (hq : Function.Surjective q)
    (d : B →ₐ[R] B ⊗[R] B) (e : B →ₐ[R] R)
    (hd : d.comp q = (Algebra.TensorProduct.map q q).comp (Bialgebra.comulAlgHom R A))
    (he : e.comp q = Bialgebra.counitAlgHom R A) : Bialgebra R B :=
  Bialgebra.ofAlgHom d e (bialgebraSurjective_coassoc q hq d hd)
    (bialgebraSurjective_leftCounit q hq d e hd he)
    (bialgebraSurjective_rightCounit q hq d e hd he)

end
end Dubon2026
