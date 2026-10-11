import Dubon2026.HopfSubgroupCoinvariants
import Dubon2026.AlgebraEqualizerBaseChange
import Mathlib.RingTheory.Bialgebra.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Actual subgroup coinvariants under flat scalar extension -/

namespace Dubon2026
noncomputable section
open scoped TensorProduct

variable {R S A B : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]

/-- The genuine scalar extension of the original subgroup coordinate bialgebra map. -/
def hopfBaseChangeCoordinateMap (q : A →ₐc[R] B) : S ⊗[R] A →ₐc[S] S ⊗[R] B :=
  Bialgebra.TensorProduct.map (BialgHom.id S S) q

/-- The actual tensor base-change distributivity map intertwines the original scalar-extended subgroup coaction with the coaction of the actual base-changed bialgebra map. -/
theorem hopfCoinvariantBaseChange_coaction (q : A →ₐc[R] B) (z : S ⊗[R] A) :
    TensorProduct.AlgebraTensorModule.distribBaseChange R S A B
      ((Algebra.TensorProduct.map (AlgHom.id S S) (hopfSubgroupRightCoaction q)) z) =
        hopfSubgroupRightCoaction (hopfBaseChangeCoordinateMap (S := S) q) z := by
  let d := TensorProduct.AlgebraTensorModule.distribBaseChange R S A B
  let c := Algebra.TensorProduct.map (AlgHom.id S S) (hopfSubgroupRightCoaction q)
  let cb := hopfSubgroupRightCoaction (hopfBaseChangeCoordinateMap (S := S) q)
  have h1 (a : A) : d (c ((1 : S) ⊗ₜ[R] a)) = cb ((1 : S) ⊗ₜ[R] a) := by
    change d ((1 : S) ⊗ₜ[R]
      ((Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom) (Coalgebra.comul a))) =
      (Algebra.TensorProduct.map (AlgHom.id S (S ⊗[R] A))
        (hopfBaseChangeCoordinateMap (S := S) q).toAlgHom)
          (Coalgebra.comul ((1 : S) ⊗ₜ[R] a))
    simp only [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
    generalize Coalgebra.comul (R := R) a = w
    induction w using TensorProduct.induction_on with
    | zero =>
      have hq : (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom) 0 = 0 :=
        (Algebra.TensorProduct.map (AlgHom.id R A) q.toAlgHom).toLinearMap.map_zero
      have hb : (Algebra.TensorProduct.map (AlgHom.id S (S ⊗[R] A))
          (hopfBaseChangeCoordinateMap (S := S) q).toAlgHom) 0 = 0 :=
        (Algebra.TensorProduct.map (AlgHom.id S (S ⊗[R] A))
          (hopfBaseChangeCoordinateMap (S := S) q).toAlgHom).toLinearMap.map_zero
      simp only [hq, TensorProduct.tmul_zero, LinearEquiv.map_zero, hb]
    | tmul x y => rfl
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  change d (c z) = cb z
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [show c 0 = 0 from c.toLinearMap.map_zero, d.map_zero,
      show cb 0 = 0 from cb.toLinearMap.map_zero]
  | tmul s a =>
    have ht : s ⊗ₜ[R] a = s • ((1 : S) ⊗ₜ[R] a) :=
      TensorProduct.tmul_eq_smul_one_tmul s a
    rw [ht]
    change d (c.toLinearMap (s • ((1 : S) ⊗ₜ[R] a))) =
      cb.toLinearMap (s • ((1 : S) ⊗ₜ[R] a))
    rw [c.toLinearMap.map_smul, d.map_smul, cb.toLinearMap.map_smul]
    exact congrArg (s • ·) (h1 a)
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The same actual tensor distributivity map sends the scalar-extended original unit inclusion to the unit inclusion in the genuine scalar-extended coordinate algebra. -/
theorem hopfCoinvariantBaseChange_unitInclusion (z : S ⊗[R] A) :
    TensorProduct.AlgebraTensorModule.distribBaseChange R S A B
      ((Algebra.TensorProduct.map (AlgHom.id S S)
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)) z) =
      z ⊗ₜ[S] (1 : S ⊗[R] B) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    have hz : (Algebra.TensorProduct.map (AlgHom.id S S)
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)) 0 = 0 :=
      (Algebra.TensorProduct.map (AlgHom.id S S)
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).toLinearMap.map_zero
    rw [hz, LinearEquiv.map_zero, TensorProduct.zero_tmul]
  | tmul s a => rfl
  | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]

/-- Under actual flat scalar extension, the original invariant coordinate subalgebra extends onto precisely the genuine base-changed subgroup coinvariants. The original coaction and unit diagrams transfer the pinned equalizer base-change theorem. -/
theorem hopfCoinvariantBaseChange_range [Module.Flat R S] (q : A →ₐc[R] B) :
    (Algebra.TensorProduct.map (AlgHom.id S S) (hopfSubgroupCoinvariants q).val).range =
      hopfSubgroupCoinvariants (hopfBaseChangeCoordinateMap (S := S) q) := by
  change (Algebra.TensorProduct.map (AlgHom.id S S)
    (AlgHom.equalizer (hopfSubgroupRightCoaction q)
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)).val).range = _
  rw [algebraEqualizerBaseChange_range]
  apply Subalgebra.ext
  intro z
  change (Algebra.TensorProduct.map (AlgHom.id S S) (hopfSubgroupRightCoaction q)) z =
      (Algebra.TensorProduct.map (AlgHom.id S S)
        (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] B)) z ↔
    hopfSubgroupRightCoaction (hopfBaseChangeCoordinateMap (S := S) q) z =
      z ⊗ₜ[S] (1 : S ⊗[R] B)
  constructor
  · intro h
    have hd := congrArg (TensorProduct.AlgebraTensorModule.distribBaseChange R S A B) h
    rwa [hopfCoinvariantBaseChange_coaction, hopfCoinvariantBaseChange_unitInclusion] at hd
  · intro h
    apply (TensorProduct.AlgebraTensorModule.distribBaseChange R S A B).injective
    rw [hopfCoinvariantBaseChange_coaction, hopfCoinvariantBaseChange_unitInclusion]
    exact h

end
end Dubon2026
