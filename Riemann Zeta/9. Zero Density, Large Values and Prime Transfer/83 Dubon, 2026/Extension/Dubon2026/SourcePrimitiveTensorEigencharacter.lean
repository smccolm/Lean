import Dubon2026.SourcePrimitiveTensorOperators

/-! DUB-17/18 -> nonzero required primitive component. The literal
primitive eigencharacter evaluates the arithmetic projector to one.
This gives the nonzero normalization needed by its Tate realization. -/
namespace Dubon2026
noncomputable section
open Polynomial TensorProduct
variable (N : ℕ) [NeZero N]
local notation "TZ" => sourceOriginalIntegralHeckeAlgebra N 2

/-- The original primitive eigencharacter on the literal coefficient extension. -/
def primitiveTensorEigencharacter (f : PrimitiveCuspForm N 2) :
    sourcePrimitiveCoefficientField f ⊗[ℤ] TZ →+* sourcePrimitiveCoefficientField f :=
  integerCoefficientExtension (RingHom.id (sourcePrimitiveCoefficientField f))
    (sourcePrimitiveFieldHeckeCharacter f).toRingHom

theorem primitiveTensorEigencharacter_hecke (f : PrimitiveCuspForm N 2) (n : ℕ+) :
    primitiveTensorEigencharacter N f
      ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ] primitiveIntegralHeckeIndex N n) =
        sourcePrimitiveFieldCoefficient f n := by
  rw [primitiveTensorEigencharacter, integerCoefficientExtension_tmul, map_one, one_smul]
  exact sourcePrimitiveFieldHeckeCharacter_hecke f n

theorem primitiveTensorEigencharacter_annihilator (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) :
    primitiveTensorEigencharacter N f (primitiveGoodTensorAnnihilator N f s) = 0 := by
  have he := integerCoefficientExtension_shifted_squares
    (RingHom.id (sourcePrimitiveCoefficientField f)) (sourcePrimitiveFieldHeckeCharacter f).toRingHom
    s (fun q => primitiveIntegralHeckeIndex N ⟨q.val.val, q.val.property.pos⟩)
    (fun q => sourcePrimitiveFieldCoefficient f q.val.val)
  refine he.trans (Finset.sum_eq_zero fun q _ => ?_)
  let n : ℕ+ := ⟨q.val.val, q.val.property.pos⟩
  have ht : sourcePrimitiveFieldHeckeCharacter f (primitiveIntegralHeckeIndex N n) =
      primitiveTensorEigencharacter N f
        ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ] primitiveIntegralHeckeIndex N n) := by
    simpa only [map_one, one_smul] using
      (integerCoefficientExtension_tmul (RingHom.id (sourcePrimitiveCoefficientField f))
        (sourcePrimitiveFieldHeckeCharacter f).toRingHom 1 (primitiveIntegralHeckeIndex N n)).symm
  have hn := ht.trans (primitiveTensorEigencharacter_hecke N f n)
  exact (congrArg (fun z : sourcePrimitiveCoefficientField f =>
    (z - sourcePrimitiveFieldCoefficient f n • 1) ^ 2) hn).trans (by
      simp only [smul_eq_mul, mul_one, sub_self, zero_pow (by decide : 2 ≠ 0)])

theorem primitiveTensorEigencharacter_projector (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : Polynomial (sourcePrimitiveCoefficientField f)) (hP : P.eval 0 = 1) :
    primitiveTensorEigencharacter N f (primitiveGoodTensorProjector N f s P) = 1 := by
  have he := integerCoefficientExtension_aeval
    (RingHom.id (sourcePrimitiveCoefficientField f)) (sourcePrimitiveFieldHeckeCharacter f).toRingHom
    (primitiveGoodTensorAnnihilator N f s) P
  refine he.trans ?_
  change aeval (primitiveTensorEigencharacter N f (primitiveGoodTensorAnnihilator N f s))
    (P.map (RingHom.id _)) = 1
  rw [primitiveTensorEigencharacter_annihilator, Polynomial.map_id]
  exact hP

theorem primitiveGoodTensorProjector_ne_zero (f : PrimitiveCuspForm N 2)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : Polynomial (sourcePrimitiveCoefficientField f)) (hP : P.eval 0 = 1) :
    primitiveGoodTensorProjector N f s P ≠ 0 := by
  intro hz
  have h := primitiveTensorEigencharacter_projector N f s P hP
  rw [hz, map_zero] at h
  exact zero_ne_one h

end
end Dubon2026
