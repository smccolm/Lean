import Dubon2026.AdicCoefficientQuotientMaps
import Mathlib.RingTheory.AdicCompletion.RingHom

/-! # The genuine completion map induced by an original coefficient homomorphism -/

namespace Dubon2026

noncomputable section

variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- The genuine nth target quotient evaluation of the original source completion. -/
def adicCoefficientCompletionQuotientMap (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (n : ℕ) :
    AdicCompletion I R →ₐ[O] A ⧸ J ^ n :=
  (adicCoefficientQuotientMap I J f hf n).comp
    ((AdicCompletion.evalₐ I n).restrictScalars O)

/-- The actual quotient evaluations of the original source completion form a genuine compatible family. -/
theorem adicCoefficientCompletionQuotientMap_transition
    (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right hmn)).comp
      (adicCoefficientCompletionQuotientMap I J f hf n) =
      adicCoefficientCompletionQuotientMap I J f hf m := by
  apply AlgHom.ext
  intro x
  have h := DFunLike.congr_fun (adicCoefficientQuotientMap_transition I J f hf hmn)
    (AdicCompletion.evalₐ I n x)
  change Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right hmn)
    (adicCoefficientQuotientMap I J f hf n (AdicCompletion.evalₐ I n x)) =
      adicCoefficientQuotientMap I J f hf m (AdicCompletion.evalₐ I m x)
  change _ = adicCoefficientQuotientMap I J f hf m
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x)) at h
  rw [adicCompletion_eval_transition I hmn] at h
  exact h

/-- The original coefficient map induces an actual map between the genuine adic completions. -/
def adicCoefficientCompletionMap (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) :
    AdicCompletion I R →ₐ[O] AdicCompletion J A :=
  AdicCompletion.liftAlgHom J (adicCoefficientCompletionQuotientMap I J f hf)
    (adicCoefficientCompletionQuotientMap_transition I J f hf)

/-- Every original quotient of the actual completed map is exactly the original induced quotient map. -/
theorem adicCoefficientCompletionMap_eval (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ J n (adicCoefficientCompletionMap I J f hf x) =
      adicCoefficientQuotientMap I J f hf n (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftAlgHom J _ _ n x

/-- The entire genuine completion map agrees with the original coefficient homomorphism on every original element. -/
theorem adicCoefficientCompletionMap_of (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (x : R) :
    adicCoefficientCompletionMap I J f hf (AdicCompletion.of I R x) =
      AdicCompletion.of J A (f x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [adicCoefficientCompletionMap_eval, AdicCompletion.evalₐ_of,
    adicCoefficientQuotientMap_mk, AdicCompletion.evalₐ_of]

/-- When the genuine target coefficient ring is complete, the original map extends to a map out of the actual source completion. -/
def adicCompleteCoefficientMap (I : Ideal R) (J : Ideal A) [IsAdicComplete J A]
    (f : R →ₐ[O] A) (hf : I ≤ Ideal.comap f.toRingHom J) :
    AdicCompletion I R →ₐ[O] A :=
  ((AdicCompletion.ofAlgEquiv J).symm.toAlgHom.restrictScalars O).comp
    (adicCoefficientCompletionMap I J f hf)

/-- The actual complete-target map recovers the original coefficient map on every original element. -/
theorem adicCompleteCoefficientMap_of (I : Ideal R) (J : Ideal A) [IsAdicComplete J A]
    (f : R →ₐ[O] A) (hf : I ≤ Ideal.comap f.toRingHom J) (x : R) :
    adicCompleteCoefficientMap I J f hf (AdicCompletion.of I R x) = f x := by
  change (AdicCompletion.ofAlgEquiv J).symm
    (adicCoefficientCompletionMap I J f hf (AdicCompletion.of I R x)) = _
  rw [adicCoefficientCompletionMap_of, AdicCompletion.ofAlgEquiv_symm_of]

end
end Dubon2026
