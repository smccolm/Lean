import Mathlib.RingTheory.AdicCompletion.Algebra

/-! # Actual coefficient maps on all original adic quotients -/

namespace Dubon2026

noncomputable section

variable {O R A : Type*} [CommRing O] [CommRing R] [CommRing A]
  [Algebra O R] [Algebra O A]

/-- An original ideal-compatible coefficient map preserves every actual ideal power. -/
theorem adicCoefficientMap_pow (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (n : ℕ) :
    I ^ n ≤ Ideal.comap f.toRingHom (J ^ n) := by
  have hp : I ^ n ≤ (Ideal.comap f.toRingHom J) ^ n := Ideal.pow_right_mono hf n
  exact hp.trans (Ideal.le_comap_pow f.toRingHom n)

/-- The original coefficient map induces a genuine map on its actual nth adic quotient. -/
def adicCoefficientQuotientMap (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (n : ℕ) :
    (R ⧸ I ^ n) →ₐ[O] (A ⧸ J ^ n) :=
  Ideal.Quotient.liftₐ (I ^ n) ((Ideal.Quotient.mkₐ O (J ^ n)).comp f)
    (fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mpr (adicCoefficientMap_pow I J f hf n hx))

/-- The genuine adic quotient map evaluates every original quotient class by the actual coefficient map. -/
theorem adicCoefficientQuotientMap_mk (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) (n : ℕ) (x : R) :
    adicCoefficientQuotientMap I J f hf n (Ideal.Quotient.mk (I ^ n) x) =
      Ideal.Quotient.mk (J ^ n) (f x) := rfl

/-- All actual adic quotient maps commute with the literal original transition maps. -/
theorem adicCoefficientQuotientMap_transition (I : Ideal R) (J : Ideal A) (f : R →ₐ[O] A)
    (hf : I ≤ Ideal.comap f.toRingHom J) {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right hmn)).comp
      (adicCoefficientQuotientMap I J f hf n) =
    (adicCoefficientQuotientMap I J f hf m).comp
      (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right hmn)) := by
  apply Ideal.Quotient.algHom_ext O
  apply AlgHom.ext
  intro x
  rfl

/-- The actual ring-valued adic evaluations commute with their genuine original quotient transitions. -/
theorem adicCompletion_eval_transition (I : Ideal R) {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  obtain ⟨r, rfl⟩ := AdicCompletion.mk_surjective I R x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn r

end
end Dubon2026
