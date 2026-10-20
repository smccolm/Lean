import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Extending the original coefficient reduction to all algebraic integers.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual modular Galois association -> the characteristic-p
specialization of the integral Hecke eigencharacter. The published residual
association route needs a map from all algebraic integers to an algebraically
closed residue field. Native lying-over and algebraic embedding results
extend the given reduction while preserving every original coefficient.
-/

namespace Dubon2026
noncomputable section

/-- A reduction of an integral subring extends to the integral overring in an
algebraically closed field, with its original values unchanged. -/
theorem sourceIntegralReduction_exists_extension
    {A B K : Type*} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra.IsIntegral A B]
    (hi : Function.Injective (algebraMap A B)) (χ : A →+* K) :
    ∃ φ : B →+* K, φ.comp (algebraMap A B) = χ := by
  letI : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  obtain ⟨Q, _, hQ, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker χ) (⊥ : Ideal B)
      (by simpa only [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hi]
        using (bot_le : (⊥ : Ideal A) ≤ RingHom.ker χ))
  letI : Q.IsPrime := hQ
  let R := A ⧸ Q.comap (algebraMap A B)
  let S := B ⧸ Q
  let ψ : R →+* K := Ideal.Quotient.lift _ χ (by
    intro a ha
    exact (show a ∈ RingHom.ker χ from hcomap ▸ ha))
  have hψ : Function.Injective ψ := by
    apply RingHom.lift_injective_of_ker_le_ideal
    exact hcomap.ge
  letI : Algebra R K := ψ.toAlgebra
  letI : Module.IsTorsionFree R K := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  letI : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Ideal.algebraMap_quotient_injective
  let j : S →ₐ[R] K := IsAlgClosed.lift
  refine ⟨j.toRingHom.comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  exact j.commutes (Ideal.Quotient.mk (Q.comap (algebraMap A B)) a)

end
end Dubon2026
