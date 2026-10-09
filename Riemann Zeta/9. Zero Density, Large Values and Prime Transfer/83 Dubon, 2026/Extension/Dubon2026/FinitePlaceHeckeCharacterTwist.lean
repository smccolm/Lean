import Dubon2026.FinitePlaceHeckeLevelIndependence
import Dubon2026.RepresentationScalarTwist

/-! # Genuine local Hecke covariance under an actual scalar character twist -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (N p : ℕ) [NeZero N] [NeZero p] [Fact p.Prime] (hpN : p.Coprime N)
    (ρ : Representation ℂ (GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ)) V)
    (χ : GeneralLinearGroup (Fin 2)
      ((rationalPrimePlace p (Fact.out : p.Prime)).adicCompletion ℚ) →* ℂ)
    (z : ℂ)
    (hχ : ∀ i : Option (ZMod p), χ
      (GeneralLinearGroup.map (finiteAdelePlace (rationalPrimePlace p (Fact.out : p.Prime)))
        ((integralGamma0FiniteGL2Hom N (heckeUpperRepresentative p N hpN i)).val⁻¹ *
          (finiteAdelicHeckeDiagonal p)⁻¹)) = z)

include hχ

/-- The original finite coset sum scales by the actual character value on those same coset representatives. -/
theorem finitePlaceHeckeTrace_scalarTwist :
    finitePlaceHeckeTrace N p hpN (scalarTwistRepresentation ρ χ) =
      z • finitePlaceHeckeTrace N p hpN ρ := by
  ext x
  simp only [finitePlaceHeckeTrace, LinearMap.sum_apply, LinearMap.smul_apply,
    scalarTwistRepresentation_apply, hχ, Finset.smul_sum]

/-- A genuine local twisted intertwiner transports the actual original Hecke coset trace with its proved character scalar. -/
theorem finitePlaceHeckeTrace_character_intertwines
    (T : Representation.IntertwiningMap ρ (scalarTwistRepresentation ρ χ)) (x : V) :
    T (finitePlaceHeckeTrace N p hpN ρ x) = z • finitePlaceHeckeTrace N p hpN ρ (T x) := by
  have h := finitePlaceHeckeTrace_intertwines N p hpN ρ (scalarTwistRepresentation ρ χ)
    T.toLinearMap (Representation.IntertwiningMap.isIntertwining ρ (scalarTwistRepresentation ρ χ) T) x
  rw [finitePlaceHeckeTrace_scalarTwist N p hpN ρ χ z hχ, LinearMap.smul_apply] at h
  exact h

end
end Dubon2026
