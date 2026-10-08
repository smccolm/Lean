import Mathlib.Algebra.Ring.Commute
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing

/-! # Exact normalized Casimir algebra from the three sl2 commutators -/

namespace Dubon2026

/-- The normalized quadratic expression in the half-diagonal, upper and lower generators. -/
def normalizedSl2Casimir {R : Type*} [Ring R] (A U F : R) : R := -A * A + A - U * F

/-- The compact-basis expression is the same quadratic expression whenever the compact generator is upper minus lower. -/
theorem normalizedSl2Casimir_eq_compact {R : Type*} [Ring R] (A U F K : R)
    (hK : K = U - F) : -A * A + A - U * U + U * K = normalizedSl2Casimir A U F := by
  rw [hK]
  unfold normalizedSl2Casimir
  noncomm_ring

/-- The genuine sl2 relations imply commutation of the normalized quadratic element with each generator. -/
theorem normalizedSl2Casimir_commutes {R : Type*} [Ring R] (A U F : R)
    (hAU : A * U - U * A = U) (hAF : A * F - F * A = -F)
    (hUF : U * F - F * U = A + A) :
    Commute (normalizedSl2Casimir A U F) A ∧
      Commute (normalizedSl2Casimir A U F) U ∧ Commute (normalizedSl2Casimir A U F) F := by
  constructor
  · change (-A * A + A - U * F) * A = A * (-A * A + A - U * F)
    linear_combination (norm := noncomm_ring) hAU * F + U * hAF
  constructor
  · change (-A * A + A - U * F) * U = U * (-A * A + A - U * F)
    linear_combination (norm := noncomm_ring) -A * hAU - hAU * A + U * hUF
  · change (-A * A + A - U * F) * F = F * (-A * A + A - U * F)
    linear_combination (norm := noncomm_ring) -A * hAF - hAF * A - hUF * F

end Dubon2026
