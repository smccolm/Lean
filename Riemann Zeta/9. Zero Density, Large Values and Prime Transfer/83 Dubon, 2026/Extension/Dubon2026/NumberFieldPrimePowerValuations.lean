/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from NYLL ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/Rank.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Dubon2026.NumberFieldPrimePowerPrincipal
import Dubon2026.SUnitValuationKernel

/-! # Actual valuations of a prime-ideal power generator

The original class group supplies an actual integer with one nontrivial
valuation. These integers give independent vectors in the existing S-unit
valuation map, needed for its rank and the global norm-index route to DUB-17.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- An actual generator of the class-number power of an original prime ideal. -/
def numberFieldPrimePowerGenerator (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : 𝓞 K :=
  letI := numberField_prime_classNumber_power_principal K v
  Submodule.IsPrincipal.generator (v.asIdeal ^ NumberField.classNumber K)

/-- The chosen generator generates precisely the original prime-ideal power. -/
theorem numberFieldPrimePowerGenerator_span (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Ideal.span {numberFieldPrimePowerGenerator K v} =
      v.asIdeal ^ NumberField.classNumber K := by
  letI := numberField_prime_classNumber_power_principal K v
  simp [numberFieldPrimePowerGenerator]

/-- The prime-ideal power generator is nonzero. -/
theorem numberFieldPrimePowerGenerator_ne_zero (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) : numberFieldPrimePowerGenerator K v ≠ 0 := by
  intro h
  have hv := pow_ne_zero (NumberField.classNumber K) v.ne_bot
  rw [← numberFieldPrimePowerGenerator_span K v, h] at hv
  exact hv (by simp)

open Classical in
/-- Every original prime valuation of the actual generator is computed exactly. -/
theorem numberFieldPrimePowerGenerator_intValuation
    (K : Type*) [Field K] [NumberField K] (v w : HeightOneSpectrum (𝓞 K)) :
    w.intValuation (numberFieldPrimePowerGenerator K v) =
      WithZero.exp (if w = v then -(NumberField.classNumber K : ℤ) else 0) := by
  classical
  rw [w.intValuation_if_neg (numberFieldPrimePowerGenerator_ne_zero K v),
    numberFieldPrimePowerGenerator_span, Associates.mk_pow,
    Associates.count_pow (Associates.mk_ne_zero.mpr v.ne_bot)
      (Associates.irreducible_mk.mpr w.irreducible)]
  by_cases hw : w = v
  · subst w
    simp [Associates.count_self (Associates.irreducible_mk.mpr v.irreducible)]
  · have hne : Associates.mk w.asIdeal ≠ Associates.mk v.asIdeal := by
      intro h
      apply hw
      apply HeightOneSpectrum.ext
      exact associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)
    rw [Associates.count_eq_zero_of_ne
      (Associates.irreducible_mk.mpr w.irreducible)
      (Associates.irreducible_mk.mpr v.irreducible) hne]
    simp [hw]

end
end Dubon2026
