/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the upstream LICENSE.
Adapted from NYLL ClassFieldTheory, commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
Nyll/ClassFieldTheory/AlgebraicNumberTheory/SUnit/Rank.lean.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.NumberTheory.NumberField.ClassNumber

/-! # Actual prime-ideal class-number powers are principal

This is the missing full-rank input for the already constructed original
S-unit valuation map. It supplies S-unit coordinate vectors for the exact
S-unit rank and power-index calculation used in the global idele-class norm
index, hence global reciprocity, Selmer duality and DUB-17 continuation.
The existing S-unit kernel and finite-generation proofs will be reused.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField nonZeroDivisors

/-- The original prime ideal raised to the actual class number is principal.
This constructs the required principal ideal from finite class-group torsion. -/
theorem numberField_prime_classNumber_power_principal
    (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) :
    (v.asIdeal ^ NumberField.classNumber K).IsPrincipal := by
  have hv0 : v.asIdeal ^ NumberField.classNumber K ≠ 0 := pow_ne_zero _ v.ne_bot
  apply (ClassGroup.mk0_eq_one_iff (mem_nonZeroDivisors_iff_ne_zero.mpr hv0)).mp
  let I : (Ideal (𝓞 K))⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  change ClassGroup.mk0 (I ^ NumberField.classNumber K) = 1
  rw [map_pow]
  exact pow_card_eq_one (x := ClassGroup.mk0 I)

end
end Dubon2026
