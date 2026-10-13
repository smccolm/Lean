/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-! # Original finite-place completion residue field

Adapted from Naganori Yamaguchi's Apache-2.0 ClassFieldTheory,
commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1, original Idele/LocallyCompact.
Only the original finite-place residue comparison and local compactness
are ported. They establish the actual local-field input needed for the
local stabilizer H2 order in DUB-17's original idele Herbrand formula.
The global duality, numerical Selmer and automorphy/descent chain remains open.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Valued
variable (K : Type*) [Field K] [NumberField K]

/-- An element integral at a finite place can be approximated by an
algebraic integer to positive valuation. -/
theorem original_exists_ringOfIntegers_approximation
    (v : HeightOneSpectrum (𝓞 K)) (y : K)
    (hy : v.valuation K y ≤ 1) :
    ∃ r : 𝓞 K, v.valuation K (y - algebraMap (𝓞 K) K r) < 1 := by
  let : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hy' : y ∈ v.valuationSubringAtPrime K := by
    rw [v.valuationSubringAtPrime_eq_valuationSubring]
    exact hy
  let y' : v.valuationSubringAtPrime K := ⟨y, hy'⟩
  obtain ⟨⟨a, d⟩, had⟩ := IsLocalization.surj v.asIdeal.primeCompl y'
  have hd : d.1 ∉ v.asIdeal := d.2
  have hdmk : Ideal.Quotient.mk v.asIdeal d.1 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk v.asIdeal a /
      Ideal.Quotient.mk v.asIdeal d.1)
  refine ⟨r, ?_⟩
  have hard : a - r * d.1 ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, map_mul, hr]
    field_simp
    simp
  have hvalard :
      v.valuation K (algebraMap (𝓞 K) K (a - r * d.1)) < 1 :=
    (v.valuation_lt_one_iff_mem (K := K) (a - r * d.1)).2 hard
  have hdval : v.valuation K (algebraMap (𝓞 K) K d.1) = 1 := by
    exact le_antisymm (v.valuation_le_one d.1)
      (not_lt.mp ((v.valuation_lt_one_iff_mem (K := K) d.1).not.mpr hd))
  have hadK :
      y * algebraMap (𝓞 K) K d.1 = algebraMap (𝓞 K) K a := by
    exact congrArg Subtype.val had
  rw [← mul_lt_mul_iff_right₀ (show
    0 < v.valuation K (algebraMap (𝓞 K) K d.1) by simp [hdval])]
  rw [← map_mul, mul_sub, mul_comm _ y, hadK, mul_comm _ (algebraMap (𝓞 K) K r),
    ← map_mul, ← map_sub, hdval, mul_one]
  exact hvalard

end
end Dubon2026
