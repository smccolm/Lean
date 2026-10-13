/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the retained dependency LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Dubon2026.OriginalInfinitePowerIndex
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-! # The original archimedean power-index product and signature

Adapted from the supported-idele index calculation in ClassFieldTheory,
commit dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. The previously proved actual
completion quotient indices are consumed directly. This combines their
archimedean factor with the degree factor in DUB-17's supported power index.
-/

namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField Classical
variable (K : Type) [Field K] [NumberField K]

/-- Only original real places and an even exponent contribute to the
archimedean product of the actual local power quotient orders. -/
theorem originalInfinitePowerQuotient_product (n : ℕ) (hn : 0 < n) :
    (∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸
      (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range)) =
      if Even n then 2 ^ InfinitePlace.nrRealPlaces K else 1 := by
  simp_rw [originalInfinitePowerQuotient_card K _ n hn]
  by_cases he : Even n
  · rw [if_pos he, InfinitePlace.prod_eq_prod_mul_prod]
    simp only [he, and_true]
    have hr : (∏ w : {w : InfinitePlace K // w.IsReal}, if w.1.IsReal then 2 else 1) =
        ∏ _w : {w : InfinitePlace K // w.IsReal}, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro w _
      rw [if_pos w.property]
    have hc : (∏ w : {w : InfinitePlace K // w.IsComplex}, if w.1.IsReal then 2 else 1) =
        ∏ _w : {w : InfinitePlace K // w.IsComplex}, (1 : ℕ) := by
      apply Finset.prod_congr rfl
      intro w _
      rw [if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr w.property)]
    rw [hr, hc]
    simp [InfinitePlace.nrRealPlaces]
  · simp [he]

/-- A primitive root and the original archimedean signature combine the
infinite local indices and field-degree factor into twice the place count. -/
theorem originalInfinitePowerQuotient_product_mul_degree
    (n : ℕ) (hn : 0 < n) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    (∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸
      (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range)) *
        n ^ Module.finrank ℚ K = n ^ (2 * Fintype.card (InfinitePlace K)) := by
  rw [originalInfinitePowerQuotient_product K n hn]
  have hsignature := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hplaces := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
  by_cases hlarge : 2 < n
  · have hreal : InfinitePlace.nrRealPlaces K = 0 :=
      InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hlarge hζ
    rw [hreal, zero_add] at hsignature hplaces
    have hdegree : Module.finrank ℚ K = 2 * Fintype.card (InfinitePlace K) := by omega
    rw [hreal, hdegree]
    simp
  · have hsmall : n = 1 ∨ n = 2 := by omega
    rcases hsmall with rfl | rfl
    · simp
    · rw [if_pos (by decide : Even 2), ← pow_add]
      congr 1
      omega

end
end Dubon2026
