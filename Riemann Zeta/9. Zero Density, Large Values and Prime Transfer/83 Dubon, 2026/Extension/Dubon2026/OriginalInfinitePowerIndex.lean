/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Dubon2026.OriginalInfiniteUnitPowerRoots
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Sign.Basic

/-! # The exact original infinite-place unit power indices

Adapted from retained ClassFieldTheory commit
 dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
 ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/ArchimedeanPowerIndex.
The actual original completion sign map has the even-power kernel and
both signs occur. Combined with actual odd-real and complex roots this
computes each archimedean factor in DUB-17's power-quotient cardinal product.
-/

namespace Dubon2026
noncomputable section
open NumberField
open scoped Classical
variable (K : Type) [Field K] (w : InfinitePlace K)

/-- The actual sign homomorphism on units of an original real completion. -/
def originalRealCompletionSign (hw : w.IsReal) : w.Completionˣ →* SignTypeˣ :=
  (Units.map (signHom : ℝ →*₀ SignType).toMonoidHom).comp
    (Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv).toMonoidHom

/-- The kernel condition for the original real sign map is literal positivity under the actual completion embedding. -/
theorem originalRealCompletionSign_eq_one_iff (hw : w.IsReal) (x : w.Completionˣ) :
    originalRealCompletionSign K w hw x = 1 ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw x.val := by
  rw [Units.ext_iff]
  exact sign_eq_one_iff

/-- Both signs occur in the actual original real completion. -/
theorem originalRealCompletionSign_surjective (hw : w.IsReal) :
    Function.Surjective (originalRealCompletionSign K w hw) := by
  let eu : w.Completionˣ ≃* ℝˣ :=
    Units.mapEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw).toMulEquiv
  intro s
  cases hs : (s : SignType) with
  | zero => exact False.elim (s.ne_zero hs)
  | neg =>
      refine ⟨eu.symm (-1), ?_⟩
      apply Units.ext
      simp [originalRealCompletionSign, eu, hs]
  | pos =>
      refine ⟨eu.symm 1, ?_⟩
      apply Units.ext
      simp [originalRealCompletionSign, eu, hs]

/-- At an original real place the positive even-power subgroup is exactly the actual sign kernel. -/
theorem originalRealCompletionSign_ker_eq_power (hw : w.IsReal)
    (n : ℕ) (hn : 0 < n) (he : Even n) :
    (originalRealCompletionSign K w hw).ker = (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range := by
  ext x
  change originalRealCompletionSign K w hw x = 1 ↔ _
  rw [originalRealCompletionSign_eq_one_iff]
  constructor
  · exact originalRealCompletionUnit_power_preimage K w hw n hn x
  · rintro ⟨y, rfl⟩
    let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    change 0 < e (y.val ^ n)
    rw [map_pow]
    apply he.pow_pos
    simpa only [map_zero] using e.injective.ne y.ne_zero

/-- The original archimedean local power index is two exactly for an even exponent at a real place, and one otherwise. -/
theorem originalInfinitePowerQuotient_card (n : ℕ) (hn : 0 < n) :
    Nat.card (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) =
      if w.IsReal ∧ Even n then 2 else 1 := by
  by_cases hw : w.IsReal
  · by_cases he : Even n
    · rw [if_pos ⟨hw, he⟩, ← originalRealCompletionSign_ker_eq_power K w hw n hn he,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
          (originalRealCompletionSign K w hw) (originalRealCompletionSign_surjective K w hw)).toEquiv,
        Nat.card_eq_fintype_card]
      decide
    · rw [if_neg (fun h => he h.2)]
      have hr : (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range = ⊤ :=
        MonoidHom.range_eq_top.mpr (originalRealCompletionUnit_oddPower_surjective K w hw n ((Nat.even_or_odd n).resolve_left he))
      rw [hr]
      haveI : Subsingleton (w.Completionˣ ⧸ (⊤ : Subgroup w.Completionˣ)) := QuotientGroup.subsingleton_quotient_top
      exact Nat.card_unique
  · rw [if_neg (fun h => hw h.1)]
    have hr : (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (originalComplexCompletionUnit_power_surjective K w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw) n hn)
    rw [hr]
    haveI : Subsingleton (w.Completionˣ ⧸ (⊤ : Subgroup w.Completionˣ)) := QuotientGroup.subsingleton_quotient_top
    exact Nat.card_unique

/-- Every positive-power quotient at an original infinite completion is finite. -/
theorem originalInfinitePowerQuotient_finite (n : ℕ) (hn : 0 < n) :
    Finite (w.Completionˣ ⧸ (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) := by
  apply Nat.finite_of_card_ne_zero
  rw [originalInfinitePowerQuotient_card K w n hn]
  split <;> decide

end
end Dubon2026
