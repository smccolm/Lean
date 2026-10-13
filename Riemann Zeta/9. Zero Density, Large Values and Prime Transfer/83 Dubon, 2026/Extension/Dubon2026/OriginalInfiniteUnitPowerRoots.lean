/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Dubon2026.AlgebraicallyClosedUnitPowerSequence
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Actual unit power preimages in original infinite completions

Adapted from retained ClassFieldTheory commit
 dc55774a7fe03e742f2b4c6114aab5e7d01edfb1,
 Idele/NormApproximation/InfinitePlaces and
 ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/ArchimedeanPowerIndex.
The pinned actual completion equivalences retain the original field and
units. These root constructions determine DUB-17's archimedean local
power indices in its supported-idele cardinal calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField
variable (K : Type) [Field K] (w : InfinitePlace K)

/-- Every positive original unit at a real place has an actual positive-exponent root in that same completion. -/
theorem originalRealCompletionUnit_power_preimage (hw : w.IsReal)
    (n : ℕ) (hn : 0 < n) (x : w.Completionˣ)
    (hx : 0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw x.val) :
    ∃ y : w.Completionˣ, y ^ n = x := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let eu : w.Completionˣ ≃* ℝˣ := Units.mapEquiv e.toMulEquiv
  let r : ℝ := (eu x).val ^ ((n : ℝ)⁻¹)
  have hr : r ^ n = (eu x).val := Real.rpow_inv_natCast_pow hx.le hn.ne'
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hr
    exact (eu x).ne_zero hr.symm
  refine ⟨eu.symm (Units.mk0 r hr0), ?_⟩
  apply eu.injective
  rw [map_pow, eu.apply_symm_apply]
  exact Units.ext hr

/-- Every odd power map is surjective on actual units of an original real completion. -/
theorem originalRealCompletionUnit_oddPower_surjective (hw : w.IsReal)
    (n : ℕ) (hn : Odd n) : Function.Surjective (powMonoidHom n : w.Completionˣ →* w.Completionˣ) := by
  intro x
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hx0 : e x.val ≠ 0 := by simpa only [map_zero] using e.injective.ne x.ne_zero
  have hn0 : 0 < n := hn.pos
  by_cases hx : 0 < e x.val
  · exact originalRealCompletionUnit_power_preimage K w hw n hn0 x hx
  · have hxneg : e x.val < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
    have hneg : 0 < e (-x).val := by
      change 0 < e (-x.val)
      rw [map_neg]
      exact neg_pos.mpr hxneg
    obtain ⟨y, hy⟩ := originalRealCompletionUnit_power_preimage K w hw n hn0 (-x) hneg
    refine ⟨-y, ?_⟩
    change (-y) ^ n = x
    rw [hn.neg_pow, hy, neg_neg]

/-- Every positive power map is surjective on actual units of an original complex completion. -/
theorem originalComplexCompletionUnit_power_surjective (hw : w.IsComplex)
    (n : ℕ) (hn : 0 < n) : Function.Surjective (powMonoidHom n : w.Completionˣ →* w.Completionˣ) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let eu : w.Completionˣ ≃* ℂˣ := Units.mapEquiv e.toMulEquiv
  intro x
  obtain ⟨y, hy⟩ := algebraicallyClosedUnitPower_surjective n hn (eu x)
  refine ⟨eu.symm y, ?_⟩
  apply eu.injective
  change eu ((eu.symm y) ^ n) = eu x
  rw [map_pow, eu.apply_symm_apply]
  exact hy

end
end Dubon2026
