/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Dubon2026.ContinuousCyclicGaloisNormQuotient
import Mathlib.Data.Real.Sign
import Mathlib.RingTheory.Complex
import Mathlib.Data.Real.Sqrt

/-! # The actual complex-to-real unit norm quotient

The sign kernel consists exactly of actual complex norms, by the original
complex norm-square formula and positive real square roots. The sign argument
is adapted from Apache-2.0 NYLL ClassFieldTheory at commit
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1, ArchimedeanNormQuotient.
This supplies the nontrivial archimedean H2 factor in DUB-17's idele formula.
No topology of the norm quotient is introduced.
-/

namespace Dubon2026
noncomputable section

/-- The sign of a nonzero real number, regarded as an integral unit. -/
def originalRealUnitsSign : ℝˣ →* ℤˣ :=
  Units.map
    ((SignType.castHom (α := ℤ)).comp
      (signHom (α := ℝ)))

/-- Coercing `originalRealUnitsSign x` to an integer recovers the usual sign of
the underlying nonzero real number. -/
@[simp]
theorem originalRealUnitsSign_coe (x : ℝˣ) :
    ((originalRealUnitsSign x : ℤˣ) : ℤ) =
      (SignType.sign (x : ℝ) : ℤ) :=
  rfl

/-- Both integral signs occur. -/
theorem originalRealUnitsSign_surjective :
    Function.Surjective originalRealUnitsSign := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact ⟨1, by simp [originalRealUnitsSign]⟩
  · exact ⟨-1, by
      apply Units.ext
      simp [originalRealUnitsSign]⟩

/-- A nonzero real unit has trivial sign precisely when it is positive. -/
@[simp]
theorem originalRealUnitsSign_eq_one_iff (x : ℝˣ) :
    originalRealUnitsSign x = 1 ↔ 0 < (x : ℝ) := by
  constructor
  · intro hx
    have hxv := congrArg Units.val hx
    have hs : SignType.sign (x : ℝ) = 1 := by
      cases hsign : SignType.sign (x : ℝ) <;>
        simp [originalRealUnitsSign_coe, hsign] at hxv ⊢
    exact sign_eq_one_iff.mp hs
  · intro hx
    apply Units.ext
    simp [originalRealUnitsSign, sign_pos hx]


/-- Actual complex norms are exactly the positive original real units. -/
theorem originalRealUnit_mem_complexNorm_iff (x : ℝˣ) :
    (∃ u : ℂˣ, Units.map (Algebra.norm ℝ (S := ℂ)) u = x) ↔ 0 < (x : ℝ) := by
  constructor
  · rintro ⟨u, rfl⟩
    change 0 < Algebra.norm ℝ (u : ℂ)
    rw [Algebra.norm_complex_apply, Complex.normSq_pos]
    exact Units.ne_zero u
  · intro hx
    let z : ℂ := (Real.sqrt (x : ℝ) : ℝ)
    have hz : z ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 hx))
    refine ⟨Units.mk0 z hz, ?_⟩
    apply Units.ext
    change Algebra.norm ℝ z = (x : ℝ)
    rw [Algebra.norm_complex_apply]
    simpa [z, Complex.normSq_ofReal] using Real.mul_self_sqrt hx.le

/-- The original additive sign map has exactly the actual field-norm range as kernel. -/
theorem originalRealUnitSign_ker :
    LinearMap.ker originalRealUnitsSign.toAdditive.toIntLinearMap =
      LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ)) := by
  ext u
  change originalRealUnitsSign u.toMul = 1 ↔ _
  rw [originalRealUnitsSign_eq_one_iff,
    ← originalRealUnit_mem_complexNorm_iff]
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨Additive.ofMul v, congrArg Additive.ofMul hv⟩
  · rintro ⟨v, hv⟩
    exact ⟨v.toMul, congrArg Additive.toMul hv⟩

/-- The original complex-to-real norm quotient is the actual two-element sign group. -/
def originalRealComplexNormQuotientEquiv :
    (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) ≃ₗ[ℤ]
      Additive ℤˣ :=
  (Submodule.quotEquivOfEq _ _ originalRealUnitSign_ker.symm).trans
    (originalRealUnitsSign.toAdditive.toIntLinearMap.quotKerEquivOfSurjective
      originalRealUnitsSign_surjective)

/-- Finiteness and order two of the actual norm quotient follow from the sign equivalence. -/
theorem originalRealComplexNormQuotient_card :
    Finite (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) ∧
    Nat.card (Additive ℝˣ ⧸ LinearMap.range (galoisUnitFieldNormLinear (K := ℝ) (L := ℂ))) = 2 := by
  refine ⟨Finite.of_equiv (Additive ℤˣ) originalRealComplexNormQuotientEquiv.symm.toEquiv, ?_⟩
  rw [Nat.card_congr originalRealComplexNormQuotientEquiv.toEquiv,
    Nat.card_congr Additive.toMul, Nat.card_eq_fintype_card, Fintype.card_units_int]

end
end Dubon2026
