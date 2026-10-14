/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted for the original Dubon coefficient route from
Nyll/ClassFieldTheory/LubinTate/Padic/ChangedUniformizerCoefficient.lean at
dc55774a7fe03e742f2b4c6114aab5e7d01edfb1. The Apache 2.0 license is retained
in Dependencies/NYLL-ClassFieldTheory-LICENSE.txt.
-/

import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Data.ZMod.Basic

/-! # The actual Witt-unit coefficient for a changed rational prime uniformizer

The pinned Witt Frobenius rotation gives a unit, not merely a nonzero
fraction-field element. This supplies the linear coefficient equation for
the semilinear changed-uniformizer construction needed by the ramified
cyclotomic formula on DUB-17's principal-product and global-duality route.
The auxiliary finite field, its normed uniformizer and its Frobenius action
remain separate obligations.
-/
namespace Dubon2026
noncomputable section

/-- The actual completed-unramified Witt coefficient ring has a unit solution of the required semilinear unit equation. -/
theorem primeWitt_exists_frobenius_unit_rotation (p : ℕ) [Fact p.Prime]
    (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ) :
    ∃ ε : (WittVector p (AlgebraicClosure (ZMod p)))ˣ,
      WittVector.frobenius (ε : WittVector p (AlgebraicClosure (ZMod p))) =
        (ε : WittVector p (AlgebraicClosure (ZMod p))) * u := by
  let W := WittVector p (AlgebraicClosure (ZMod p))
  have h1 : (1 : W).coeff 0 ≠ 0 := by simp
  have hu : (u : W).coeff 0 ≠ 0 :=
    (u.isUnit.map WittVector.constantCoeff).ne_zero
  let e := WittVector.frobeniusRotation p h1 hu
  have he0 : e.coeff 0 ≠ 0 := by
    simpa only [e, WittVector.frobeniusRotation, WittVector.coeff_mk,
      WittVector.frobeniusRotationCoeff] using
      WittVector.RecursionBase.solution_nonzero p h1 hu
  obtain ⟨ε, hε⟩ := WittVector.isUnit_of_coeff_zero_ne_zero e he0
  refine ⟨ε, ?_⟩
  rw [hε]
  exact (mul_one _).symm.trans (WittVector.frobenius_frobeniusRotation p h1 hu)

end
end Dubon2026
