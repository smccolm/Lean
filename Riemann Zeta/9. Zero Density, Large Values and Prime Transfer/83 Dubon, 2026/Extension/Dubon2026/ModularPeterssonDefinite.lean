/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors

Adapted from Modularforms/PeterssonInner.lean at
7c41b9b1747d47298f76bdb51f07031087702198.
-/
import Dubon2026.ModularPeterssonMeasure

/-! # Definiteness of the actual local Petersson integral

This uses holomorphic continuation from the interior of the standard domain.
It does not identify that domain with a fundamental domain for a higher-level group.
-/

namespace Dubon2026

open MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

theorem cuspForm_eq_zero_of_peterssonIntegral [Γ.IsArithmetic] (f : CuspForm Γ k) (hpet : peterssonInner k fd f f = 0) :
    f = 0 := by
  have hfdo : ∀ τ ∈ fdo, (⇑f) τ = 0 := fun τ hτ ↦
    eq_zero_on_fd_of_peterssonInner_self_eq_zero f hpet (fdo_subset_fd hτ)
  set τ₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩
  have hτ₀ : τ₀ ∈ fdo := by
    refine ⟨by norm_num [Complex.normSq_apply], ?_⟩
    change |(τ₀ : ℂ).re| < 1 / 2
    norm_num
  have hev := Filter.eventually_of_mem (isOpen_fdo.mem_nhds hτ₀) hfdo
  have h := UpperHalfPlane.eq_zero_of_frequently (CuspFormClass.holo f)
    (hev.filter_mono nhdsWithin_le_nhds).frequently
  ext τ
  exact congr_fun h τ


end Dubon2026
