/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import RiemannZeta.External.PNT.ResidueCalcOnRectangles
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# A finite-pole residue theorem for the sharp Perron contour

This theorem is adapted from `Zeta23.Analytic.residueTheorem_finset` in the
pinned Zeta23 `v1.0` source artifact.  It is reproduced in the isolated
Gafni--Tao package because the frozen Guth--Maynard dependency exposes the
single-pole rectangle theorem but not this finite-pole induction.
-/

open Complex Set Topology Filter Asymptotics Real

noncomputable section

namespace GafniTao

/-- Residue theorem on a rectangle for a finite set of simple principal
parts.  The hypotheses give the coefficient of `(s - p)⁻¹` directly, which
is the form needed for the pole at one, the zero residues, and the origin in
the sharp Perron integrand. -/
theorem residueTheorem_finset {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (S : Finset ℂ) (A : ℂ → ℂ)
    (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ (S : Set ℂ)))
    (near : ∀ p ∈ S,
      (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = ∑ p ∈ S, A p := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    have fHolo' : HolomorphicOn f (Rectangle z w) := by
      simpa using fHolo
    rw [Finset.sum_empty]
    show (1 / (2 * π * I)) • RectangleIntegral f z w = 0
    rw [fHolo'.vanishesOnRectangle subset_rfl, smul_zero]
  | @insert p S hpS ih =>
    have hp : Rectangle z w ∈ 𝓝 p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, Rectangle z w ∈ 𝓝 q :=
      fun q hq => hS q (Finset.mem_insert_of_mem hq)
    set P : ℂ → ℂ := fun s => A p / (s - p) with hP
    set f₁ : ℂ → ℂ := f - P with hf₁
    set f₂ : ℂ → ℂ := Function.update f₁ p (limUnder (𝓝[≠] p) f₁) with hf₂
    have hPdiff : ∀ s, s ≠ p → DifferentiableAt ℂ P s := by
      intro s hs
      have : s - p ≠ 0 := sub_ne_zero.mpr hs
      simp only [hP]
      fun_prop (disch := assumption)
    have hf₁holo :
        HolomorphicOn f₁ (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) := by
      refine fHolo.sub ?_
      intro s hs
      apply (hPdiff s ?_).differentiableWithinAt
      intro h
      apply hs.2
      simp [h]
    have hSclosed : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
    have hRS : Rectangle z w \ (S : Set ℂ) ∈ 𝓝 p := by
      apply Filter.inter_mem hp
      exact hSclosed.isOpen_compl.mem_nhds (by simpa using hpS)
    obtain ⟨U, hU, hbdd⟩ := IsBigO_to_BddAbove
      (near p (Finset.mem_insert_self p S))
    have hV : U ∩ (Rectangle z w \ (S : Set ℂ)) ∈ 𝓝 p :=
      Filter.inter_mem hU hRS
    have hf₁V : DifferentiableOn ℂ f₁
        ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p}) := by
      apply hf₁holo.mono
      rintro s ⟨⟨_, hsR, hsS⟩, hsp⟩
      refine ⟨hsR, ?_⟩
      simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨by simpa using hsp, by simpa using hsS⟩
    have hbddV : BddAbove
        (norm ∘ f₁ '' ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p})) :=
      hbdd.mono (image_mono (by
        intro x hx
        exact ⟨hx.1.1, hx.2⟩))
    have hf₂V : DifferentiableOn ℂ f₂
        (U ∩ (Rectangle z w \ (S : Set ℂ))) :=
      differentiableOn_update_limUnder_of_bddAbove hV hf₁V hbddV
    have hf₂eq : ∀ s, s ≠ p → f₂ s = f₁ s :=
      fun s hs => Function.update_of_ne hs _ _
    have hf₂holo : HolomorphicOn f₂ (Rectangle z w \ (S : Set ℂ)) := by
      intro s hs
      by_cases hsp : s = p
      · rw [hsp]
        exact (hf₂V.differentiableAt hV).differentiableWithinAt
      · have h1 : DifferentiableWithinAt ℂ f₁
            (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) s :=
          hf₁holo s ⟨hs.1, by
            simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
            exact ⟨hsp, by simpa using hs.2⟩⟩
        have hset : Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ) =
            (Rectangle z w \ (S : Set ℂ)) ∩ {p}ᶜ := by
          ext x
          simp [Finset.coe_insert, and_assoc, and_comm]
        rw [hset] at h1
        have hpc : {p}ᶜ ∈ 𝓝[Rectangle z w \ (S : Set ℂ)] s :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hsp)
        rw [differentiableWithinAt_inter' hpc] at h1
        refine h1.congr_of_eventuallyEq ?_ (hf₂eq s hsp)
        filter_upwards [hpc] with x hx
        exact hf₂eq x hx
    have near₂ : ∀ q ∈ S,
        (f₂ - fun s => A q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
      intro q hq
      have hqp : q ≠ p := fun h => hpS (h ▸ hq)
      have hev : ((f - fun s => A q / (s - q)) - P) =ᶠ[𝓝[≠] q]
          (f₂ - fun s => A q / (s - q)) := by
        have : {p}ᶜ ∈ 𝓝[≠] q :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hqp)
        filter_upwards [this] with s hs
        simp only [Pi.sub_apply, hf₂eq s hs, hf₁]
        ring
      have hPO : P =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
        have hc : ContinuousAt P q := (hPdiff q hqp).continuousAt
        exact (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      exact ((near q (Finset.mem_insert_of_mem hq)).sub hPO).congr'
        hev EventuallyEq.rfl
    have ih' := ih hS' hf₂holo near₂
    have hborder : EqOn f (f₂ + P) (RectangleBorder z w) := by
      intro s hs
      have hsp : s ≠ p :=
        fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      simp only [Pi.add_apply, hf₂eq s hsp, hf₁, Pi.sub_apply,
        sub_add_cancel]
    have hbS : ∀ s ∈ RectangleBorder z w, s ∈ Rectangle z w \ (S : Set ℂ) :=
      fun s hs => ⟨rectangleBorder_subset_rectangle z w hs,
        fun hsS => not_mem_rectangleBorder_of_rectangle_mem_nhds (hS' s hsS) hs⟩
    have hi₂ : RectangleBorderIntegrable f₂ z w :=
      ContinuousOn.rectangleBorder_integrable (hf₂holo.continuousOn.mono hbS)
    have hiP : RectangleBorderIntegrable P z w := by
      apply ContinuousOn.rectangleBorder_integrable
      intro s hs
      have hsp : s ≠ p :=
        fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      exact (hPdiff s hsp).continuousAt.continuousWithinAt
    rw [RectangleIntegral'_congr hborder, Finset.sum_insert hpS]
    show (1 / (2 * π * I)) • RectangleIntegral (f₂ + P) z w = _
    rw [RectangleBorderIntegrable.add hi₂ hiP, smul_add]
    show RectangleIntegral' f₂ z w + RectangleIntegral' P z w = _
    rw [ih', ResidueTheoremInRectangle hre him hp, add_comm]

end GafniTao
