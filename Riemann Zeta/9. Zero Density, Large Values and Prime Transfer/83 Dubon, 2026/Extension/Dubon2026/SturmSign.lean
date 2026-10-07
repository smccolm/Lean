/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Sign

/- Port of leanprover/hex-real-roots-mathlib at
53ce31466dc5ff520463249d470119c1e0006e22 for the pinned Lean 4.30 toolchain.
Original source and Apache 2.0 license: ../../Dependencies/SturmSource/. -/

/-!
# Signs of continuous nonvanishing functions

This file backports the general sign lemmas used by the Sturm development.
-/

namespace Dubon2026

variable {α : Type*} [Zero α] [TopologicalSpace α] [LinearOrder α] [OrderTopology α]

/-- The sign of a continuous function is continuous wherever the function is nonzero. -/
theorem continuousOn_sign_of_ne_zero {β : Type*} [TopologicalSpace β] {f : β → α} {s : Set β}
    (hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
    ContinuousOn (fun x => SignType.sign (f x)) s := by
  refine (continuousOn_of_forall_continuousAt fun y hy => ?_).comp' hf (Set.mapsTo_image _ _)
  obtain ⟨x, hx, rfl⟩ := hy
  exact continuousAt_sign_of_ne_zero (h0 x hx)

/-- A continuous nonvanishing function has constant sign on a preconnected set. -/
theorem sign_eq_on_preconnected_of_ne_zero {β : Type*} [TopologicalSpace β] {f : β → α}
    {s : Set β} (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (h0 : ∀ x ∈ s, f x ≠ 0) {x y : β} (hx : x ∈ s) (hy : y ∈ s) :
    SignType.sign (f x) = SignType.sign (f y) :=
  hs.constant (continuousOn_sign_of_ne_zero hf h0) hx hy

end Dubon2026
