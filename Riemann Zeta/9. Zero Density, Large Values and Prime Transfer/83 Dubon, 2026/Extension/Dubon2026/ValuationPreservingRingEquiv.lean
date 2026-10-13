import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.UniformRing

/-! # Continuity needed for original Galois transport of local fields

Exact preservation of the original valuations makes a ring equivalence
uniformly continuous. This supplies the completion map used in the
Galois-equivariant supported-idele sequence for DUB-17's norm-index route.
-/

namespace Dubon2026
noncomputable section
open scoped Topology
open MonoidWithZeroHom.ValueGroup₀
variable {A B Γ : Type*} [Field A] [Field B] [LinearOrderedCommGroupWithZero Γ]
  [Valued A Γ] [Valued B Γ]

/-- Exact preservation of field valuations gives the required uniform continuity. -/
theorem valuationPreservingRingEquiv_uniformContinuous (f : A ≃+* B)
    (h : ∀ x : A, Valued.v (f x) = (Valued.v x : Γ)) : UniformContinuous f := by
  refine uniformContinuous_of_continuousAt_zero f.toAddMonoidHom ?_
  simp only [ContinuousAt, map_zero]
  rw [(Valued.hasBasis_nhds_zero A Γ).tendsto_iff (Valued.hasBasis_nhds_zero B Γ)]
  intro γ _
  obtain ⟨y, hy⟩ := restrict₀_surjective (Valued.v (R := B)) γ.val
  have hy0 : y ≠ 0 := by
    intro hz
    subst y
    exact Units.ne_zero γ (by simpa using hy.symm)
  let x := f.symm y
  have hx0 : x ≠ 0 := by simpa [x] using f.symm.injective.ne hy0
  refine ⟨Units.mk0 ((Valued.v (R := A) (Γ₀ := Γ)).restrict x) (by simp [Valuation.restrict_def, restrict₀_apply, hx0]), trivial, ?_⟩
  intro z hz
  change (Valued.v (R := B) (Γ₀ := Γ)).restrict (f z) < γ.val
  rw [← hy]
  change (Valued.v (R := B) (Γ₀ := Γ)).restrict (f z) < (Valued.v (R := B) (Γ₀ := Γ)).restrict y
  rw [Valuation.restrict_lt_iff]
  change (Valued.v (R := A) (Γ₀ := Γ)).restrict z < (Valued.v (R := A) (Γ₀ := Γ)).restrict x at hz
  rw [Valuation.restrict_lt_iff] at hz
  rw [h, ← f.apply_symm_apply y, h]
  exact hz

end
end Dubon2026
