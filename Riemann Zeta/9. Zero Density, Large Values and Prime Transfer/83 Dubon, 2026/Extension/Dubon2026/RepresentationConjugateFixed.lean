import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Complex.Basic

/-! # Genuine conjugation stabilizers fix the original translated vector -/

namespace Dubon2026

/-- If a genuine conjugate belongs to the original stabilizer, that group element fixes the actual inverse-diagonal translate. -/
theorem representation_conjugate_fixed {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (d : G) (v : V)
    (hv : ∀ g : K, ρ g.val v = v) (g : G) (hg : d * g * d⁻¹ ∈ K) :
    ρ g (ρ d⁻¹ v) = ρ d⁻¹ v := by
  have he := congrArg (ρ d⁻¹) (hv ⟨d * g * d⁻¹, hg⟩)
  rw [← Module.End.mul_apply, ← map_mul] at he
  have hmul : d⁻¹ * (d * g * d⁻¹) = g * d⁻¹ := by simp [← mul_assoc]
  rw [hmul, map_mul, Module.End.mul_apply] at he
  exact he

end Dubon2026
