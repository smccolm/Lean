import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic.LinearCombination

/-! # A genuine scalar orthogonal projection determines its original range -/

namespace Dubon2026

/-- An actual orthogonal projection acting scalarly on a nonzero containing subspace has zero range or that entire subspace. -/
theorem scalarProjection_eq_bot_or_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (p q : Submodule ℂ V) [p.HasOrthogonalProjection] (hpq : p ≤ q)
    (x : V) (hx : x ∈ q) (hn : x ≠ 0)
    (hs : ∃ a : ℂ, ∀ v ∈ q, p.starProjection v = a • v) : p = ⊥ ∨ p = q := by
  obtain ⟨a, ha⟩ := hs
  have hid : p.starProjection (p.starProjection x) = p.starProjection x :=
    p.starProjection_eq_self_iff.mpr (p.starProjection_apply_mem x)
  have hPa := ha (p.starProjection x) (hpq (p.starProjection_apply_mem x))
  rw [hid, ha x hx, smul_smul] at hPa
  have haa : a * a = a := (smul_left_injective ℂ hn) hPa.symm
  have hz : a * (a - 1) = 0 := by linear_combination haa
  rcases mul_eq_zero.mp hz with ha0 | ha1
  · left
    apply (Submodule.eq_bot_iff p).mpr
    intro v hv
    have he := ha v (hpq hv)
    rw [p.starProjection_eq_self_iff.mpr hv, ha0, zero_smul] at he
    exact he
  · right
    have ha1' : a = 1 := sub_eq_zero.mp ha1
    apply le_antisymm hpq
    intro v hv
    apply p.starProjection_eq_self_iff.mp
    simpa only [ha1', one_smul] using ha v hv

end Dubon2026
