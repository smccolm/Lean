import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.UnitInterval
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-! DUB-17/18 -> original Abel-Jacobi -> regular loop-period generation.
This is a necessary step in converting arbitrary actual path integrals into
the subgroup of the constructed primitive jumps. Adapted from
S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Reuse original cell compactness, coefficient pullback and primitive uniqueness;
no new ambient curve, manifold, compactness or primitive existence is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open Set Filter
open scoped Topology

theorem sub_sub_mem_of_atlas {X V ι : Type*} [TopologicalSpace X] [AddCommGroup V]
    (Λ : AddSubgroup V) (U : ι → Set X) (G : ι → X → V)
    (hΛ : ∀ i j, ∀ x ∈ U i ∩ U j, G i x - G j x ∈ Λ)
    {γ : unitInterval → X} (hγ : Continuous γ) (g : unitInterval → V)
    (hloc : ∀ t₀, ∃ i, IsOpen (U i) ∧ γ t₀ ∈ U i ∧ ∃ c : V, ∀ᶠ t in 𝓝 t₀, g t = G i (γ t) + c)
    {j₀ j₁ : ι} (hj₀ : γ 0 ∈ U j₀) (hj₁ : γ 1 ∈ U j₁) :
    g 1 - g 0 - (G j₁ (γ 1) - G j₀ (γ 0)) ∈ Λ := by
  classical
  choose i hio hiγ c hc using hloc
  set q : unitInterval → V ⧸ Λ := fun t => QuotientAddGroup.mk (g t - G (i t) (γ t)) with hq
  have hlc : IsLocallyConstant q := by
    refine (IsLocallyConstant.iff_eventually_eq q).2 fun t₀ => ?_
    have hin : ∀ᶠ t in 𝓝 t₀, γ t ∈ U (i t₀) :=
      hγ.continuousAt.preimage_mem_nhds ((hio t₀).mem_nhds (hiγ t₀))
    filter_upwards [hin, hc t₀] with t ht hgt
    simp only [hq]
    rw [QuotientAddGroup.eq]
    have h0 : g t₀ = G (i t₀) (γ t₀) + c t₀ := (hc t₀).self_of_nhds
    have h1 : G (i t) (γ t) - G (i t₀) (γ t) ∈ Λ := hΛ _ _ _ ⟨hiγ t, ht⟩
    have : -(g t - G (i t) (γ t)) + (g t₀ - G (i t₀) (γ t₀)) =
        G (i t) (γ t) - G (i t₀) (γ t) := by rw [hgt, h0]; abel
    rw [this]
    exact h1
  have hconst : q 1 = q 0 := hlc.apply_eq_of_preconnectedSpace (x := 1) (y := 0)
  simp only [hq] at hconst
  rw [QuotientAddGroup.eq] at hconst

  have h1 : G (i 1) (γ 1) - G j₁ (γ 1) ∈ Λ := hΛ _ _ _ ⟨hiγ 1, hj₁⟩
  have h0 : G (i 0) (γ 0) - G j₀ (γ 0) ∈ Λ := hΛ _ _ _ ⟨hiγ 0, hj₀⟩
  have h3 := Λ.sub_mem (Λ.add_mem hconst h0) h1
  have : -(g 1 - G (i 1) (γ 1)) + (g 0 - G (i 0) (γ 0)) + (G (i 0) (γ 0) - G j₀ (γ 0)) -
      (G (i 1) (γ 1) - G j₁ (γ 1)) = -(g 1 - g 0 - (G j₁ (γ 1) - G j₀ (γ 0))) := by abel
  rw [this] at h3
  simpa using Λ.neg_mem h3
end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
