import Dubon2026.FiniteActionUnitNorm

/-! # Exact norm and cocycle transfer through actual injective coefficient maps -/

namespace Dubon2026
noncomputable section

open scoped BigOperators

variable {G V U : Type} [Group G] [CommGroup V] [CommGroup U]
  [MulDistribMulAction G V] [MulDistribMulAction G U]
  (j : V →* U) (hj : Function.Injective j)
  (heq : ∀ (g : G) (v : V), j (g • v) = g • j v)

include heq in
/-- The original equivariant coefficient map preserves the literal finite action norm. -/
theorem equivariant_unit_map_norm [Fintype G] (v : V) :
    j (finiteActionUnitNorm G V v) = finiteActionUnitNorm G U (j v) := by
  change j (∏ g : G, g • v) = ∏ g : G, g • j v
  rw [map_prod]
  exact Finset.prod_congr rfl (fun g _ => heq g v)

include hj heq in
/-- Exact original norm preimages descend through an injective equivariant
map when the actual displayed subgroups have the same coefficient image. -/
theorem injective_unit_norm_preimages [Fintype G]
    (T : Subgroup V) (S : Subgroup U)
    (hmem : ∀ v : V, v ∈ T ↔ j v ∈ S)
    (honto : ∀ u : U, u ∈ S → ∃ v : V, v ∈ T ∧ j v = u)
    (hnorm : ∀ u : U, u ∈ S → (∀ g : G, g • u = u) →
      ∃ v : U, v ∈ S ∧ finiteActionUnitNorm G U v = u)
    (u : V) (hu : u ∈ T) (hinv : ∀ g : G, g • u = u) :
    ∃ v : V, v ∈ T ∧ finiteActionUnitNorm G V v = u := by
  have hi : ∀ g : G, g • j u = j u := by
    intro g
    rw [← heq, hinv]
  obtain ⟨w, hw, hn⟩ := hnorm (j u) ((hmem u).mp hu) hi
  obtain ⟨v, hv, hjv⟩ := honto w hw
  refine ⟨v, hv, hj ?_⟩
  rw [equivariant_unit_map_norm j heq, hjv, hn]

include hj heq in
/-- Exact original multiplicative coboundaries descend through the same
injective equivariant coefficient map, preserving every original cocycle value. -/
theorem injective_unit_cocycle_preimages
    (T : Subgroup V) (S : Subgroup U)
    (hmem : ∀ v : V, v ∈ T ↔ j v ∈ S)
    (honto : ∀ u : U, u ∈ S → ∃ v : V, v ∈ T ∧ j v = u)
    (hcob : ∀ c : G → U,
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S) →
        ∃ v : U, v ∈ S ∧ ∀ g, (g • v) / v = c g)
    (c : G → V) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hcT : ∀ g, c g ∈ T) :
    ∃ v : V, v ∈ T ∧ ∀ g, (g • v) / v = c g := by
  have hcj : ∀ g h, j (c (g * h)) = (g • j (c h)) * j (c g) := by
    intro g h
    rw [hc, map_mul, heq]
  obtain ⟨w, hw, hcw⟩ := hcob (fun g => j (c g)) hcj
    (fun g => (hmem (c g)).mp (hcT g))
  obtain ⟨v, hv, hjv⟩ := honto w hw
  refine ⟨v, hv, fun g => hj ?_⟩
  rw [map_div, heq, hjv, hcw]

end
end Dubon2026
