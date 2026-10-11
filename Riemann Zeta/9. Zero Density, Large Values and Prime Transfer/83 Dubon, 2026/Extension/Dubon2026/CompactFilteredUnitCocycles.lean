import Dubon2026.UnitCocycleCorrections
import Dubon2026.CompactFilteredExactness

/-! # Exact original multiplicative coboundaries from compact filtered corrections -/

namespace Dubon2026
noncomputable section

/-- Actual original finite-precision cocycle corrections converge to an
exact original unit coboundary by compactness of the initial subgroup. The
literal action and all original cocycle values are retained in the limit. -/
theorem unit_cocycle_coboundary_of_compact_filtration
    {G U : Type} [Group G] [CommGroup U] [MulDistribMulAction G U]
    [TopologicalSpace U] [IsTopologicalGroup U]
    (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)
    (hcompact : IsCompact (S 0 : Set U))
    (hclosed : ∀ j, IsClosed (S j : Set U))
    (hsep : ∀ u : U, (∀ j, u ∈ S j) → u = 1)
    (hcont : ∀ g : G, Continuous (fun u : U => g • u))
    (hcorrect : ∀ j (c : G → U),
      (∀ g h, c (g * h) = (g • c h) * c g) → (∀ g, c g ∈ S j) →
        ∃ u : U, u ∈ S j ∧ ∀ g, c g / ((g • u) / u) ∈ S (j + 1))
    (c : G → U) (hc : ∀ g h, c (g * h) = (g • c h) * c g)
    (hc0 : ∀ g, c g ∈ S 0) :
    ∃ u : U, u ∈ S 0 ∧ ∀ g, (g • u) / u = c g := by
  haveI : CompactSpace (S 0) := isCompact_iff_compactSpace.mp hcompact
  let f : S 0 → (G → U) := fun u g => (g • (u : U)) / (u : U)
  have hf : Continuous f := continuous_pi (fun g =>
    (hcont g |>.comp continuous_subtype_val).div' continuous_subtype_val)
  let C : ℕ → Set (G → U) := fun j => {z | ∀ g, c g / z g ∈ S j}
  have hC (j : ℕ) : IsClosed (C j) := by
    have he : C j = ⋂ g : G, (fun z : G → U => c g / z g) ⁻¹' (S j : Set U) := by
      ext z
      simp only [C, Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq]
      rfl
    rw [he]
    exact isClosed_iInter (fun g => (hclosed j).preimage
      (continuous_const.div' (continuous_apply g)))
  have hCs : (⋂ j, C j) = {c} := by
    ext z
    simp only [Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hz
      funext g
      exact (div_eq_one.mp (hsep (c g / z g) (fun j => hz j g))).symm
    · rintro rfl
      intro j g
      simp
  have happrox := unit_cocycle_filtered_approximations S hmono hcorrect c hc hc0
  obtain ⟨u, hu⟩ := compact_exists_of_nested_closed_image_approximations f hf C hC
    (fun j _ hz g => hmono j (hz g)) c hCs (fun j => by
      obtain ⟨u, hu, he⟩ := happrox j
      exact ⟨⟨u, hu⟩, he⟩)
  exact ⟨u, u.property, fun g => congrFun hu g⟩

end
end Dubon2026
