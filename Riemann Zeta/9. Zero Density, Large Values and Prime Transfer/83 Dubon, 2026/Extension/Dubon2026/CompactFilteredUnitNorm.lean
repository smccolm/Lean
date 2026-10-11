import Dubon2026.FiniteActionUnitNorm
import Dubon2026.CompactFilteredExactness

/-! # Iterated original norm corrections and their actual compact limit -/

namespace Dubon2026
noncomputable section

variable (G U : Type) [Group G] [Fintype G] [CommGroup U] [MulDistribMulAction G U]
  (S : ℕ → Subgroup U) (hmono : ∀ j, S (j + 1) ≤ S j)

include hmono in
/-- Actual one-step corrections at every original level give an original
norm approximation to every finite precision. The correcting product stays
inside the original initial subgroup. -/
theorem finiteActionUnitNorm_filtered_approximations
    (hcorrect : ∀ j (u : U), u ∈ S j → (∀ g : G, g • u = u) →
      ∃ v : U, v ∈ S j ∧ u / finiteActionUnitNorm G U v ∈ S (j + 1))
    (u : U) (hu : u ∈ S 0) (hinv : ∀ g : G, g • u = u) :
    ∀ j, ∃ v : U, v ∈ S 0 ∧ u / finiteActionUnitNorm G U v ∈ S j := by
  have hsub : ∀ j, S j ≤ S 0 := by
    intro j
    induction j with
    | zero => exact le_rfl
    | succ j ih => exact (hmono j).trans ih
  intro j
  induction j with
  | zero => exact ⟨1, (S 0).one_mem, by simpa using hu⟩
  | succ j ih =>
    obtain ⟨v, hv, he⟩ := ih
    have hi : ∀ g : G, g • (u / finiteActionUnitNorm G U v) =
        u / finiteActionUnitNorm G U v := by
      intro g
      rw [smul_div', hinv, finiteActionUnitNorm_invariant]
    obtain ⟨w, hw, hnext⟩ := hcorrect j _ he hi
    refine ⟨v * w, (S 0).mul_mem hv (hsub j hw), ?_⟩
    rw [map_mul]
    simpa only [div_div] using hnext

include hmono in
/-- Genuine finite-precision norm corrections in the original nested closed
unit subgroups yield an exact original norm preimage by compactness. -/
theorem finiteActionUnitNorm_surjective_on_invariants_of_compact_filtration
    [TopologicalSpace U] [IsTopologicalGroup U]
    (hcompact : IsCompact (S 0 : Set U))
    (hclosed : ∀ j, IsClosed (S j : Set U))
    (hsep : ∀ u : U, (∀ j, u ∈ S j) → u = 1)
    (hcont : ∀ g : G, Continuous (fun u : U => g • u))
    (hcorrect : ∀ j (u : U), u ∈ S j → (∀ g : G, g • u = u) →
      ∃ v : U, v ∈ S j ∧ u / finiteActionUnitNorm G U v ∈ S (j + 1))
    (u : U) (hu : u ∈ S 0) (hinv : ∀ g : G, g • u = u) :
    ∃ v : U, v ∈ S 0 ∧ finiteActionUnitNorm G U v = u := by
  haveI : CompactSpace (S 0) := isCompact_iff_compactSpace.mp hcompact
  let f : S 0 → U := fun v => finiteActionUnitNorm G U v
  have hf : Continuous f :=
    (finiteActionUnitNorm_continuous G U hcont).comp continuous_subtype_val
  have happrox := finiteActionUnitNorm_filtered_approximations G U S hmono hcorrect u hu hinv
  obtain ⟨v, hv⟩ := compact_exists_of_nested_closed_image_approximations f hf
    (fun j => {z : U | u / z ∈ S j})
    (fun j => (hclosed j).preimage (continuous_const.div' continuous_id))
    (fun j _ hz => hmono j hz) u (by
      ext z
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hz
        exact (div_eq_one.mp (hsep (u / z) hz)).symm
      · rintro rfl
        simp) (fun j => by
      obtain ⟨v, hv, he⟩ := happrox j
      exact ⟨⟨v, hv⟩, he⟩)
  exact ⟨v, v.property, hv⟩

end
end Dubon2026
