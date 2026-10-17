import Dubon2026.OriginalNormalSubgroupInducedEmbedding
import Dubon2026.OriginalCoefficientRangeQuotient
import Dubon2026.OriginalRelationModuleSequence

/-! # The literal induced finite-coefficient sequence for relation dévissage

Use the existing range quotient of the actual induction unit. The resulting
short exact sequence retains finite prime-torsion coefficients and the
original normal-kernel action. Pinned adjunctions also preserve the genuine
relation sequence and projectivity of its free term. These discharge the
sequence inputs to DUB-17's remaining nontrivial-action relation extension.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {G : Type} [Group G] [Finite G] (N : Subgroup G) (B : Rep.{0} ℤ G)

/-- The actual induction unit and its literal range quotient. -/
def originalSubgroupInducedSequence : ShortComplex (Rep ℤ G) where
  X₁ := B
  X₂ := Rep.ind N.subtype (Rep.res N.subtype B)
  X₃ := originalCoefficientRangeQuotient (originalSubgroupInducedUnit N B)
  f := originalSubgroupInducedUnit N B
  g := originalCoefficientRangeProjection (originalSubgroupInducedUnit N B)
  zero := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact originalCoefficientRangeProjection_map (originalSubgroupInducedUnit N B) x

/-- The original finite-index induction unit gives a literal short exact
coefficient sequence, with no sequence-exactness input. -/
theorem originalSubgroupInducedSequence_shortExact :
    (originalSubgroupInducedSequence N B).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (originalSubgroupInducedUnit_injective N B)
    epi_g := (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _) }
  apply ((originalSubgroupInducedSequence N B).exact_map_iff_of_faithful
    (forget₂ (Rep.{0} ℤ G) (ModuleCat.{0} ℤ))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (originalSubgroupInducedUnit N B).hom.toLinearMap.range =
    (originalSubgroupInducedUnit N B).hom.toLinearMap.range.mkQ.ker
  rw [Submodule.ker_mkQ]

/-- The actual quotient of the finite induced coefficient is finite. -/
theorem originalSubgroupInducedQuotient_finite [Finite B] :
    Finite (originalSubgroupInducedSequence N B).X₃ := by
  letI : Finite (originalSubgroupInducedSequence N B).X₂ := originalSubgroupInduced_finite N B
  exact Finite.of_surjective (originalSubgroupInducedSequence N B).g.hom
    ((Rep.epi_iff_surjective _).mp (originalSubgroupInducedSequence_shortExact N B).epi_g)

/-- The same prime annihilates the literal induced quotient. -/
theorem originalSubgroupInducedQuotient_nsmul_zero
    (p : ℕ) (hB : ∀ b : B, p • b = 0)
    (x : (originalSubgroupInducedSequence N B).X₃) : p • x = 0 := by
  obtain ⟨y, rfl⟩ := ((Rep.epi_iff_surjective _).mp
    (originalSubgroupInducedSequence_shortExact N B).epi_g) x
  rw [← map_nsmul]
  change (originalSubgroupInducedSequence N B).g.hom
    (p • (y : Rep.ind N.subtype (Rep.res N.subtype B))) = 0
  exact (congrArg (originalSubgroupInducedSequence N B).g.hom
    (originalSubgroupInduced_nsmul_zero N B p hB y)).trans (map_zero _)

/-- The original normal kernel still acts trivially on the literal quotient. -/
theorem originalNormalSubgroupInducedQuotient_action_trivial [N.Normal]
    (hN : ∀ g ∈ N, ∀ b : B, B.ρ g b = b)
    (n : G) (hn : n ∈ N) (x : (originalSubgroupInducedSequence N B).X₃) :
    (originalSubgroupInducedSequence N B).X₃.ρ n x = x := by
  obtain ⟨y, rfl⟩ := ((Rep.epi_iff_surjective _).mp
    (originalSubgroupInducedSequence_shortExact N B).epi_g) x
  rw [← Rep.hom_comm_apply]
  exact congrArg (originalSubgroupInducedSequence N B).g.hom
    (originalNormalSubgroupInduced_action_trivial N B hN n hn y)

/-- Pinned finite-index adjunctions carry the actual subgroup relation
sequence to a short exact sequence of original full-group coefficients. -/
theorem originalInducedRelationSequence_shortExact :
    ((originalRelationShortComplex (Rep.res N.subtype B)).map
      (Rep.indFunctor ℤ N.subtype)).ShortExact := by
  have hX := originalRelationShortComplex_shortExact (Rep.res N.subtype B)
  letI := hX.mono_f
  letI := hX.epi_g
  exact hX.map _

omit [Finite G] in
/-- The induced actual free relation term is projective by the pinned
induction/restriction adjunction, not by a supplied lifting certificate. -/
theorem originalInducedRelationFree_projective :
    Projective ((Rep.indFunctor ℤ N.subtype).obj (Rep.free ℤ N (Rep.res N.subtype B))) :=
  (Rep.indResAdjunction ℤ N.subtype).map_projective _ inferInstance

end
end Dubon2026
