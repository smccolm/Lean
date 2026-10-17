import Dubon2026.OriginalAdicInertiaNormRepresentatives
import Dubon2026.OriginalAdicIntegralRelativeTrace
import Dubon2026.OriginalInvariantTraceNormClass
import Dubon2026.OriginalDecompositionInertiaNormal

/-! # Inertia classes have integral representatives under the actual norm map

The proved subgroup image comparison, integral norm adjustment and literal
norm tower put every inertia abelianization class in the integral-unit
image. No Artin-map or Frobenius normalization is assumed. This is the
local input for DUB-17's prescribed-support norm-field construction.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : HeightOneSpectrum (𝓞 L))
  [Fintype (OriginalFiniteDecompositionGroup K L w)]
  (φ : groupCohomology.cocycles₂ (originalAdicUnitRep K L w))
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (OriginalFiniteDecompositionGroup K L w))
  (hC : ∀ H : Subgroup (OriginalFiniteDecompositionGroup K L w),
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalFundamentalSplittingModule (originalAdicUnitRep K L w) φ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalFundamentalSplittingModule (originalAdicUnitRep K L w) φ)) 2))

/-- Every abelianization class from a normal subgroup of actual inertia
is represented by an actual invariant integral completion unit. -/
theorem originalAdicInertiaSubgroup_image_mem_integral_norm_image
    (S : Subgroup (OriginalFiniteDecompositionGroup K L w)) [S.Normal]
    [Fintype S] [Fintype (OriginalFiniteDecompositionGroup K L w ⧸ S)]
    (hS : S.map (OriginalFiniteDecompositionGroup K L w).subtype ≤ w.asIdeal.inertia Gal(L/K)) :
    Set.range (Abelianization.map S.subtype).toAdditive ⊆
      (originalInvariantAbelianMap (originalAdicUnitRep K L w) φ p hG hC) ''
        {x | x.val.toMul ∈ (w.adicCompletionIntegers L).units} := by
  intro z hz
  rw [← originalInvariantAbelianMap_trace_range (originalAdicUnitRep K L w) φ p hG hC S] at hz
  obtain ⟨x, hx⟩ := hz
  obtain ⟨b, hb⟩ := originalAdicInertiaSubgroup_exists_integral_mod_norm w S hS x
  let y := x - originalSubgroupNormToInvariants (originalAdicUnitRep K L w) S b
  refine ⟨originalInvariantRelativeTrace (originalAdicUnitRep K L w) S y,
    originalAdicUnit_relativeTrace_integral K L w S y hb, ?_⟩
  exact (originalInvariantAbelianMap_trace_sub_norm
    (originalAdicUnitRep K L w) S φ p hG hC x b).trans hx

/-- Every class from the entire original inertia subgroup is in the
integral-unit image of the actual completion invariant norm map. -/
theorem originalAdicInertia_image_mem_integral_norm_image :
    let I := (w.asIdeal.inertia Gal(L/K)).comap
      (OriginalFiniteDecompositionGroup K L w).subtype
    Set.range (Abelianization.map I.subtype).toAdditive ⊆
      (originalInvariantAbelianMap (originalAdicUnitRep K L w) φ p hG hC) ''
        {x | x.val.toMul ∈ (w.adicCompletionIntegers L).units} := by
  let I := (w.asIdeal.inertia Gal(L/K)).comap
    (OriginalFiniteDecompositionGroup K L w).subtype
  letI : I.Normal := originalDecompositionInertia_normal K L w
  letI : Fintype I := Fintype.ofFinite _
  letI : Fintype (OriginalFiniteDecompositionGroup K L w ⧸ I) := Fintype.ofFinite _
  exact originalAdicInertiaSubgroup_image_mem_integral_norm_image K L w φ p hG hC I
    (Subgroup.map_comap_le _ _)

end
end Dubon2026
