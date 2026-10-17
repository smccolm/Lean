import Dubon2026.OriginalNormalizedCompletionCocycle
import Dubon2026.OriginalInvariantAbelianGroupChange

/-! # Source-normalized completion compatibility of the actual norm map

Normalization constructs the compatible local cocycle and its full
order; the existing local subgroup results give its fundamental
acyclicity. The proved homology comparison then gives the actual norm
map square. This is the completion comparison needed before DUB-17's
outside-unit inertia image and prescribed ramification support.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
  [(OriginalFiniteDecompositionGroup K L w).Normal]
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
  (ψ : groupCohomology.cocycles₂ (originalIdeleClassRep K L))
  (hD : ∀ T : Subgroup Gal(L/K),
    Limits.IsZero (groupCohomology (Rep.res T.subtype
      (originalFundamentalSplittingModule (originalIdeleClassRep K L) ψ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res T.subtype
      (originalFundamentalSplittingModule (originalIdeleClassRep K L) ψ)) 2))

/-- The literal norm-map square for one actual completion and global
cocycle, including the locally constructed full-order acyclic coefficient.
This proposition alone asserts no existence. -/
def OriginalCompletionNormComparison : Prop :=
  letI : Fintype (OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  ∃ φ : groupCohomology.cocycles₂ (originalAdicUnitRep K L w),
    ∃ hC : ∀ T : Subgroup (OriginalFiniteDecompositionGroup K L w),
      Limits.IsZero (groupCohomology (Rep.res T.subtype
        (originalFundamentalSplittingModule (originalAdicUnitRep K L w) φ)) 1) ∧
      Limits.IsZero (groupCohomology (Rep.res T.subtype
        (originalFundamentalSplittingModule (originalAdicUnitRep K L w) φ)) 2),
    addOrderOf (groupCohomology.H2π (originalAdicUnitRep K L w) φ) =
      Nat.card (OriginalFiniteDecompositionGroup K L w) ∧
    ∀ x : (originalAdicUnitRep K L w).ρ.invariants,
      originalInvariantAbelianMap (originalIdeleClassRep K L) ψ p hG hD
        (originalInvariantRelativeTrace (originalIdeleClassRep K L)
          (OriginalFiniteDecompositionGroup K L w)
          ((Rep.invariantsFunctor ℤ (OriginalFiniteDecompositionGroup K L w)).map
            (originalCompletionClassRepHom K L w) x)) =
      (Abelianization.map (OriginalFiniteDecompositionGroup K L w).subtype).toAdditive
        (originalInvariantAbelianMap (originalAdicUnitRep K L w) φ p
          (hG.to_subgroup (OriginalFiniteDecompositionGroup K L w)) hC x)

/-- The source-normalized global cocycle constructs the full local
fundamental data and the actual invariant/abelianization norm square. -/
theorem originalCompletion_norm_comparison_of_normalization
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver v.asIdeal]
    (Ω : Type) [Field Ω]
    [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
    [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
    [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
    (hψ : addOrderOf (groupCohomology.H2π (originalIdeleClassRep K L) ψ) = Module.finrank K L)
    (hl : OriginalCompletionClassRestrictions K L
      (groupCohomology.H2π (originalIdeleClassRep K L) ψ)) :
    OriginalCompletionNormComparison K L w p hG ψ hD := by
  letI : Fintype (OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  letI : Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w) := Fintype.ofFinite _
  obtain ⟨φ, hφ, hc⟩ := originalCompletion_exists_compatible_full_order_cocycle K L v w Ω _ hψ hl
  have hC := originalAdicUnit_fundamental_subgroup_first_second_zero K L v w φ hφ
  refine ⟨φ, hC, hφ, fun x => ?_⟩
  exact originalInvariantAbelianMap_groupChange (OriginalFiniteDecompositionGroup K L w)
    (originalAdicUnitRep K L w) (originalIdeleClassRep K L)
    (originalCompletionClassRepHom K L w) φ ψ p hG hC hD hc x

end
end Dubon2026
