import Dubon2026.OriginalNormalizedCompletionNormMap
import Dubon2026.OriginalFinitePrimeOrbits
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Constructing the compatible closure for an actual completion norm comparison

The algebraic closure of the original upper completion supplies the
required scalar tower, Galois structure and discrete coefficient
topology. Thus DUB-17's inertia comparison requires no separately
chosen closure or local comparison premise.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory IsDedekindDomain
open scoped NumberField
attribute [-instance] UniformSpace.Completion.instSMul
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2 Submodule.module
attribute [local instance] originalCompletionCarryAlgebra originalCompletionCarryFinite
  originalCompletionCarryGalois originalCompletionCarryValuation originalCompletionCarryLocalField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (w : HeightOneSpectrum (𝓞 L)) [(OriginalFiniteDecompositionGroup K L w).Normal]
  (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
  (ψ : groupCohomology.cocycles₂ (originalIdeleClassRep K L))
  (hD : ∀ H : Subgroup Gal(L/K),
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalFundamentalSplittingModule (originalIdeleClassRep K L) ψ)) 1) ∧
    Limits.IsZero (groupCohomology (Rep.res H.subtype
      (originalFundamentalSplittingModule (originalIdeleClassRep K L) ψ)) 2))

/-- Global source normalization constructs the actual local norm square
after deriving all compatible-closure data from the original completion. -/
theorem originalCompletion_norm_comparison_with_constructed_closure
    (hψ : addOrderOf (groupCohomology.H2π (originalIdeleClassRep K L) ψ) = Module.finrank K L)
    (hl : OriginalCompletionClassRestrictions K L
      (groupCohomology.H2π (originalIdeleClassRep K L) ψ)) :
    OriginalCompletionNormComparison K L w p hG ψ hD := by
  let v := originalFinitePrimeBelow K L w
  letI : w.asIdeal.LiesOver v.asIdeal := originalFinitePrimeBelow_liesOver K L w
  let Ω := AlgebraicClosure (w.adicCompletion L)
  letI : CharZero (v.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
  letI : Algebra.IsAlgebraic (v.adicCompletion K) Ω :=
    Algebra.IsAlgebraic.trans (v.adicCompletion K) (w.adicCompletion L) Ω
  letI : IsGalois (v.adicCompletion K) Ω := ⟨⟩
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω) := ⟨rfl⟩
  exact originalCompletion_norm_comparison_of_normalization K L w p hG ψ hD v Ω hψ hl

end
end Dubon2026
