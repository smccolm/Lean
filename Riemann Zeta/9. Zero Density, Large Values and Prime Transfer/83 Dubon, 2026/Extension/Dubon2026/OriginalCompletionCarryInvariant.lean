import Dubon2026.OriginalCompletionCarryLocalization
import Dubon2026.OriginalAdicLocalFieldStructures
import Dubon2026.OriginalFiniteGaloisImage
import Dubon2026.LocalFieldOriginalCarryInvariant
import Dubon2026.ContinuousDiscreteH2Comparison

/-! # Normalized character pairing on the literal original completion

Actual global carry localization is composed with the same-cocycle
continuous comparison and actual inflation to the local closure. Its
finite cyclic image, scalar towers and cyclicity are constructed from the
original completion embedding. The resulting identity is the local term
needed for DUB-17's cyclotomic principal-product to invariant-sum argument.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [-instance] UniformSpace.Completion.instSMul

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

/-- Retain the literal original completion embedding. -/
local instance originalCompletionCarryAlgebra : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (originalAdicBaseChangeMap K L v w).toAlgebra

/-- Derive finiteness for the literal original completion extension. -/
local instance originalCompletionCarryFinite : FiniteDimensional (v.adicCompletion K) (w.adicCompletion L) :=
  (originalAdicBaseChange_finite_galois K L v w).1

/-- Derive the actual original completion Galois structure. -/
local instance originalCompletionCarryGalois : IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  (originalAdicBaseChange_finite_galois K L v w).2

/-- Retain the original completion's norm valuation. -/
local instance originalCompletionCarryValuation : ValuativeRel (v.adicCompletion K) :=
  ValuativeRel.ofValuation (NormedField.valuation (K := v.adicCompletion K))

/-- Derive the original local-field structure in its actual topology. -/
local instance originalCompletionCarryLocalField : IsNonarchimedeanLocalField (v.adicCompletion K) :=
  originalAdic_isNonarchimedeanLocalField K v

/-- Cyclicity of the original global extension gives cyclicity of its actual completion. -/
theorem originalCompletionGalois_isCyclic [IsCyclic Gal(L/K)] :
    IsCyclic Gal(w.adicCompletion L/v.adicCompletion K) := by
  apply isCyclic_of_injective (originalCompletionGaloisRestriction K L v w)
  exact Subtype.val_injective.comp (originalAdicDecompositionGaloisEquiv K L v w).symm.injective

variable (Ω : Type) [Field Ω]
  [Algebra (v.adicCompletion K) Ω] [Algebra (w.adicCompletion L) Ω]
  [IsScalarTower (v.adicCompletion K) (w.adicCompletion L) Ω]
  [IsGalois (v.adicCompletion K) Ω] [IsSepClosed Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) Ω)]

/-- The normalized local invariant after literal original completion localization and inflation. -/
def originalGlobalCompletionInvariant
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) : AddCircle (1 : ℚ) := by
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  exact localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
    (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L) Ω
      ((continuousDiscreteH2Equiv
        (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
        (discreteGaloisUnitAction_continuous (K := v.adicCompletion K)
          (Ω := w.adicCompletion L))).symm (originalGlobalCompletionH2 K L v w x)))

/-- The original completion invariant of a global carry class is its literal character pairing with actual normalized local reciprocity; the cyclic local image and all its towers are derived. -/
theorem originalGlobalCompletionInvariant_characterCarry [IsCyclic Gal(L/K)]
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    let F := originalFiniteGaloisImage (v.adicCompletion K) (w.adicCompletion L) Ω
    letI : IsCyclic Gal(w.adicCompletion L/v.adicCompletion K) :=
      originalCompletionGalois_isCyclic K L v w
    letI : IsCyclic Gal(F/v.adicCompletion K) :=
      originalFiniteGaloisImage_isCyclic (v.adicCompletion K) (w.adicCompletion L) Ω
    letI := originalFiniteGaloisImageAlgebra (v.adicCompletion K) (w.adicCompletion L) Ω
    letI := originalFiniteGaloisImage_baseTower (v.adicCompletion K) (w.adicCompletion L) Ω
    originalGlobalCompletionInvariant K L v w Ω
      (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (representationCarryCocycle (Rep.ofAlgebraAutOnUnits K L) χ
          (galoisUnitsBaseCoefficient u) (galoisUnitsBaseCoefficient_fixed u))) =
      rationalCyclicInvariant n
        (χ (originalCompletionGaloisRestriction K L v w
          (galoisBaseChangeRestriction (v.adicCompletion K) (v.adicCompletion K)
            (w.adicCompletion L) F
            (localFieldFiniteCyclicReciprocity (v.adicCompletion K) Ω F
              (Additive.ofMul (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u))).toMul))).toAdd := by
  let F := originalFiniteGaloisImage (v.adicCompletion K) (w.adicCompletion L) Ω
  letI : IsCyclic Gal(w.adicCompletion L/v.adicCompletion K) :=
    originalCompletionGalois_isCyclic K L v w
  letI : IsCyclic Gal(F/v.adicCompletion K) :=
    originalFiniteGaloisImage_isCyclic (v.adicCompletion K) (w.adicCompletion L) Ω
  letI := originalFiniteGaloisImageAlgebra (v.adicCompletion K) (w.adicCompletion L) Ω
  letI := originalFiniteGaloisImage_baseTower (v.adicCompletion K) (w.adicCompletion L) Ω
  letI := originalFiniteGaloisImage_ambientTower (v.adicCompletion K) (w.adicCompletion L) Ω
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L)) := ⟨rfl⟩
  let ψ := χ.comp (originalCompletionGaloisRestriction K L v w)
  let u' := Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom u
  let e := continuousDiscreteH2Equiv
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.adicCompletion L))
  have hc := continuousDiscreteH2Equiv_mk
    (Rep.ofAlgebraAutOnUnits (v.adicCompletion K) (w.adicCompletion L))
    (discreteGaloisUnitAction_continuous (K := v.adicCompletion K) (Ω := w.adicCompletion L))
    (galoisUnitCharacterCarryCocycle ψ u')
  have hl := (originalGlobalCompletionH2_characterCarry K L v w χ u).trans hc.symm
  have he := congrArg e.symm hl
  simp only [e, LinearEquiv.symm_apply_apply] at he
  exact (congrArg (fun z => localFieldContinuousH2InvariantEquiv (v.adicCompletion K) Ω
    (continuousGaloisUnitBaseChangeH2 (v.adicCompletion K) (v.adicCompletion K)
      (w.adicCompletion L) Ω z)) he).trans
    (localFieldOriginalCarryInvariant (v.adicCompletion K) (w.adicCompletion L) Ω F ψ u')

end
end Dubon2026
