import Dubon2026.ArithmeticSUnitFiniteStageInclusion
import Dubon2026.GaloisUnitCochainFiniteDescent

/-! # Actual finite-stage descent of continuous S-unit coboundary witnesses

The original continuous cochain descends, retaining every S-unit value, to a
finite Galois field containing any prescribed stage. This is the witness
descent needed to detect vanishing in the arithmetic S-unit H2 colimit.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [TopologicalSpace (originalArithmeticSUnitRepresentation K Ω a ha)]
  [DiscreteTopology (originalArithmeticSUnitRepresentation K Ω a ha)]

/-- Every original continuous S-unit cochain descends to a larger actual finite Galois stage with the same original S-unit coefficient values. -/
theorem arithmeticSUnitCochain_exists_finite_descent
    (E : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (b : C(Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
      originalArithmeticSUnitRepresentation K Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a), E ≤ F ∧
      ∃ f : Gal(F/K) → (↑(arithmeticSUnitFiniteStageSupport K Ω a ha F) :
        Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F,
        ∀ g : Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K),
          arithmeticSUnitFiniteStageUnitMap K Ω a ha F (f (AlgEquiv.restrictNormalHom F g)) =
            (b g).toMul := by
  let Γ := originalUnramifiedGaloisUnion (Ω := Ω) a
  letI : IsGalois K Γ := originalUnramifiedGaloisUnion_isGalois a
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K Γ) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K Γ) := ⟨rfl⟩
  let bΓ : C(Gal(Γ/K), Rep.ofAlgebraAutOnUnits K Γ) :=
    ⟨fun g => (originalArithmeticSUnitInclusion K Ω a ha).hom (b g),
      continuous_of_discreteTopology.comp b.continuous⟩
  obtain ⟨F, hEF, hvalues, hperiod⟩ := continuousGaloisUnitCochain_exists_finiteField E bΓ
  letI : NumberField F := NumberField.of_module_finite K F
  let bU : Gal(Γ/K) → Γˣ := fun g =>
    Units.map (OriginalArithmeticSUnitRing K Ω a ha).val.toMonoidHom (b g).toMul
  have hp : ∀ g u : Gal(Γ/K), AlgEquiv.restrictNormalHom F u = 1 → bU (g * u) = bU g := by
    intro g u hu
    exact congrArg (fun z : Rep.ofAlgebraAutOnUnits K Γ => z.toMul) (hperiod g u hu)
  obtain ⟨f, hf⟩ := galoisUnitCochain_exists_finite_descent F bU hvalues hp
  have hj : Function.Surjective (AlgEquiv.restrictNormalHom F : Gal(Γ/K) →* Gal(F/K)) :=
    AlgEquiv.restrictNormalHom_surjective Γ
  have hmem (σ : Gal(F/K)) : f σ ∈
      (↑(arithmeticSUnitFiniteStageSupport K Ω a ha F) :
        Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))).unit F := by
    obtain ⟨g, hg⟩ := hj σ
    obtain ⟨v, hv⟩ := originalArithmeticSUnit_supportedPreimage_at_finiteField
      K Ω a ha F (b g).toMul (hvalues g)
    have he : v.val = f σ := by
      apply Units.map_injective F.toIntermediateField.val.injective
      apply Units.ext
      have hfg := congrArg Units.val (hf g)
      rw [hg] at hfg
      exact hv.trans hfg.symm
    exact he ▸ v.property
  refine ⟨F, hEF, fun σ => ⟨f σ, hmem σ⟩, ?_⟩
  intro g
  apply Units.ext
  apply Subtype.ext
  exact (arithmeticSUnitFiniteStageUnitMap_coe K Ω a ha F _).trans (congrArg Units.val (hf g))

end
end Dubon2026
