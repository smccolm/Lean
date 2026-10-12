import Dubon2026.FiniteScalarCharacterH2Coordinates

/-! # The original scalar-extension H2 invariant from its prime-field invariant

The extended normalized unit spans the actual extension-field H2. Prime-field
coordinates prove both injectivity and surjectivity, using the already proved
continuous boundary reconstruction. This supplies the scalar target required
for actual finite extension-field local perfectness in DUB-17's trace pairing.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] characterDualSequenceContinuousSMul

variable {k G : Type} [Field k] [Group G]
  (q : ℕ) [Fact q.Prime] [CharP k q] [Algebra (ZMod q) k]
  [TopologicalSpace k] [DiscreteTopology k] [IsTopologicalRing k]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (χ : G →* ZMod q) (hχ : Continuous χ)
  (σ : ContinuousRepresentationH2 (coefficientCharacterRep χ)
    (coefficientCharacterAction_continuous χ hχ) ≃ₗ[ZMod q] ZMod q)

/-- Scalar multiples of the original extended normalized prime-field unit,
inside the actual extension-field H2 quotient. -/
def finiteScalarCharacterH2Span : k →ₗ[k]
    ContinuousRepresentationH2 (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (coefficientCharacterAction_continuous _ (finiteScalarCharacter_continuous q χ hχ)) :=
  LinearMap.toSpanSingleton k _ (finiteScalarCharacterH2Extend q χ hχ (σ.symm 1))

variable [Finite k]

/-- The actual extended normalized unit is a basis of the original scalar
H2. Original coordinate classes and continuous boundary reconstruction prove
surjectivity and injectivity, with no extension-field H2 dimension assumption. -/
theorem finiteScalarCharacterH2Span_bijective :
    Function.Bijective (finiteScalarCharacterH2Span q χ hχ σ (k := k)) := by
  let A₀ := finiteScalarCharacterPrimeRep q χ (k := k)
  letI : Module (ZMod q) k := A₀.hV2
  let b := Module.finBasis (ZMod q) k
  let hA₀ := coefficientCharacterAction_continuous
    ((algebraMap (ZMod q) k).toMonoidHom.comp χ) (finiteScalarCharacter_continuous q χ hχ)
  let e := finiteScalarCharacterPrimeH2Equiv q χ hχ (k := k)
  let c := fun i => continuousCoefficientH2Map A₀ (coefficientCharacterRep χ) (b.coord i)
    continuous_of_discreteTopology
    (scalarCoefficientCoordinate_equivariant A₀ χ b (finiteScalarCharacterPrime_action q χ) i)
    hA₀ (coefficientCharacterAction_continuous χ hχ)
  have hc (a : k) (i) : σ (c i (e (finiteScalarCharacterH2Span q χ hχ σ a))) = b.coord i a := by
    change σ (continuousCoefficientH2Map A₀ (coefficientCharacterRep χ) (b.coord i)
      continuous_of_discreteTopology
      (scalarCoefficientCoordinate_equivariant A₀ χ b (finiteScalarCharacterPrime_action q χ) i)
      hA₀ (coefficientCharacterAction_continuous χ hχ)
      (e (a • finiteScalarCharacterH2Extend q χ hχ (σ.symm 1)))) = b.coord i a
    rw [finiteScalarCharacterH2Extend_coordinate, map_smul, σ.apply_symm_apply, smul_eq_mul, mul_one]
  constructor
  · intro a d h
    apply b.equivFun.injective
    funext i
    exact (hc a i).symm.trans ((congrArg (fun x => σ (c i (e x))) h).trans (hc d i))
  · intro x
    let v := fun i => σ (c i (e x))
    let a := b.equivFun.symm v
    refine ⟨a, ?_⟩
    apply e.injective
    apply sub_eq_zero.mp
    apply continuousScalarH2_eq_zero_of_coordinates A₀ χ b (finiteScalarCharacterPrime_action q χ) hA₀ hχ
    intro i
    change c i (e (finiteScalarCharacterH2Span q χ hχ σ a) - e x) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    apply σ.injective
    exact (hc a i).trans (congrArg (fun f => f i) (b.equivFun.apply_symm_apply v))

/-- The original scalar H2 invariant is the inverse of the actual extended
normalized unit map. In particular it is linear over the original coefficient field. -/
def finiteScalarCharacterH2ScalarEquiv :
    ContinuousRepresentationH2 (coefficientCharacterRep ((algebraMap (ZMod q) k).toMonoidHom.comp χ))
      (coefficientCharacterAction_continuous _ (finiteScalarCharacter_continuous q χ hχ)) ≃ₗ[k] k :=
  (LinearEquiv.ofBijective (finiteScalarCharacterH2Span q χ hχ σ)
    (finiteScalarCharacterH2Span_bijective q χ hχ σ)).symm

end
end Dubon2026
