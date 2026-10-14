import Dubon2026.LocalFieldFiniteCyclicFrobenius

/-! # Character images of the original unramified reciprocity formula

This transports the already proved normalization through a genuine finite
Galois character, as required for the cyclotomic principal-product calculation
on the DUB-17 arithmetic invariant-sum route.
-/
namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsSepClosed Ω]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]
  (E : FiniteGaloisIntermediateField K Ω)
  [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[E]]

attribute [local instance] IsCyclic.commGroup

/-- Any actual multiplicative character carries normalized original unramified reciprocity to the same power of its Frobenius image. -/
theorem localFieldFiniteCyclicReciprocity_frobenius_image
    {H : Type*} [Group H] (χ : Gal(E/K) →* H) (u : Kˣ) :
    letI : IsCyclic Gal(E/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K E).isCyclic.mpr inferInstance
    χ (localFieldFiniteCyclicReciprocity K Ω E (Additive.ofMul u)).toMul =
      χ (localFieldArithmeticFrobenius K E) ^ localFieldUnitOrder K (Additive.ofMul u) := by
  haveI : IsCyclic Gal(E/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K E).isCyclic.mpr inferInstance
  have h := congrArg (fun x => χ x.toMul)
    (localFieldFiniteCyclicReciprocity_frobenius K Ω E u)
  exact h.trans (map_zpow χ _ _)

end
end Dubon2026
