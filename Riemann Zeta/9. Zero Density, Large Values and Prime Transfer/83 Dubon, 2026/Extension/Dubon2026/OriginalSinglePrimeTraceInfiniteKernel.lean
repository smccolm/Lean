import Dubon2026.OriginalIdeleInfiniteH2
import Dubon2026.OriginalSinglePrimeIdeleH2Lift

/-! # Infinite vanishing for the actual local-class trace at every finite prime

Every term of the native single-prime coinduced trace has identity
infinite coordinate. Hence the original H2 lift is in the zero-infinite
domain where DUB-17's constructed general-stage class total is normalized.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical BigOperators
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]

/-- Every translated original single-finite-prime idele has identity
coordinate at each original infinite place. -/
theorem originalIdeleSingleFinite_galois_infinite
    (w : HeightOneSpectrum (𝓞 L)) (v : InfinitePlace L) (σ : Gal(L/K))
    (u : (w.adicCompletion L)ˣ) :
    numberFieldIdeleInfiniteComponent L v
      (numberFieldIdeleGaloisMap K L σ (originalIdeleSingleFinite L w u)) = 1 := by
  apply Units.ext
  change numberFieldInfiniteAdeleGaloisMap K L σ (originalIdeleSingleFinite L w u).val.1 v = 1
  rw [numberFieldInfiniteAdeleGaloisMap_apply K L σ _ (σ⁻¹ • v) v (smul_inv_smul σ v)]
  have hc := congrArg Units.val (originalIdeleSingleFinite_infinite L w u (σ⁻¹ • v))
  change (originalIdeleSingleFinite L w u).val.1 (σ⁻¹ • v) = 1 at hc
  rw [hc, map_one]

variable (w : HeightOneSpectrum (𝓞 L))
  [Fintype (Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w)]

/-- The literal single-prime coinduced coefficient trace has zero
additive infinite coordinate at every original infinite place. -/
theorem originalSinglePrimeCoinducedTrace_infinite
    (v : InfinitePlace L)
    (x : Rep.coind (OriginalFiniteDecompositionGroup K L w).subtype (originalAdicUnitRep K L w)) :
    (originalFullIdeleInfiniteRepHom K L v).hom ((originalSinglePrimeCoinducedTrace K L w).hom x) = 0 := by
  change (originalFullIdeleInfiniteRepHom K L v).hom
    (∑ q : Gal(L/K) ⧸ OriginalFiniteDecompositionGroup K L w,
      coinducedCosetValues (originalFullIdeleRep K L) (OriginalFiniteDecompositionGroup K L w)
        (((Rep.coindFunctor ℤ (OriginalFiniteDecompositionGroup K L w).subtype).map
          (originalIdeleSingleFiniteRepHom K L w)).hom x) q) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro q _
  induction q using QuotientGroup.induction_on with
  | H g =>
    exact congrArg Additive.ofMul (originalIdeleSingleFinite_galois_infinite K L w v g (x.val g⁻¹).toMul)

/-- The actual lift of any finite local H2 class has zero localization
at every original infinite place, without a full-decomposition assumption. -/
theorem originalSinglePrimeIdeleH2Lift_infinite
    (v : InfinitePlace L) (x : groupCohomology (originalAdicUnitRep K L w) 2) :
    originalFullIdeleInfiniteH2 K L v (originalSinglePrimeIdeleH2Lift K L w x) = 0 := by
  have hz (y : groupCohomology
      (Rep.coind (OriginalFiniteDecompositionGroup K L w).subtype (originalAdicUnitRep K L w)) 2) :
      originalFullIdeleInfiniteH2 K L v
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalSinglePrimeCoinducedTrace K L w) y) = 0 := by
    induction y using groupCohomology.H2_induction_on with
    | h c =>
      simp only [originalFullIdeleInfiniteH2, groupCohomology.functor]
      erw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply]
      rw [← map_zero (groupCohomology.H2π (originalInfiniteUnitRep K L v)).hom]
      apply congrArg (groupCohomology.H2π _)
      apply Subtype.ext
      funext g
      exact originalSinglePrimeCoinducedTrace_infinite K L w v _
  exact hz ((groupCohomology.coindIso (originalAdicUnitRep K L w) 2).inv x)

end
end Dubon2026
