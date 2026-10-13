import Dubon2026.OriginalIdeleNorm
import Dubon2026.OriginalAdicNormGaloisProduct

/-! # The actual finite components of the original descended idele norm

Original idele inclusion retains each actual completed base embedding.
Evaluating the proved original norm product therefore gives the product
of the actual transported local units. Grouping these factors by the
actual decomposition group will consume the actual local field-norm
formula for DUB-17's local norm containment and norm-index upper bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- Actual original idele inclusion evaluates to the actual completed base-field map at each finite place. -/
theorem originalIdeleBaseChangeMap_finiteComponent (a : (AdeleRing (𝓞 K) K)ˣ) :
    numberFieldIdeleFiniteComponent L w (originalIdeleBaseChangeMap K L a) =
      Units.map (originalAdicBaseChangeMap K L v w).toMonoidHom (numberFieldIdeleFiniteComponent K v a) := by
  apply Units.ext
  have hw : originalFinitePrimeBelow K L w = v :=
    HeightOneSpectrum.ext (Ideal.over_def w.asIdeal v.asIdeal).symm
  exact originalFiniteAdeleBaseChangeMap_apply_at K L a.val.2 v w hw

variable [FiniteDimensional K L] [IsGalois K L]

/-- Each finite component of the actual original norm has the actual transported Galois-product formula. -/
theorem originalIdeleNorm_finiteComponent_product (a : (AdeleRing (𝓞 L) L)ˣ) :
    Units.map (originalAdicBaseChangeMap K L v w).toMonoidHom
        (numberFieldIdeleFiniteComponent K v (originalIdeleNorm K L a)) =
      ∏ σ : Gal(L/K), Units.map
        (numberFieldGaloisLocalTransport K L σ ((numberFieldGaloisPlaceEquiv K L σ).symm w) w
          ((numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w)).toMonoidHom
        (numberFieldIdeleFiniteComponent L ((numberFieldGaloisPlaceEquiv K L σ).symm w) a) := by
  rw [← originalIdeleBaseChangeMap_finiteComponent, originalIdeleBaseChangeMap_norm, map_prod]
  apply Finset.prod_congr rfl
  intro σ _
  apply Units.ext
  exact numberFieldFiniteAdeleGaloisMap_apply K L σ a.val.2
    ((numberFieldGaloisPlaceEquiv K L σ).symm w) w
      ((numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w)

end
end Dubon2026
