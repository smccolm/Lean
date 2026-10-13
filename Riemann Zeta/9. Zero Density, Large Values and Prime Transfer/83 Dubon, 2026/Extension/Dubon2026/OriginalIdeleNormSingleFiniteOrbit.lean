import Dubon2026.OriginalLocalNormUnitProducts

/-! # The original idele norm for one selected finite prime per fiber

When an original idele has unit coordinate one at the other upper primes
over a base place, evaluating its actual Galois product leaves exactly the
local decomposition-group norm at the selected prime. This is the norm
identity needed by DUB-17's actual restricted-product preimage assembly.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- If other original upper coordinates over the actual base prime are one, the original idele norm component is the selected actual local norm. -/
theorem originalIdeleNorm_finiteComponent_of_onePrime (w : HeightOneSpectrum (𝓞 L))
    (a : (AdeleRing (𝓞 L) L)ˣ)
    (ha : ∀ u : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L u = originalFinitePrimeBelow K L w →
      u ≠ w → numberFieldIdeleFiniteComponent L u a = 1) :
    numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) (originalIdeleNorm K L a) =
      originalFiniteLocalNorm K L w (numberFieldIdeleFiniteComponent L w a) := by
  letI := originalFinitePrimeBelow_liesOver K L w
  let D := OriginalFiniteDecompositionGroup K L w
  let f (σ : Gal(L/K)) := numberFieldIdeleFiniteComponent L w (numberFieldIdeleGaloisMap K L σ a)
  have hout (σ : {σ : Gal(L/K) // σ ∉ D}) : f σ.val = 1 := by
    let u := (numberFieldGaloisPlaceEquiv K L σ.val).symm w
    have hu : numberFieldGaloisPlaceEquiv K L σ.val u = w :=
      (numberFieldGaloisPlaceEquiv K L σ.val).apply_symm_apply w
    have hb : originalFinitePrimeBelow K L u = originalFinitePrimeBelow K L w := by
      have h := originalFinitePrimeBelow_galois K L σ.val u
      rw [hu] at h
      exact h.symm
    have hn : u ≠ w := by
      intro h
      apply σ.property
      change numberFieldGaloisPlaceEquiv K L σ.val w = w
      simpa only [h] using hu
    have hv := congrArg Units.val (ha u hb hn)
    change a.val.2 u = 1 at hv
    apply Units.ext
    change numberFieldFiniteAdeleGaloisMap K L σ.val a.val.2 w = 1
    rw [numberFieldFiniteAdeleGaloisMap_apply K L σ.val a.val.2 u w hu, hv, map_one]
  have hp : (∏ σ : Gal(L/K), f σ) = ∏ τ : D, f τ.val := by
    have h := Fintype.prod_subtype_mul_prod_subtype (fun σ : Gal(L/K) => σ ∈ D) f
    have hother : (∏ σ : {σ : Gal(L/K) // σ ∉ D}, f σ.val) = 1 := by
      apply Finset.prod_eq_one
      intro σ _
      exact hout σ
    rw [hother, mul_one] at h
    exact h.symm
  apply Units.map_injective (originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w).injective
  rw [← originalIdeleBaseChangeMap_finiteComponent, originalIdeleBaseChangeMap_norm, map_prod,
    originalFiniteLocalNorm_baseChange]
  exact hp.trans (Finset.prod_congr rfl (fun τ _ => originalIdeleFiniteComponent_decomposition K L w τ a))

end
end Dubon2026
