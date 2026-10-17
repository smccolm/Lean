import Dubon2026.OriginalSPlaceClassComparison
import Dubon2026.OriginalIdelePowerLocalUnits

/-! # Literal local powers split into a supported power and outside units

Use the already proved original coordinate equivalence to choose roots
only at infinity and the selected finite primes. This proves the actual
subgroup comparison required by DUB-17's prescribed-support norm field,
without rebuilding the restricted-product constructor.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K : Type) [Field K] [NumberField K]
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (hS : ∀ (σ : Gal(K/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ S)

/-- The literal original local-power idele is a supported power times
an actual outside-unit idele, expressed in the additive coefficient. -/
theorem originalSupportedPowerLocalUnit_decomposition (n : ℕ)
    (a : originalSupportedIdeleRep K K S hS)
    (ha : a.toMul.val ∈ originalIdelePowerLocalUnitSubgroup K n S ∅) :
    ∃ (b : originalSupportedIdeleRep K K S hS) (u : supportedOutsideUnitRep K K S hS),
      a = n • b + (originalOutsideSupportedInclusion K K S hS).hom u := by
  obtain ⟨hInf, hFin, _⟩ := (originalIdelePowerLocalUnitSubgroup_mem_iff K n S ∅ _).mp ha
  let e := supportedIdeleLocalFactorLinearEquiv K S
  have hroots : ∀ v : SUnitLogPlace K S,
      ∃ y : supportedUnrestrictedUnitModule K S v, n • y = (e a).1 v := by
    intro v
    cases v with
    | inl v =>
      obtain ⟨y, hy⟩ := hInf v
      exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
    | inr v =>
      obtain ⟨y, hy⟩ := hFin v.val v.property
      exact ⟨Additive.ofMul y, congrArg Additive.ofMul hy⟩
  choose y hy using hroots
  let b : originalSupportedIdeleRep K K S hS := e.symm (y, 0)
  refine ⟨b, (e a).2, e.injective ?_⟩
  change e a = e (n • e.symm (y, 0) + e.symm (0, (e a).2))
  rw [e.map_add, map_nsmul e]
  rw [e.apply_symm_apply, e.apply_symm_apply]
  apply Prod.ext
  · change (e a).1 = n • y + 0
    rw [add_zero]
    exact (funext hy).symm
  · change (e a).2 = n • (0 : ∀ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      Additive (v.val.adicCompletionIntegers K)ˣ) + (e a).2
    rw [smul_zero, zero_add]

end
end Dubon2026
