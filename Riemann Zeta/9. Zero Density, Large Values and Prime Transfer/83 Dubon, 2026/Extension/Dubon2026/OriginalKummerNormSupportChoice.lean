import Dubon2026.OriginalUnramifiedIdeleSupport
import Dubon2026.ArithmeticExceptionalSUnitSupport

/-! # Constructing the support needed by the actual Kummer norm field

Existing finite ramification and class-surjective support results are
combined with the actual primes containing the exponent. This removes
all auxiliary support-existence assumptions from DUB-17's large-support
Kummer step without invoking a new class-group principalization theorem.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField
variable (K : Type) [Field K] [NumberField K]

/-- Every prescribed finite support has a finite stable enlargement
surjecting onto actual classes, containing all exponent primes and all
absolutely ramified primes. -/
theorem original_exists_kummer_norm_support
    (p : ℕ) (hp : p ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), S ⊆ T ∧
      (∀ (σ : Gal(K/K)) v, v ∈ T ↔ numberFieldGaloisPlaceEquiv K K σ v ∈ T) ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap K T) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → Algebra.IsUnramifiedAt ℤ v.asIdeal) ∧
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → (p : 𝓞 K) ∉ v.asIdeal) := by
  classical
  have hpK : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp
  let P := originalExceptionalIntegerSupport K (p : 𝓞 K) hpK
  obtain ⟨T, hT, hStable, hClasses, hBase⟩ :=
    original_exists_unramified_galoisStable_idele_support K K (S ∪ P)
  refine ⟨T, Finset.subset_union_left.trans hT, hStable, hClasses, hBase, ?_⟩
  intro v hv hpv
  exact hv (hT (Finset.mem_union_right _
    ((mem_originalExceptionalIntegerSupport K (p : 𝓞 K) hpK v).mpr hpv)))

end
end Dubon2026
