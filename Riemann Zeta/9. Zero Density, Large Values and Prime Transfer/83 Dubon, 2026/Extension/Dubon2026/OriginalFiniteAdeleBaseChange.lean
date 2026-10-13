import Dubon2026.OriginalFinitePrimeOrbits
import Dubon2026.OriginalAdicBaseChangeNaturality
import Dubon2026.NumberFieldFiniteAdeleGaloisMap

/-! # Actual base change on the original finite adeles

The local maps act on the original restricted product. The existing
finite-prime base-change theorem proves the cofinite condition; the
original valuation comparison proves integrality. This supplies the
finite part of original idele descent for DUB-17's native norm quotient.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Original prime contraction preserves the cofinite filters used by the original finite adeles. -/
theorem originalFinitePrimeBelow_tendsto_cofinite :
    Filter.Tendsto (originalFinitePrimeBelow K L) Filter.cofinite Filter.cofinite := by
  intro S hS
  exact originalFinitePrimeBelow_preimage_finite K L Sᶜ hS

/-- The actual completion map indexed by an original upper prime and its original contraction. -/
def originalFiniteCompletionBaseChange (w : HeightOneSpectrum (𝓞 L)) :
    (originalFinitePrimeBelow K L w).adicCompletion K →+* w.adicCompletion L := by
  letI := originalFinitePrimeBelow_liesOver K L w
  exact originalAdicBaseChangeMap K L (originalFinitePrimeBelow K L w) w

/-- The original restricted-product subrings are preserved and reflected at each original prime. -/
theorem originalFiniteCompletionBaseChange_mem_integers (w : HeightOneSpectrum (𝓞 L))
    (x : (originalFinitePrimeBelow K L w).adicCompletion K) :
    originalFiniteCompletionBaseChange K L w x ∈ w.adicCompletionIntegers L ↔
      x ∈ (originalFinitePrimeBelow K L w).adicCompletionIntegers K := by
  letI := originalFinitePrimeBelow_liesOver K L w
  exact originalAdicBaseChangeMap_mem_integers K L (originalFinitePrimeBelow K L w) w x

/-- The actual original finite-adele base-change ring map. -/
def originalFiniteAdeleBaseChangeMap :
    FiniteAdeleRing (𝓞 K) K →+* FiniteAdeleRing (𝓞 L) L :=
  RestrictedProduct.mapAlongRingHom _ _ (originalFinitePrimeBelow K L)
    (originalFinitePrimeBelow_tendsto_cofinite K L) (originalFiniteCompletionBaseChange K L)
    (Filter.Eventually.of_forall fun w x hx =>
      (originalFiniteCompletionBaseChange_mem_integers K L w x).mpr hx)

/-- Original finite-adele base change uses the actual completion map at each original coordinate. -/
theorem originalFiniteAdeleBaseChangeMap_apply_at
    (a : FiniteAdeleRing (𝓞 K) K) (v : HeightOneSpectrum (𝓞 K))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (h : originalFinitePrimeBelow K L w = v) :
    originalFiniteAdeleBaseChangeMap K L a w = originalAdicBaseChangeMap K L v w (a v) := by
  subst v
  rfl

/-- Original finite-adele base change extends the actual global-field embedding. -/
theorem originalFiniteAdeleBaseChangeMap_algebraMap (x : K) :
    originalFiniteAdeleBaseChangeMap K L (algebraMap K (FiniteAdeleRing (𝓞 K) K) x) =
      algebraMap L (FiniteAdeleRing (𝓞 L) L) (algebraMap K L x) := by
  apply FiniteAdeleRing.ext
  intro w
  letI := originalFinitePrimeBelow_liesOver K L w
  exact originalAdicBaseChangeMap_algebraMap K L (originalFinitePrimeBelow K L w) w x

/-- The original finite-adele base-change map is injective. -/
theorem originalFiniteAdeleBaseChangeMap_injective :
    Function.Injective (originalFiniteAdeleBaseChangeMap K L) := by
  intro a b hab
  apply FiniteAdeleRing.ext
  intro v
  obtain ⟨w, rfl⟩ := originalFinitePrimeBelow_surjective K L v
  apply (originalFiniteCompletionBaseChange K L w).injective
  exact congrArg (fun t : FiniteAdeleRing (𝓞 L) L => t w) hab

/-- Original base finite adeles are fixed by every original Galois finite-adele map. -/
theorem originalFiniteAdeleBaseChangeMap_fixed (σ : Gal(L/K)) (a : FiniteAdeleRing (𝓞 K) K) :
    numberFieldFiniteAdeleGaloisMap K L σ (originalFiniteAdeleBaseChangeMap K L a) =
      originalFiniteAdeleBaseChangeMap K L a := by
  apply FiniteAdeleRing.ext
  intro w
  let u := (numberFieldGaloisPlaceEquiv K L σ).symm w
  have hσ : numberFieldGaloisPlaceEquiv K L σ u = w :=
    (numberFieldGaloisPlaceEquiv K L σ).apply_symm_apply w
  have hb : originalFinitePrimeBelow K L u = originalFinitePrimeBelow K L w :=
    (originalFinitePrimeBelow_galois K L σ u).symm.trans
      (congrArg (originalFinitePrimeBelow K L) hσ)
  letI := originalFinitePrimeBelow_liesOver K L w
  haveI : u.asIdeal.LiesOver (originalFinitePrimeBelow K L w).asIdeal := by
    rw [← hb]
    exact originalFinitePrimeBelow_liesOver K L u
  rw [numberFieldFiniteAdeleGaloisMap_apply K L σ _ u w hσ,
    originalFiniteAdeleBaseChangeMap_apply_at K L a (originalFinitePrimeBelow K L w) u hb,
    originalFiniteAdeleBaseChangeMap_apply_at K L a (originalFinitePrimeBelow K L w) w rfl]
  exact originalAdicBaseChangeMap_transport K L (originalFinitePrimeBelow K L w) u w σ hσ _

end
end Dubon2026
