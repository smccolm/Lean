import Dubon2026.OriginalFiniteAdeleBaseChange
import Dubon2026.OriginalAdicFixedFieldDescent

/-! # Descent of actual fixed original finite adeles

Each fixed coordinate descends to the actual base completion. Actual
prime-orbit transitivity makes the descents consistent, and the finite
exceptional set proves restricted-product membership. This discharges
the finite-adele part of original idele descent needed for DUB-17's native
norm quotient and subsequent global duality and Selmer arguments.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- Every fixed original finite adele is the image of an actual original base finite adele. -/
theorem originalFiniteAdeleBaseChangeMap_surjective_fixed
    (a : FiniteAdeleRing (𝓞 L) L) (ha : ∀ σ : Gal(L/K), numberFieldFiniteAdeleGaloisMap K L σ a = a) :
    ∃ b : FiniteAdeleRing (𝓞 K) K, originalFiniteAdeleBaseChangeMap K L b = a := by
  have hfixed (w : HeightOneSpectrum (𝓞 L)) (σ : Gal(L/K))
      (hσ : numberFieldGaloisPlaceEquiv K L σ w = w) :
      numberFieldGaloisLocalTransport K L σ w w hσ (a w) = a w := by
    have h := congrArg (fun t : FiniteAdeleRing (𝓞 L) L => t w) (ha σ)
    change numberFieldFiniteAdeleGaloisMap K L σ a w = a w at h
    rw [numberFieldFiniteAdeleGaloisMap_apply K L σ a w w hσ] at h
    exact h
  choose W hW using originalFinitePrimeBelow_surjective K L
  letI (v : HeightOneSpectrum (𝓞 K)) : (W v).asIdeal.LiesOver v.asIdeal := by
    exact ⟨(congrArg HeightOneSpectrum.asIdeal (hW v)).symm⟩
  choose b hb using fun v : HeightOneSpectrum (𝓞 K) =>
    originalAdicBaseChangeMap_surjective_fixed K L v (W v) (a (W v)) (hfixed (W v))
  have hcoord (w : HeightOneSpectrum (𝓞 L)) :
      originalFiniteCompletionBaseChange K L w (b (originalFinitePrimeBelow K L w)) = a w := by
    let v := originalFinitePrimeBelow K L w
    letI := originalFinitePrimeBelow_liesOver K L w
    obtain ⟨σ, hσ⟩ := (originalFinitePrimeBelow_eq_iff_orbit K L (W v) w).mp (hW v)
    have hn := originalAdicBaseChangeMap_transport K L v (W v) w σ hσ (b v)
    rw [hb v] at hn
    have hg := congrArg (fun t : FiniteAdeleRing (𝓞 L) L => t w) (ha σ)
    change numberFieldFiniteAdeleGaloisMap K L σ a w = a w at hg
    rw [numberFieldFiniteAdeleGaloisMap_apply K L σ a (W v) w hσ] at hg
    exact hn.symm.trans hg
  have hbad : {w : HeightOneSpectrum (𝓞 L) | a w ∉ w.adicCompletionIntegers L}.Finite :=
    Filter.eventually_cofinite.mp a.property
  have hbint : ∀ᶠ v in Filter.cofinite, b v ∈ v.adicCompletionIntegers K := by
    filter_upwards [(hbad.image (originalFinitePrimeBelow K L)).eventually_cofinite_notMem] with v hv
    have hai : a (W v) ∈ (W v).adicCompletionIntegers L := by
      by_contra hn
      exact hv ⟨W v, hn, hW v⟩
    apply (originalAdicBaseChangeMap_mem_integers K L v (W v) (b v)).mp
    rwa [hb v]
  refine ⟨⟨b, hbint⟩, ?_⟩
  apply FiniteAdeleRing.ext
  exact hcoord

/-- The image of the original base finite adeles is exactly the actual Galois-fixed finite adeles. -/
theorem originalFiniteAdeleBaseChangeMap_range_iff_fixed (a : FiniteAdeleRing (𝓞 L) L) :
    a ∈ Set.range (originalFiniteAdeleBaseChangeMap K L) ↔
      ∀ σ : Gal(L/K), numberFieldFiniteAdeleGaloisMap K L σ a = a := by
  constructor
  · rintro ⟨b, rfl⟩ σ
    exact originalFiniteAdeleBaseChangeMap_fixed K L σ b
  · exact originalFiniteAdeleBaseChangeMap_surjective_fixed K L a

end
end Dubon2026
