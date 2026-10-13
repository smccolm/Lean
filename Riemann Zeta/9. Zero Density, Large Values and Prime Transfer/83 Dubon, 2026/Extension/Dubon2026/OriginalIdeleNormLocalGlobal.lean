import Dubon2026.OriginalIdeleNormSingleFiniteOrbit
import Dubon2026.OriginalIdeleNormSingleInfiniteOrbit
import Dubon2026.OriginalIdeleLocalUnitAssembly

/-! # The actual original idele norm image from actual local norm images

One upper prime is chosen above each original base place. Actual local
norm preimages are placed at those coordinates and all other coordinates
are one. Their integrality eventually follows from the proved original
norm valuation. The original restricted-product constructor and the actual
single-orbit norm identities give a full original idele preimage.
This discharges the local-to-global idele norm-image comparison needed
for DUB-17's power/local-unit containment and norm-index upper bound.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Actual local norm preimages at every original place assemble to an original full idele norm preimage. -/
theorem originalIdeleNorm_exists_of_local (a : (AdeleRing (𝓞 K) K)ˣ)
    (hFin : ∀ w : HeightOneSpectrum (𝓞 L),
      numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) a ∈ (originalFiniteLocalNorm K L w).range)
    (hInf : ∀ w : InfinitePlace L,
      numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) a ∈ (originalInfiniteLocalNorm K L w).range) :
    ∃ b : (AdeleRing (𝓞 L) L)ˣ, originalIdeleNorm K L b = a := by
  choose yFin hyFin using hFin
  choose yInf hyInf using hInf
  choose W hW using originalFinitePrimeBelow_surjective K L
  choose U hU using (InfinitePlace.comap_surjective (k := K) (K := L))
  let zFin (w : HeightOneSpectrum (𝓞 L)) := if w = W (originalFinitePrimeBelow K L w) then yFin w else 1
  let zInf (w : InfinitePlace L) := if w = U (w.comap (algebraMap K L)) then yInf w else 1
  have he : ∀ᶠ w in Filter.cofinite, zFin w ∈ (w.adicCompletionIntegers L).units := by
    have ha := (originalFinitePrimeBelow_tendsto_cofinite K L).eventually
      (originalIdele_finiteComponent_eventually_integerUnit K a)
    filter_upwards [ha] with w hw
    by_cases hs : w = W (originalFinitePrimeBelow K L w)
    · simp only [zFin, if_pos hs]
      apply originalFiniteLocalNorm_preimage_integerUnit K L w
      rw [hyFin]
      exact hw
    · simp only [zFin, if_neg hs, Subgroup.one_mem]
  let b := originalIdeleFromLocalUnits L zInf zFin he
  have hbFin (w : HeightOneSpectrum (𝓞 L)) : numberFieldIdeleFiniteComponent L w b = zFin w := rfl
  have hbInf (w : InfinitePlace L) : numberFieldIdeleInfiniteComponent L w b = zInf w := rfl
  refine ⟨b, originalIdele_eq_of_components K _ _ ?_ ?_⟩
  · intro v
    let w := W v
    have hw : originalFinitePrimeBelow K L w = v := hW v
    have hs : w = W (originalFinitePrimeBelow K L w) := by rw [hw]
    have hone (u : HeightOneSpectrum (𝓞 L)) (hu : originalFinitePrimeBelow K L u = originalFinitePrimeBelow K L w)
        (hne : u ≠ w) : numberFieldIdeleFiniteComponent L u b = 1 := by
      rw [hbFin]
      have hnu : u ≠ W (originalFinitePrimeBelow K L u) := by rw [hu, hw]; exact hne
      simp only [zFin, if_neg hnu]
    have hn := originalIdeleNorm_finiteComponent_of_onePrime K L w b hone
    rw [hbFin, show zFin w = yFin w from if_pos hs, hyFin, hw] at hn
    exact hn
  · intro v
    let w := U v
    have hw : w.comap (algebraMap K L) = v := hU v
    have hs : w = U (w.comap (algebraMap K L)) := by rw [hw]
    have hone (u : InfinitePlace L) (hu : u.comap (algebraMap K L) = w.comap (algebraMap K L))
        (hne : u ≠ w) : numberFieldIdeleInfiniteComponent L u b = 1 := by
      rw [hbInf]
      have hnu : u ≠ U (u.comap (algebraMap K L)) := by rw [hu, hw]; exact hne
      simp only [zInf, if_neg hnu]
    have hn := originalIdeleNorm_infiniteComponent_of_onePlace K L w b hone
    rw [hbInf, show zInf w = yInf w from if_pos hs, hyInf, hw] at hn
    exact hn

variable [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

attribute [-instance] UniformSpace.Completion.instSMul in
/-- An actual base idele is an actual original norm exactly when all its original local components are actual corresponding field norms. -/
theorem originalIdeleNorm_range_iff_local (a : (AdeleRing (𝓞 K) K)ˣ) :
    a ∈ (originalIdeleNorm K L).range ↔
      (∀ w : HeightOneSpectrum (𝓞 L), numberFieldIdeleFiniteComponent K (originalFinitePrimeBelow K L w) a ∈
        (originalFiniteLocalNorm K L w).range) ∧
      (∀ w : InfinitePlace L, numberFieldIdeleInfiniteComponent K (w.comap (algebraMap K L)) a ∈
        (originalInfiniteLocalNorm K L w).range) := by
  constructor
  · rintro ⟨b, rfl⟩
    constructor
    · intro w
      exact ⟨originalIdeleFiniteOrbitNormPreimage K L w b, (originalIdeleNorm_finiteLocal K L w b).symm⟩
    · intro w
      exact ⟨originalIdeleInfiniteOrbitNormPreimage K L w b, (originalIdeleNorm_infiniteLocal K L w b).symm⟩
  · rintro ⟨hFin, hInf⟩
    exact originalIdeleNorm_exists_of_local K L a hFin hInf

end
end Dubon2026
