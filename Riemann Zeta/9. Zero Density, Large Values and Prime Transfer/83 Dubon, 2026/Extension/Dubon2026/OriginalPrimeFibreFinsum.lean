import Dubon2026.OriginalPrimeFibreTower
import Mathlib.Topology.Instances.AddCircle.Defs

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField BigOperators

/-- Reindex a finitely supported actual upper-prime invariant family by
its original lower-prime fibres. This is the summation step in the required
normalized total base-change identity. -/
theorem originalPrimeFibre_finsum
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (f : HeightOneSpectrum (𝓞 E) → AddCircle (1 : ℚ))
    (hf : (Function.support f).Finite) :
    (∑ᶠ v : HeightOneSpectrum (𝓞 K), ∑ᶠ u : OriginalPrimeFibre K E v, f u.val) =
      ∑ᶠ u, f u := by
  classical
  let s := hf.toFinset
  let g := originalFinitePrimeBelow K E
  have hs : Function.support f ⊆ s := fun _ hx => hf.mem_toFinset.mpr hx
  have hinner (v : HeightOneSpectrum (𝓞 K)) :
      (∑ᶠ u : OriginalPrimeFibre K E v, f u.val) = ∑ u ∈ s with g u = v, f u := by
    rw [finsum_subtype_eq_finsum_cond]
    simp only [finsum_eq_if]
    rw [finsum_eq_sum_of_support_subset (s := s)]
    · simp only [Finset.sum_filter]
      rfl
    · intro u hu
      change (if g u = v then f u else 0) ≠ 0 at hu
      by_cases h : g u = v
      · exact hs (by simpa only [h, if_true] using hu)
      · exact False.elim (hu (if_neg h))
  have hout : Function.support (fun v => ∑ᶠ u : OriginalPrimeFibre K E v, f u.val) ⊆ s.image g := by
    intro v hv
    by_contra h
    apply hv
    change (∑ᶠ u : OriginalPrimeFibre K E v, f u.val) = 0
    rw [hinner]
    apply Finset.sum_eq_zero
    intro u hu
    obtain ⟨hus, huv⟩ := Finset.mem_filter.mp hu
    exact False.elim (h (Finset.mem_image.mpr ⟨u, hus, huv⟩))
  rw [finsum_eq_sum_of_support_subset _ hout]
  simp_rw [hinner]
  rw [Finset.sum_fiberwise_of_maps_to (fun u hu => Finset.mem_image_of_mem g hu)]
  exact (finsum_eq_sum_of_support_subset f hs).symm

/-- The literal fibre formula determines the canonical total; finite support
justifies both the prime reindexing and scalar multiplication of the sum. -/
theorem originalPrimeFibre_finsum_eq_nsmul
    (K E : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
    (n : ℕ) (f : HeightOneSpectrum (𝓞 K) → AddCircle (1 : ℚ))
    (g : HeightOneSpectrum (𝓞 E) → AddCircle (1 : ℚ))
    (hf : (Function.support f).Finite) (hg : (Function.support g).Finite)
    (hfg : ∀ v, (∑ᶠ u : OriginalPrimeFibre K E v, g u.val) = n • f v) :
    (∑ᶠ u, g u) = n • ∑ᶠ v, f v := by
  calc
    _ = ∑ᶠ v, ∑ᶠ u : OriginalPrimeFibre K E v, g u.val :=
      (originalPrimeFibre_finsum K E g hg).symm
    _ = ∑ᶠ v, n • f v := finsum_congr hfg
    _ = n • ∑ᶠ v, f v := (finsum_nsmul hf n).symm

end
end Dubon2026
