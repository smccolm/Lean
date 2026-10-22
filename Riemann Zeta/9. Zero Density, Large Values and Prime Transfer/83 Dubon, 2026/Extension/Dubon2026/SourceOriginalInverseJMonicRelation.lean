import Dubon2026.SourceOriginalRegularInverseJIntegral
import Dubon2026.SourceOriginalInverseJGermPolynomial

/-! DUB-17/18 -> cusp decay -> analytic control from inverse-j integrality.
Expose a finite monic relation whose coefficients are actual scalar
polynomials in inverse j, then transfer that exact relation through the
proved original realization homomorphism.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter Polynomial
open scoped Topology BigOperators

theorem exists_original_inverse_j_monic_relation (N : ℕ) [NeZero N]
    (y : modularFunctionFieldOver N ℂ)
    (hy : IsIntegral (Algebra.adjoin ℂ ({(jOver N ℂ)⁻¹} : Set (modularFunctionFieldOver N ℂ))) y) :
    ∃ (n : ℕ) (c : ℕ → ℂ[X]), 0 < n ∧
      y ^ n + ∑ i ∈ Finset.range n, aeval (jOver N ℂ)⁻¹ (c i) * y ^ i = 0 := by
  classical
  obtain ⟨p, hp, hpy⟩ := hy
  have hn : 0 < p.natDegree := by
    by_contra h
    have hz : p.natDegree = 0 := by omega
    have hp1 : p = 1 := hp.natDegree_eq_zero.mp hz
    simp only [hp1, eval₂_one, one_ne_zero] at hpy
  have hc : ∀ i, ∃ c : ℂ[X], aeval (jOver N ℂ)⁻¹ c =
      algebraMap (Algebra.adjoin ℂ ({(jOver N ℂ)⁻¹} : Set (modularFunctionFieldOver N ℂ)))
        (modularFunctionFieldOver N ℂ) (p.coeff i) := by
    intro i
    exact Algebra.adjoin_mem_exists_aeval ℂ _ (p.coeff i).2
  choose c hc using hc
  refine ⟨p.natDegree, c, hn, ?_⟩
  rw [hp.as_sum] at hpy
  simpa only [eval₂_add, eval₂_pow, eval₂_X, eval₂_finsetSum, eval₂_mul, eval₂_C, hc] using hpy

theorem original_inverse_j_relation_germ (N : ℕ) [NeZero N]
    (y : modularFunctionFieldOver N ℂ) (n : ℕ) (c : ℕ → ℂ[X])
    (hrel : y ^ n + ∑ i ∈ Finset.range n, aeval (jOver N ℂ)⁻¹ (c i) * y ^ i = 0)
    (τ : ℍ) (φ : ℂ → ℂ)
    (hφ : (fun z : ℂ => realize N (y : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] φ) :
    (fun z : ℂ => φ z ^ n + ∑ i ∈ Finset.range n,
      (c i).eval ((JMultiplicity.jf (ofComplex z))⁻¹) * φ z ^ i) =ᶠ[𝓝[≠] (τ : ℂ)] 0 := by
  have hy : originalRealizeGerm N τ y = (φ : Germ (𝓝[≠] (τ : ℂ)) ℂ) := Germ.coe_eq.mpr hφ
  have h := congrArg (originalRealizeGerm N τ) hrel
  simp only [map_add, map_sum, map_mul, map_pow, map_zero, originalRealizeGerm_aeval_inverse_j, hy] at h
  let C : ℕ → ℂ → ℂ := fun i z => (c i).eval ((JMultiplicity.jf (ofComplex z))⁻¹)
  have hg : (Germ.coeRingHom (𝓝[≠] (τ : ℂ)))
      (φ ^ n + ∑ i ∈ Finset.range n, C i * φ ^ i) = 0 := by
    simpa only [map_add, map_sum, map_mul, map_pow, Germ.coe_coeRingHom] using h
  have hh := Germ.coe_eq.mp hg
  filter_upwards [hh] with z hz
  simpa only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply, C] using hz

end
end Dubon2026.SourceFunctionField
