import Dubon2026.SourceOriginalInverseJMonicRelation

/-! DUB-17/18 -> analytic cusp decay. Continuity evaluates the genuine
original monic relation at every point where the chosen quotient and
inverse j are regular. Thus the monic root bound controls the analytic
quantity built from the actual differential coefficient.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter Polynomial
open scoped Topology BigOperators

theorem original_inverse_j_relation_value (N : ℕ) [NeZero N]
    (y : modularFunctionFieldOver N ℂ) (n : ℕ) (c : ℕ → ℂ[X])
    (hrel : y ^ n + ∑ i ∈ Finset.range n, aeval (jOver N ℂ)⁻¹ (c i) * y ^ i = 0)
    (τ : ℍ) (hj : JMultiplicity.jf τ ≠ 0) (φ : ℂ → ℂ)
    (hcont : ContinuousAt φ (τ : ℂ))
    (hφ : (fun z : ℂ => realize N (y : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)] φ) :
    φ τ ^ n + ∑ i ∈ Finset.range n, (c i).eval (JMultiplicity.jf τ)⁻¹ * φ τ ^ i = 0 := by
  have hjcont := (JMultiplicity.analyticAt_comp JMultiplicity.mdifferentiable_jf τ).continuousAt
  have hinv : ContinuousAt (fun z : ℂ => (JMultiplicity.jf (ofComplex z))⁻¹) (τ : ℂ) :=
    hjcont.inv₀ (by simpa only [Function.comp_apply, ofComplex_apply] using hj)
  have hc : ∀ i, ContinuousAt (fun z : ℂ => (c i).eval (JMultiplicity.jf (ofComplex z))⁻¹) (τ : ℂ) :=
    fun i => (c i).continuous.continuousAt.comp hinv
  have hsum : ContinuousAt (fun z : ℂ => φ z ^ n + ∑ i ∈ Finset.range n,
      (c i).eval ((JMultiplicity.jf (ofComplex z))⁻¹) * φ z ^ i) (τ : ℂ) := by
    exact (hcont.pow n).add (tendsto_finsetSum _ fun i _ => (hc i).mul (hcont.pow i))
  have he := original_inverse_j_relation_germ N y n c hrel τ φ hφ
  have hv := tendsto_nhds_unique_of_eventuallyEq
    (hsum.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds he
  simpa only [ofComplex_apply] using hv

theorem original_differential_expression_germ (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) {k : ℤ}
    (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k) (hh : h ≠ 0)
    (hr : (x : LaurentSeries ℂ) * ModularRatios.qL h = ModularRatios.qL g)
    (M : ℕ) (τ : ℍ) :
    (fun z : ℂ => realize N
      ((x ^ (2 * M) * jOver N ℂ ^ (M + 1) *
        (jOver N ℂ - algebraMap ℂ (modularFunctionFieldOver N ℂ) 1728) ^ M :
          modularFunctionFieldOver N ℂ) : LaurentSeries ℂ) (ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => (g (ofComplex z) / h (ofComplex z)) ^ (2 * M) *
        JMultiplicity.jf (ofComplex z) ^ (M + 1) *
        (JMultiplicity.jf (ofComplex z) - 1728) ^ M := by
  apply Germ.coe_eq.mp
  change originalRealizeGerm N τ _ = _
  have hx : originalRealizeGerm N τ x =
      ((fun z : ℂ => g (ofComplex z) / h (ofComplex z)) : Germ (𝓝[≠] (τ : ℂ)) ℂ) :=
    Germ.coe_eq.mpr (realize_eventuallyEq_of_ratio g h x hh hr τ)
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, map_sub, hx,
    originalRealizeGerm_j, originalRealizeGerm_algebraMap]
  rfl

end
end Dubon2026.SourceFunctionField
