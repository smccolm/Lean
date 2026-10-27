import Dubon2026.SourceMonicQuotientRelation
import Dubon2026.SourceHolomorphicQuotientExtension
import Dubon2026.SourceMonicRelationRootBound

/-! DUB-17/18 -> rational Fourier spanning -> holomorphic recovery of integral
Fricke Laurent summands. The existing upper-half-plane identity theorem gives
isolated denominator zeros. Continuity bounds the finitely many coefficients,
and the existing monic-root bound controls the quotient. The already proved
removable-singularity extension then returns the exact holomorphic quotient.
This replaces the external analytic quotient and valuation development. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter
open scoped Topology Manifold

theorem mdiff_eventually_ne_zero_ofComplex {b : ℍ → ℂ}
    (hb : MDiff b) (hb0 : b ≠ 0) (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), b (ofComplex z) ≠ 0 := by
  apply (ModularRatios.eventually_nhdsNE_coe_iff (τ := τ) (p := fun w => b w ≠ 0)).mpr
  by_contra h
  have hfr : ∃ᶠ w in 𝓝[≠] τ, b w = 0 := by
    simpa only [Filter.not_eventually, not_not] using h
  exact hb0 (UpperHalfPlane.eq_zero_of_frequently hb hfr)

theorem quotient_locally_bounded_of_monic {a b : ℍ → ℂ} {c : ℕ → ℍ → ℂ} {d : ℕ}
    (hb : MDiff b) (hb0 : b ≠ 0) (hc : ∀ k < d, MDiff (c k))
    (hrel : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) (τ : ℍ) :
    ∃ M : ℝ, ∀ᶠ z in 𝓝[≠] (τ : ℂ), ‖a (ofComplex z) / b (ofComplex z)‖ ≤ M := by
  let C : ℍ → ℝ := fun w => ∑ k ∈ Finset.range d, ‖c k w‖
  let B : ℝ := C τ + 1
  have hC : Continuous C := continuous_finsetSum _ fun k hk =>
    (hc k (Finset.mem_range.mp hk)).continuous.norm
  have hCat : ContinuousAt (C ∘ ofComplex) (τ : ℂ) :=
    hC.continuousAt.comp_of_eq (mdifferentiableAt_ofComplex τ.im_pos).continuousAt
      (ofComplex_apply τ)
  have hCB : (C ∘ ofComplex) (τ : ℂ) < B := by
    simp only [Function.comp_apply, ofComplex_apply]
    exact lt_add_one _
  have hlocal : ∀ᶠ z in 𝓝[≠] (τ : ℂ), C (ofComplex z) < B :=
    (Filter.Tendsto.eventually_lt_const hCB hCat).filter_mono nhdsWithin_le_nhds
  have hB : 0 ≤ B := by
    have hnon : 0 ≤ C τ := Finset.sum_nonneg fun k _ => norm_nonneg (c k τ)
    dsimp only [B]
    linarith
  refine ⟨d * B + 1, ?_⟩
  filter_upwards [hlocal, mdiff_eventually_ne_zero_ofComplex hb hb0 τ] with z hz hzb
  have hcoeff : ∀ k ∈ Finset.range d, ‖c k (ofComplex z)‖ ≤ B := by
    intro k hk
    exact (Finset.single_le_sum (fun j _ => norm_nonneg (c j (ofComplex z))) hk).trans hz.le
  have hpoint : a (ofComplex z) ^ d + ∑ k ∈ Finset.range d,
      c k (ofComplex z) * b (ofComplex z) ^ (d - k) * a (ofComplex z) ^ k = 0 := by
    simpa only [Pi.add_apply, Pi.pow_apply, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply]
      using congrFun hrel (ofComplex z)
  exact norm_le_of_monic_relation hB hcoeff (monic_div_relation_of_cleared hzb hpoint)

theorem exists_mdifferentiable_quotient_of_monic {a b : ℍ → ℂ}
    {c : ℕ → ℍ → ℂ} {d : ℕ} (ha : MDiff a) (hb : MDiff b) (hb0 : b ≠ 0)
    (hc : ∀ k < d, MDiff (c k))
    (hrel : a ^ d + ∑ k ∈ Finset.range d, c k * b ^ (d - k) * a ^ k = 0) :
    ∃ F : ℍ → ℂ, MDiff F ∧ F * b = a := by
  obtain ⟨F, hF, hFa⟩ := HolomorphicQuotient.exists_mdifferentiable_mul_eq ha hb
    (fun z hz => mdiff_eventually_ne_zero_ofComplex hb hb0 ⟨z, hz⟩)
    (quotient_locally_bounded_of_monic hb hb0 hc hrel)
  exact ⟨F, hF, funext hFa⟩

end
end Dubon2026.SourceFunctionField