import Dubon2026.SourceGammaOnePoleClearedCuspBounds

/-! DUB-17/18 -> original all-weight arithmetic association -> actual finite
Gamma1 characters -> Picard/H1 and modular periods -> original meromorphic
field realization. A finite prescribed analytic divisor and bounded cusp
limits suffice: clear its poles using the actual field multiplier, realize
the holomorphic product, and divide in the original integral-ratio field.
The precise ramification-weighted orders are retained at every analytic place. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane CongruenceSubgroup SourceCurve Filter
open scoped MatrixGroups Topology Manifold ModularForm

theorem exists_original_field_of_prescribed_meromorphic_orders
    (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Gamma1 N)
    (D : Divisor ℂ (functionFieldOver (Gamma1 N) ℂ)) (F : ℍ → ℂ)
    (hm : ∀ τ : ℍ, MeromorphicAt (F ∘ ofComplex) (τ : ℂ))
    (hinv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, F (γ • τ) = F τ)
    (hcusp : ∀ γ : SL(2, ℤ), IsBoundedAtImInfty (F ∘ (γ • ·)))
    (ho : ∀ τ : ℍ, meromorphicOrderAt (F ∘ ofComplex) (τ : ℂ) =
      (((analyticRamification hT τ : ℤ) * D (analyticPlace hT τ) : ℤ) : WithTop ℤ)) :
    ∃ x : functionFieldOver (Gamma1 N) ℂ, x ≠ 0 ∧
      (∀ τ : ℍ, (fun z : ℂ => realize (Gamma1 N) (x : LaurentSeries ℂ) (ofComplex z))
        =ᶠ[𝓝[≠] (τ : ℂ)] (F ∘ ofComplex)) ∧
      ∀ τ : ℍ, (analyticPlace hT τ).ord x = D (analyticPlace hT τ) := by
  have hΓ : Gamma N ≤ Gamma1 N := by
    intro γ hγ
    simp_all [Gamma1_mem, Gamma_mem]
  obtain ⟨a, A, G, ha0, _, hG, hAr, hGr, _, hGinv, hApb⟩ :=
    exists_pole_cleared_holomorphic_product N hΓ hT D F hm hinv ho
  have hGpb := pole_bounds_of_local_product hG hGr hcusp hApb
  obtain ⟨b, hBr, _, _⟩ := exists_original_field_of_holomorphic N G hG hGinv
    (meromorphic_cusps_of_holomorphic_pole_bounds N hΓ G hG hGinv hGpb)
  let x := b / a
  have hxa : x * a = b := div_mul_cancel₀ _ ha0
  have hxr (τ : ℍ) : (fun z : ℂ => realize (Gamma1 N) (x : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)] (F ∘ ofComplex) := by
    have hane : ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        realize (Gamma1 N) (a : LaurentSeries ℂ) (ofComplex z) ≠ 0 :=
      (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (meromorphicAt_realize hT a τ)).mp
        (meromorphicOrderAt_realize_ne_top hT a ha0 τ)
    filter_upwards [realize_mul_eventuallyEq hT x a τ, hAr τ, hGr τ, hane]
      with z hmul hA hprod hne
    apply mul_right_cancel₀ hne
    calc
      _ = realize (Gamma1 N) ((x * a : functionFieldOver (Gamma1 N) ℂ) : LaurentSeries ℂ)
          (ofComplex z) := hmul.symm
      _ = G (ofComplex z) := by rw [hxa]; exact hBr _
      _ = F (ofComplex z) * A (ofComplex z) := hprod
      _ = _ := congrArg (fun v : ℂ => F (ofComplex z) * v) hA
  have hxo (τ : ℍ) : analyticOrder (Gamma1 N) τ x =
      (((analyticRamification hT τ : ℤ) * D (analyticPlace hT τ) : ℤ) : WithTop ℤ) :=
    (meromorphicOrderAt_congr (hxr τ)).trans (ho τ)
  have hx0 : x ≠ 0 := by
    intro hz
    have h := hxo default
    rw [hz, analyticOrder_zero hT] at h
    exact WithTop.top_ne_coe h
  refine ⟨x, hx0, hxr, fun τ => ?_⟩
  have h := (analyticPlace_order hT τ x hx0).symm.trans (hxo τ)
  have hi : (analyticRamification hT τ : ℤ) * (analyticPlace hT τ).ord x =
      (analyticRamification hT τ : ℤ) * D (analyticPlace hT τ) := WithTop.coe_inj.mp h
  have he : (analyticRamification hT τ : ℤ) ≠ 0 := by
    exact_mod_cast (analyticRamification_pos hT τ).ne'
  exact mul_left_cancel₀ he hi

end
end Dubon2026.SourceFunctionField.GammaOne
