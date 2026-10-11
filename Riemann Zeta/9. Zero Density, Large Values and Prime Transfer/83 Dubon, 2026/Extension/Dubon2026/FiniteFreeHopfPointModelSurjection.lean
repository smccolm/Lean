import Dubon2026.FiniteFreeHopfPointModelEquiv
import Dubon2026.FiniteFreeHopfPointModelQuotient

/-! # Actual Hopf models inherited through original equivariant surjections -/

namespace Dubon2026
noncomputable section

universe uC

variable {R F K V W : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [Module.Flat R K] [CommGroup V] [CommGroup W]
  {ρ : (K ≃ₐ[F] K) →* MulAut V} {τ : (K ≃ₐ[F] K) →* MulAut W}

/-- An original equivariant surjection from a modeled group gives a model of its actual target. The actual kernel is stable; the invariant-coordinate quotient model is transported through the original first-isomorphism equivalence. -/
def finiteFreeHopfPointModelOfSurjective
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ) (f : V →* W)
    (hf : Function.Surjective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K W τ := by
  have hH : ∀ (g : K ≃ₐ[F] K) (v : V), v ∈ f.ker → ρ g v ∈ f.ker := by
    intro g v hv
    change f (ρ g v) = 1
    rw [he, show f v = 1 from hv, map_one]
  let e : (V ⧸ f.ker) ≃* W := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hi : ∀ (g : K ≃ₐ[F] K) (z : V ⧸ f.ker),
      e (galoisModuleQuotientAction ρ f.ker hH g z) = τ g (e z) := by
    intro g z
    induction z using Quotient.inductionOn with
    | h v =>
      change f (ρ g v) = τ g (f v)
      exact he g v
  exact finiteFreeHopfPointModelEquiv
    (finiteFreeHopfPointModelQuotient m f.ker hH) e hi

/-- The actual target of the original equivariant surjection has a genuine finite free Hopf model, derived from the source model and the original quotient construction. -/
theorem finiteFreeHopfPointModel_of_surjective_exists
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ) (f : V →* W)
    (hf : Function.Surjective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K W τ) := by
  exact ⟨finiteFreeHopfPointModelOfSurjective m f hf he⟩

end
end Dubon2026
