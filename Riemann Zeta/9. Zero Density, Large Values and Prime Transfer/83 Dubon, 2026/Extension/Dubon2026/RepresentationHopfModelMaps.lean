import Dubon2026.RepresentationUnderlyingGroupAction
import Dubon2026.FiniteFreeHopfPointModelEmbedding
import Dubon2026.FiniteFreeHopfPointModelSurjection

/-! # Actual Hopf models under injective and surjective original representation maps -/

namespace Dubon2026
noncomputable section

universe uC

variable {R F K O V W : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W] [Module O W]

/-- An injective map between the actual original linear representations inherits a Hopf model from its actual target. The original vectors, coefficient-module structures and action operators are retained by the proved underlying-group adapter. -/
def representationHopfModelOfInjective
    (ρ : Representation O (K ≃ₐ[F] K) V) (τ : Representation O (K ≃ₐ[F] K) W)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative W)
      (representationUnderlyingGroupAction τ))
    (f : V →ₗ[O] W) (hf : Function.Injective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative V)
      (representationUnderlyingGroupAction ρ) := by
  apply finiteFreeHopfPointModelOfInjective m f.toAddMonoidHom.toMultiplicative
  · intro v w h
    exact congrArg Multiplicative.ofAdd (hf (congrArg Multiplicative.toAdd h))
  · exact representationUnderlyingGroupAction_intertwining ρ τ f he

/-- The inherited model realizes exactly the original source linear representation's underlying additive group. -/
theorem representationHopfModel_of_injective_exists
    (ρ : Representation O (K ≃ₐ[F] K) V) (τ : Representation O (K ≃ₐ[F] K) W)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative W)
      (representationUnderlyingGroupAction τ))
    (f : V →ₗ[O] W) (hf : Function.Injective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative V)
      (representationUnderlyingGroupAction ρ)) := by
  exact ⟨representationHopfModelOfInjective ρ τ m f hf he⟩

/-- A surjective map between the actual original linear representations inherits a Hopf model from its actual source, through the genuine kernel quotient and original action comparison. -/
def representationHopfModelOfSurjective [Module.Flat R K]
    (ρ : Representation O (K ≃ₐ[F] K) V) (τ : Representation O (K ≃ₐ[F] K) W)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative V)
      (representationUnderlyingGroupAction ρ))
    (f : V →ₗ[O] W) (hf : Function.Surjective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative W)
      (representationUnderlyingGroupAction τ) := by
  apply finiteFreeHopfPointModelOfSurjective m f.toAddMonoidHom.toMultiplicative
  · intro w
    obtain ⟨v, hv⟩ := hf (Multiplicative.toAdd w)
    exact ⟨Multiplicative.ofAdd v, congrArg Multiplicative.ofAdd hv⟩
  · exact representationUnderlyingGroupAction_intertwining ρ τ f he

/-- The inherited model realizes exactly the original target linear representation's underlying additive group. -/
theorem representationHopfModel_of_surjective_exists [Module.Flat R K]
    (ρ : Representation O (K ≃ₐ[F] K) V) (τ : Representation O (K ≃ₐ[F] K) W)
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative V)
      (representationUnderlyingGroupAction ρ))
    (f : V →ₗ[O] W) (hf : Function.Surjective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K (Multiplicative W)
      (representationUnderlyingGroupAction τ)) := by
  exact ⟨representationHopfModelOfSurjective ρ τ m f hf he⟩

end
end Dubon2026
