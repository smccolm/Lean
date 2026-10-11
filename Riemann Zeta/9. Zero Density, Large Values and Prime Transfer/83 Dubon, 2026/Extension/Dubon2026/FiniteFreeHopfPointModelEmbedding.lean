import Dubon2026.FiniteFreeHopfPointModelEquiv
import Dubon2026.FiniteFreeHopfPointModelSubgroup

/-! # Actual Hopf models inherited through original equivariant embeddings -/

namespace Dubon2026
noncomputable section

universe uC

variable {R F K V W : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field F] [PerfectField F] [Field K] [Algebra R F] [IsFractionRing R F]
  [Algebra R K] [Algebra F K] [IsScalarTower R F K] [Normal F K] [IsAlgClosed K]
  [CommGroup V] [CommGroup W]
  {ρ : (K ≃ₐ[F] K) →* MulAut V} {τ : (K ≃ₐ[F] K) →* MulAut W}

/-- An original equivariant injection into a modeled group gives a model of its actual source. The stable range model is constructed from the original integral coordinates and transported through the genuine injective range equivalence. -/
def finiteFreeHopfPointModelOfInjective
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K W τ) (f : V →* W)
    (hf : Function.Injective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ := by
  have hH : ∀ (g : K ≃ₐ[F] K) (w : W), w ∈ f.range → τ g w ∈ f.range := by
    intro g w hw
    obtain ⟨v, rfl⟩ := hw
    exact ⟨ρ g v, he g v⟩
  let e : V ≃* f.range := MonoidHom.ofInjective hf
  have hi : ∀ (g : K ≃ₐ[F] K) (w : f.range),
      e.symm (galoisModuleSubgroupAction τ f.range hH g w) = ρ g (e.symm w) := by
    intro g w
    apply hf
    calc
      f (e.symm (galoisModuleSubgroupAction τ f.range hH g w)) =
          (galoisModuleSubgroupAction τ f.range hH g w).val :=
        MonoidHom.apply_ofInjective_symm hf _
      _ = τ g w.val := galoisModuleSubgroupAction_apply τ f.range hH g w
      _ = τ g (f (e.symm w)) :=
        congrArg (τ g) (MonoidHom.apply_ofInjective_symm hf w).symm
      _ = f (ρ g (e.symm w)) := (he g (e.symm w)).symm
  exact finiteFreeHopfPointModelEquiv
    (finiteFreeHopfPointModelSubgroup m f.range hH) e.symm hi

/-- The actual source of the original equivariant embedding has a genuine finite free Hopf model; no model of that source is assumed. -/
theorem finiteFreeHopfPointModel_of_injective_exists
    (m : FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K W τ) (f : V →* W)
    (hf : Function.Injective f)
    (he : ∀ (g : K ≃ₐ[F] K) (v : V), f (ρ g v) = τ g (f v)) :
    Nonempty (FiniteFreeHopfPointModel.{_, _, _, _, uC} R F K V ρ) := by
  exact ⟨finiteFreeHopfPointModelOfInjective m f hf he⟩

end
end Dubon2026
