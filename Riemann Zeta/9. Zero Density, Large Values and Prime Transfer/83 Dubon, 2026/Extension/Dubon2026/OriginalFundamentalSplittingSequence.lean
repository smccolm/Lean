import Dubon2026.OriginalFundamentalCocycleTwist

/-! # The actual fundamental-class splitting coefficient

The middle coefficient is the original coefficient times the actual
augmentation ideal, with the action twisted by the supplied two-cocycle.
Its short exact sequence is proved here. This is the specific extension
whose subgroup vanishing is needed for DUB-17's finite class/Ext duality;
no vanishing, cup-product or duality property is asserted by definition.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (C : Rep k G) (φ : groupCohomology.cocycles₂ C)

/-- The actual two-cocycle gives the twisted action on the coefficient and augmentation ideal. -/
def originalFundamentalSplittingAction : Representation k G (C × originalAugmentationIdeal k G) where
  toFun g := LinearMap.prod
    (C.ρ g ∘ₗ LinearMap.fst k C (originalAugmentationIdeal k G) +
      originalFundamentalCocycleTwist C φ g ∘ₗ
        (LinearMap.ker (originalAugmentation k G).hom.toLinearMap).subtype ∘ₗ
          LinearMap.snd k C (originalAugmentationIdeal k G))
    ((originalAugmentationIdeal k G).ρ g ∘ₗ LinearMap.snd k C (originalAugmentationIdeal k G))
  map_one' := LinearMap.ext fun v => Prod.ext
    (by
      change C.ρ 1 v.1 + originalFundamentalCocycleTwist C φ 1 (v.2 : G →₀ k) = v.1
      rw [map_one, originalFundamentalCocycleTwist_one C φ _
        ((originalAugmentationIdeal_mem k G _).1 v.2.2), add_zero]
      rfl)
    (by change (originalAugmentationIdeal k G).ρ 1 v.2 = v.2; rw [map_one]; rfl)
  map_mul' g h := LinearMap.ext fun v => Prod.ext
    (by
      change C.ρ (g * h) v.1 + originalFundamentalCocycleTwist C φ (g * h) (v.2 : G →₀ k) =
        C.ρ g (C.ρ h v.1 + originalFundamentalCocycleTwist C φ h (v.2 : G →₀ k)) +
          originalFundamentalCocycleTwist C φ g ((originalAugmentationIdeal k G).ρ h v.2 : G →₀ k)
      rw [map_mul, map_add, originalFundamentalCocycleTwist_mul C φ g h _
        ((originalAugmentationIdeal_mem k G _).1 v.2.2), add_assoc,
        originalAugmentationIdeal_action]
      rfl)
    (by
      change (originalAugmentationIdeal k G).ρ (g * h) v.2 =
        (originalAugmentationIdeal k G).ρ g ((originalAugmentationIdeal k G).ρ h v.2)
      rw [map_mul]
      rfl)

/-- The actual fundamental splitting representation. -/
abbrev originalFundamentalSplittingModule : Rep k G :=
  Rep.of (originalFundamentalSplittingAction C φ)

/-- The original coefficient's inclusion into its actual twisted extension. -/
def originalFundamentalSplittingInclusion : C ⟶ originalFundamentalSplittingModule C φ :=
  Rep.ofHom ⟨LinearMap.inl k C (originalAugmentationIdeal k G),
    fun g => LinearMap.ext fun c => Prod.ext
      (by
        change C.ρ g c = C.ρ g c + originalFundamentalCocycleTwist C φ g
          ((0 : originalAugmentationIdeal k G) : G →₀ k)
        rw [ZeroMemClass.coe_zero, map_zero, add_zero])
      (by change (0 : originalAugmentationIdeal k G) = (originalAugmentationIdeal k G).ρ g 0
          rw [map_zero])⟩

/-- The actual twisted extension's projection to the augmentation ideal. -/
def originalFundamentalSplittingProjection :
    originalFundamentalSplittingModule C φ ⟶ originalAugmentationIdeal k G :=
  Rep.ofHom ⟨LinearMap.snd k C (originalAugmentationIdeal k G), fun _ => LinearMap.ext fun _ => rfl⟩

/-- The literal coefficient complex associated to the fundamental cocycle. -/
def originalFundamentalSplittingShortComplex : ShortComplex (Rep k G) where
  X₁ := C
  X₂ := originalFundamentalSplittingModule C φ
  X₃ := originalAugmentationIdeal k G
  f := originalFundamentalSplittingInclusion C φ
  g := originalFundamentalSplittingProjection C φ
  zero := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

/-- The actual twisted coefficient extension is short exact. -/
theorem originalFundamentalSplittingShortComplex_shortExact :
    (originalFundamentalSplittingShortComplex C φ).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr LinearMap.inl_injective
    epi_g := (Rep.epi_iff_surjective _).mpr (fun x => ⟨(0, x), rfl⟩) }
  apply ((originalFundamentalSplittingShortComplex C φ).exact_map_iff_of_faithful
    (forget₂ (Rep k G) (ModuleCat k))).mp
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro v hv
  exact ⟨v.1, Prod.ext rfl hv.symm⟩

end
end Dubon2026
