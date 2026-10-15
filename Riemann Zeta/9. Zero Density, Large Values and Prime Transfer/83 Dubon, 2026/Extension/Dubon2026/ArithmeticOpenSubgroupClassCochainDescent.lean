import Dubon2026.ContinuousGaloisOpenSubgroupFinitePeriods
import Dubon2026.CompactCoefficientColimitLift
import Dubon2026.ArithmeticClassesModOutsideColimit

/-! # Original class coboundary cochains descend above any prescribed stage

A continuous one-cochain has compact finite image and finite Galois
periods. Descending its actual values above a given stage supplies the
finite coboundary witness needed to make the DUB-17 class H2 invariant
construction independent of representatives. No cocycle identity is
required of this witness.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]
  [TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha)]
  [DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha)]

/-- Every original continuous class one-cochain descends to the actual finite Galois image above the prescribed arithmetic stage. -/
theorem arithmeticOpenSubgroupClassCochain_exists_finite_descent
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (E₀ : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (c : C(H, arithmeticClassesModOutsideColimitRep K Ω a ha)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a), E₀ ≤ F ∧
      let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
      ∃ d : π.range → arithmeticClassesModOutsideStageRep K Ω a ha F,
        ∀ g : H, (coefficientRepresentationColimitOf
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
          (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom
            (d (π.rangeRestrict g)) = c g := by
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  letI : ∀ F, TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  have hLift := @compactCoefficientColimit_exists_lift ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    _ _ _ _ _ (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (fun F => (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).hV1)
    (fun F => (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F).hV2)
    (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    (inferInstance : TopologicalSpace (arithmeticClassesModOutsideColimitRep K Ω a ha))
    (inferInstance : DiscreteTopology (arithmeticClassesModOutsideColimitRep K Ω a ha))
    (fun F => (inferInstance : TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)))
    (fun F => (inferInstance : DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)))
    H inferInstance inferInstance c c.continuous
  obtain ⟨E, b, hbc, hb⟩ := hLift
  let bMap : C(H, arithmeticGlobalClassesModOutsideStageRep K Ω a ha E) := ⟨b, hbc⟩
  have hPeriods := @continuousGaloisOpenSubgroupFunction_exists_finite_periods K
    (originalUnramifiedGaloisUnion (Ω := Ω) a)
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha E)
    (inferInstance : Field K)
    (inferInstance : Field (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (inferInstance : Algebra K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (originalUnramifiedGaloisUnion_isGalois a)
    (⊥ : TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha E))
    ⟨rfl⟩ H (E₀ ⊔ E) bMap
  obtain ⟨F, hF, hp⟩ := hPeriods
  have hEF : E ≤ F := le_trans le_sup_right hF
  let φ := arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF
  let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
  have hfiber (g h : H) (he : π.rangeRestrict g = π.rangeRestrict h) : b g = b h := by
    have he' : π g = π h := congrArg Subtype.val he
    have hk : π (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, he', inv_mul_cancel]
    have hv := hp g (g⁻¹ * h) hk
    simpa only [mul_inv_cancel_left] using hv.symm
  let d : π.range → arithmeticClassesModOutsideStageRep K Ω a ha F :=
    fun z => φ.hom (b (Function.surjInv π.rangeRestrict_surjective z))
  have hd (g : H) : d (π.rangeRestrict g) = φ.hom (b g) :=
    congrArg φ.hom (hfiber _ g (Function.surjInv_eq π.rangeRestrict_surjective (π.rangeRestrict g)))
  refine ⟨F, le_trans le_sup_left hF, d, ?_⟩
  intro g
  rw [hd g]
  exact (Module.DirectLimit.of_f (R := ℤ)
    (G := fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (f := fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    (hij := hEF) (x := b g)).trans (hb g)

end
end Dubon2026
