import Dubon2026.OpenSubgroupTwoCochainFinitePeriods
import Dubon2026.ArithmeticOpenSubgroupClassTwoCocycleLift
import Dubon2026.RestrictedTwoCocycleDescent

/-! # Actual open-subgroup class two-cocycles descend to their finite Galois image

The faithful coefficient lift, common finite periods and original
restriction action give a literal finite-image two-cocycle with the same
values. This removes the finite-representative premise in the H2 invariant
construction needed by DUB-17's P-class formation and global duality.
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

/-- Every original continuous class two-cocycle on an actual open subgroup descends with unchanged values to its actual finite Galois image. -/
theorem arithmeticOpenSubgroupClassTwoCocycle_exists_finite_descent
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (c : H × H → arithmeticClassesModOutsideColimitRep K Ω a ha) (hc : Continuous c)
    (hcc : ∀ g h k, c (g * h, k) + c (g, h) =
      (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g.val (c (h, k)) + c (g, h * k)) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
      ∃ d : groupCohomology.cocycles₂
        (Rep.res π.range.subtype (arithmeticClassesModOutsideStageRep K Ω a ha F)),
        ∀ g h : H, (coefficientRepresentationColimitOf
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
          (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom
            (d (π.rangeRestrict g, π.rangeRestrict h)) = c (g, h) := by
  have hLift := arithmeticOpenSubgroupClassTwoCocycle_exists_coefficient_lift K Ω a ha H c hc hcc
  obtain ⟨E, b, hbc, hbcoc, hb⟩ := hLift
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  let A := fun F => Rep.res H.toSubgroup.subtype (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
  let f := fun E F (h : E ≤ F) =>
    (Rep.resFunctor H.toSubgroup.subtype).map
      (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h)
  letI : ∀ F, TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  let bMap : C(H × H, arithmeticGlobalClassesModOutsideStageRep K Ω a ha E) := ⟨b, hbc⟩
  have hPeriods := @continuousGaloisOpenSubgroupTwoFunction_exists_finite_periods K
    (originalUnramifiedGaloisUnion (Ω := Ω) a)
    (arithmeticGlobalClassesModOutsideStageRep K Ω a ha E)
    (inferInstance : Field K)
    (inferInstance : Field (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (inferInstance : Algebra K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (originalUnramifiedGaloisUnion_isGalois a)
    (⊥ : TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha E))
    ⟨rfl⟩ H E bMap
  obtain ⟨F, hEF, hp⟩ := hPeriods
  let φ := f E F hEF
  let bF : groupCohomology.cocycles₂ (A F) := ⟨fun z => φ.hom (b z), by
    apply (groupCohomology.mem_cocycles₂_iff _).mpr
    intro g h k
    have hc : b (g * h, k) + b (g, h) = (A E).ρ g (b (h, k)) + b (g, h * k) := hbcoc g h k
    have he := congrArg φ.hom hc
    rw [map_add, map_add, Rep.hom_comm_apply] at he
    exact he⟩
  let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
  have hperiod (g h g' h' : H)
      (he : π.rangeRestrict g = π.rangeRestrict g')
      (hf : π.rangeRestrict h = π.rangeRestrict h') : bF (g, h) = bF (g', h') := by
    have he' : π g = π g' := congrArg Subtype.val he
    have hf' : π h = π h' := congrArg Subtype.val hf
    have hk : π (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, he', inv_mul_cancel]
    have hl : π (h⁻¹ * h') = 1 := by rw [map_mul, map_inv, hf', inv_mul_cancel]
    have hv := hp g h (g⁻¹ * g') (h⁻¹ * h') hk hl
    have hv' : b (g, h) = b (g', h') := by simpa only [mul_inv_cancel_left] using hv.symm
    exact congrArg φ.hom hv'
  have hDescent := restrictedTwoCocycle_exists_descent
    (Rep.res π.range.subtype (arithmeticClassesModOutsideStageRep K Ω a ha F))
    π.rangeRestrict π.rangeRestrict_surjective bF hperiod
  obtain ⟨d, hd⟩ := hDescent
  refine ⟨F, d, ?_⟩
  intro g h
  rw [hd g h]
  change Module.DirectLimit.of ℤ _
    (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    F ((arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF).hom.toLinearMap (b (g, h))) = _
  exact (Module.DirectLimit.of_f (R := ℤ)
    (G := fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (f := fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    (hij := hEF) (x := b (g, h))).trans (hb (g, h))

end
end Dubon2026
