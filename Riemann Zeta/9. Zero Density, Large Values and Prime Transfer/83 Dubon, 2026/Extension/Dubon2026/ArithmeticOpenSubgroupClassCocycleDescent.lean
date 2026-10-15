import Dubon2026.ContinuousGaloisOpenSubgroupFinitePeriods
import Dubon2026.ArithmeticOpenSubgroupClassCoefficientLift
import Dubon2026.RestrictedOneCocycleDescent
import Dubon2026.ArithmeticClassesModOutsideColimit

/-! # Original arithmetic class cocycles on open subgroups descend to finite images

The original coefficient lift is restricted to the actual open subgroup.
Ambient finite periods give a finite Galois stage, and literal image-group
descent retains the cocycle values there. This supplies the finite input
to all open-subgroup class H1 vanishing needed for DUB-17 class formation.
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

/-- Every actual continuous class cocycle on an original open arithmetic subgroup descends to its actual finite Galois image, with unchanged coefficient values. -/
theorem arithmeticOpenSubgroupClassOneCocycle_exists_finite_descent
    (H : OpenSubgroup Gal(originalUnramifiedGaloisUnion (Ω := Ω) a / K))
    (c : H → arithmeticClassesModOutsideColimitRep K Ω a ha) (hc : Continuous c)
    (hcc : ∀ g h, c (g * h) =
      (arithmeticClassesModOutsideColimitRep K Ω a ha).ρ g.val (c h) + c g) :
    ∃ F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a),
      let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
      ∃ d : groupCohomology.cocycles₁
        (Rep.res π.range.subtype (arithmeticClassesModOutsideStageRep K Ω a ha F)),
        ∀ g : H, (coefficientRepresentationColimitOf
          (arithmeticGlobalClassesModOutsideStageRep K Ω a ha)
          (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha) F).hom
            (d (π.rangeRestrict g)) = c g := by
  have hLift := arithmeticOpenSubgroupClassOneCocycle_exists_coefficient_lift K Ω a ha H c hc hcc
  obtain ⟨E, b, hbc, hbcoc, hb⟩ := hLift
  letI : IsGalois K (originalUnramifiedGaloisUnion (Ω := Ω) a) := originalUnramifiedGaloisUnion_isGalois a
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  let A := fun F => Rep.res H.toSubgroup.subtype (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
  let f := fun E F (h : E ≤ F) =>
    (Rep.resFunctor H.toSubgroup.subtype).map
      (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h)
  letI : ∀ F, TopologicalSpace (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⊥
  letI : ∀ F, DiscreteTopology (arithmeticGlobalClassesModOutsideStageRep K Ω a ha F) := fun _ => ⟨rfl⟩
  let bMap : C(H, arithmeticGlobalClassesModOutsideStageRep K Ω a ha E) := ⟨b, hbc⟩
  have hPeriods := @continuousGaloisOpenSubgroupFunction_exists_finite_periods K
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
  let bF : groupCohomology.cocycles₁ (A F) := ⟨fun g => φ.hom (b g), by
    apply (groupCohomology.mem_cocycles₁_iff _).mpr
    intro g h
    have hc : b (g * h) = (A E).ρ g (b h) + b g := hbcoc g h
    exact (congrArg φ.hom hc).trans (by rw [map_add, Rep.hom_comm_apply])⟩
  let π : H →* Gal(F/K) := (AlgEquiv.restrictNormalHom F).comp H.toSubgroup.subtype
  have hperiod (g h : H) (he : π.rangeRestrict g = π.rangeRestrict h) : bF g = bF h := by
    have he' : π g = π h := congrArg Subtype.val he
    have hk : π (g⁻¹ * h) = 1 := by rw [map_mul, map_inv, he', inv_mul_cancel]
    have hv := hp g (g⁻¹ * h) hk
    have hv' : b g = b h := by simpa only [mul_inv_cancel_left] using hv.symm
    exact congrArg φ.hom hv'
  have hDescent := restrictedOneCocycle_exists_descent
    (Rep.res π.range.subtype (arithmeticClassesModOutsideStageRep K Ω a ha F))
    π.rangeRestrict π.rangeRestrict_surjective bF hperiod
  obtain ⟨d, hd⟩ := hDescent
  refine ⟨F, d, ?_⟩
  intro g
  rw [hd g]
  change Module.DirectLimit.of ℤ _
    (fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    F ((arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F hEF).hom.toLinearMap (b g)) = _
  exact (Module.DirectLimit.of_f (R := ℤ)
    (G := fun F => arithmeticGlobalClassesModOutsideStageRep K Ω a ha F)
    (f := fun E F h => (arithmeticGlobalClassesModOutsideStageTransition K Ω a ha E F h).hom.toLinearMap)
    (hij := hEF) (x := b g)).trans (hb g)

end
end Dubon2026
