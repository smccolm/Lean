import Dubon2026.ArithmeticSPlaceCoefficientColimits

/-! # Exactness of the original fixed-support source coefficient colimit

The original finite source sequence is short exact. The pinned direct-limit
zero-detection theorem transports its exactness to the actual source colimit,
using the proved diagonal and quotient transition squares. This removes a
source coefficient exactness premise on DUB-17's global-duality route; the
arithmetic class-formation and continuous Ext comparisons remain separate.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K Ω : Type) [Field K] [Field Ω] [NumberField K] [Algebra K Ω]
  (a : 𝓞 K) (ha : a ≠ 0)
  [DecidableEq (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))]

/-- The original diagonal coefficient-colimit map is injective, by finite-stage exactness and actual direct-limit zero detection. -/
theorem arithmeticSPlaceColimitPrincipal_injective :
    Function.Injective (arithmeticSPlaceColimitPrincipal K Ω a ha) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨E, y, rfl⟩ := Module.DirectLimit.exists_of x
  rw [arithmeticSPlaceColimitPrincipal_of K Ω a ha E y] at hx
  obtain ⟨F, hEF, hF⟩ := Module.DirectLimit.of.zero_exact hx
  letI : NumberField F := NumberField.of_module_finite K F
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  have hF' : (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom
      (arithmeticSUnitCoefficientTransition K Ω a ha E F hEF y) = 0 :=
    (arithmeticSPlaceFiniteTransition_principal K Ω a ha E F hEF y).symm.trans hF
  have hy : arithmeticSUnitCoefficientTransition K Ω a ha E F hEF y = 0 :=
    originalSPlacePrincipalRepHom_injective K F _ _
      (hF'.trans (map_zero (arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom).symm)
  rw [← Module.DirectLimit.of_f (hij := hEF), hy, map_zero]

/-- The actual source colimit quotient is surjective, by the literal finite-stage quotient. -/
theorem arithmeticSPlaceColimitQuotient_surjective :
    Function.Surjective (arithmeticSPlaceColimitQuotient K Ω a ha) := by
  intro x
  obtain ⟨F, y, rfl⟩ := Module.DirectLimit.exists_of x
  have hq : Function.Surjective (arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom :=
    Submodule.mkQ_surjective _
  obtain ⟨z, rfl⟩ := hq y
  exact ⟨Module.DirectLimit.of ℤ
    (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (fun F => ArithmeticSPlaceFiniteStageRep K Ω a ha F)
    (arithmeticSPlaceTransitionMap K Ω a ha) F z,
    arithmeticSPlaceColimitQuotient_of K Ω a ha F z⟩

/-- Original diagonal S-units give zero in the actual source class colimit. -/
theorem arithmeticSPlaceColimitQuotient_principal
    (x : ArithmeticSUnitCoefficientColimit K Ω a ha) :
    arithmeticSPlaceColimitQuotient K Ω a ha (arithmeticSPlaceColimitPrincipal K Ω a ha x) = 0 := by
  obtain ⟨F, y, rfl⟩ := Module.DirectLimit.exists_of x
  letI : NumberField F := NumberField.of_module_finite K F
  rw [arithmeticSPlaceColimitPrincipal_of K Ω a ha F y,
    arithmeticSPlaceColimitQuotient_of K Ω a ha F
      ((arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom y)]
  have hz : (arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom
      ((arithmeticSPlaceFiniteStagePrincipal K Ω a ha F).hom y) = 0 :=
    (originalSPlaceIdeleClassRepHom_eq_zero_iff K F _ _ _).mpr ⟨y, rfl⟩
  rw [hz, map_zero]

/-- The kernel of the actual source colimit quotient is exactly the original diagonal colimit image. -/
theorem arithmeticSPlaceColimit_range_eq_ker :
    LinearMap.range (arithmeticSPlaceColimitPrincipal K Ω a ha) =
      LinearMap.ker (arithmeticSPlaceColimitQuotient K Ω a ha) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact arithmeticSPlaceColimitQuotient_principal K Ω a ha x
  · intro x hx
    change arithmeticSPlaceColimitQuotient K Ω a ha x = 0 at hx
    obtain ⟨E, y, rfl⟩ := Module.DirectLimit.exists_of x
    rw [arithmeticSPlaceColimitQuotient_of K Ω a ha E y] at hx
    obtain ⟨F, hEF, hF⟩ := Module.DirectLimit.of.zero_exact hx
    letI : NumberField F := NumberField.of_module_finite K F
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    have hF' : (arithmeticSPlaceFiniteStageQuotient K Ω a ha F).hom
        (arithmeticSPlaceTransitionMap K Ω a ha E F hEF y) = 0 :=
      (arithmeticSPlaceClassFiniteTransition_quotient K Ω a ha E F hEF y).symm.trans hF
    obtain ⟨u, hu⟩ := (originalSPlaceIdeleClassRepHom_eq_zero_iff K F _ _ _).mp hF'
    refine ⟨Module.DirectLimit.of ℤ
      (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
      (fun F => arithmeticSUnitFiniteStageRep K Ω a ha F)
      (arithmeticSUnitCoefficientTransition K Ω a ha) F u, ?_⟩
    rw [arithmeticSPlaceColimitPrincipal_of K Ω a ha F u]
    exact (congrArg (Module.DirectLimit.of ℤ
      (FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
      (fun F => ArithmeticSPlaceFiniteStageRep K Ω a ha F)
      (arithmeticSPlaceTransitionMap K Ω a ha) F) hu).trans (Module.DirectLimit.of_f (hij := hEF))

end
end Dubon2026
