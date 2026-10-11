import Dubon2026.GaloisUnitTwoCocycleFiniteDescent
import Dubon2026.DiscreteGaloisUnitActionContinuity

/-! # Original continuous unit H2 for any Galois extension of a finite base field -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [Finite K]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Descent constructs an actual finite coefficient field for the original
two-cocycle. The proved finite-field norm calculation then supplies a genuine
continuous one-cochain witness in the original extension. -/
theorem continuousFiniteBaseGaloisTwoCocycle_exists_coboundary
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ b : C(Gal(Ω/K), Rep.ofAlgebraAutOnUnits K Ω),
      continuousRepresentationCoboundaryTwo (Rep.ofAlgebraAutOnUnits K Ω)
        (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω)) b = c := by
  obtain ⟨F, hvalues, hperiod⟩ := continuousGaloisUnitTwoCocycle_exists_finiteField c
  obtain ⟨f, hf, hfactor⟩ :=
    galoisUnitTwoCocycle_exists_finite_descent F c.val hvalues hperiod
  letI : Finite F := Module.finite_of_finite K
  letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
  letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
  let cF : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K F) :=
    ⟨groupCohomology.cocyclesOfIsMulCocycle₂ hf, continuous_of_discreteTopology⟩
  have hcF := continuousFiniteFieldGaloisUnitH2_eq_zero
    (K := K) (L := F) (Submodule.Quotient.mk cF)
  obtain ⟨bF, hbF⟩ := (Submodule.Quotient.mk_eq_zero _).mp hcF
  let j : Gal(Ω/K) →* Gal(F/K) := AlgEquiv.restrictNormalHom F
  have hj : Continuous j := InfiniteGalois.restrictNormalHom_continuous F.toIntermediateField
  let i := Units.map F.toIntermediateField.val.toMonoidHom
  let e : Rep.ofAlgebraAutOnUnits K F → Rep.ofAlgebraAutOnUnits K Ω := fun v =>
    Rep.toAdditive.symm (Additive.ofMul (i (Additive.toMul (Rep.toAdditive v))))
  have he : Continuous e := continuous_of_discreteTopology
  let b : C(Gal(Ω/K), Rep.ofAlgebraAutOnUnits K Ω) :=
    ⟨fun g => e (bF (j g)), he.comp (bF.continuous.comp hj)⟩
  refine ⟨b, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext z
  rcases z with ⟨g, h⟩
  have hfb := congrArg (fun d : continuousRepresentationCocyclesTwo
    (Rep.ofAlgebraAutOnUnits K F) => d.val (j g, j h)) hbF
  change j g • (Additive.toMul (Rep.toAdditive (bF (j h)))) /
      Additive.toMul (Rep.toAdditive (bF (j g * j h))) *
      Additive.toMul (Rep.toAdditive (bF (j g))) = f (j g, j h) at hfb
  have haction : ∀ u : Fˣ, i (j g • u) = g • i u := by
    intro u
    apply Units.ext
    exact AlgEquiv.restrictNormal_commutes g F u.val
  have hmap := congrArg i hfb
  rw [map_mul, map_div, haction, hfactor] at hmap
  change g • i (Additive.toMul (Rep.toAdditive (bF (j h)))) /
      i (Additive.toMul (Rep.toAdditive (bF (j (g * h))))) *
      i (Additive.toMul (Rep.toAdditive (bF (j g)))) =
      Additive.toMul (Rep.toAdditive (c.val (g, h)))
  rw [j.map_mul]
  exact hmap

/-- The original continuous unit H2 vanishes for an arbitrary actual Galois
extension of a finite base field, with no finiteness assumption on Ω. -/
theorem continuousFiniteBaseGaloisUnitH2_eq_zero
    (x : ContinuousRepresentationH2 (Rep.ofAlgebraAutOnUnits K Ω)
      (discreteGaloisUnitAction_continuous (K := K) (Ω := Ω))) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact continuousFiniteBaseGaloisTwoCocycle_exists_coboundary c

end
end Dubon2026
