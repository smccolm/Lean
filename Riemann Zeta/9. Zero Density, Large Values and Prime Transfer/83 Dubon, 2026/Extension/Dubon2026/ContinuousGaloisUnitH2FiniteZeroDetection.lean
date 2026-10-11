import Dubon2026.GaloisUnitFiniteStageTower
import Dubon2026.GaloisUnitFiniteCoboundaryReflection

/-! # Actual continuous Galois unit H2 detects zero at a genuine finite stage -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  (E : FiniteGaloisIntermediateField K Ω)
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

omit [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] [IsGalois K Ω] in
private theorem galoisUnitCochain_tower_identity
    (F : FiniteGaloisIntermediateField K Ω) (hEF : E ≤ F)
    (c : Gal(E/K) × Gal(E/K) → Eˣ) (b : Gal(Ω/K) → Ωˣ)
    (hc : ∀ g h : Gal(Ω/K),
      Units.map E.toIntermediateField.val.toMonoidHom
        (c (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)) =
          g • b h / b (g * h) * b g) :
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    ∀ g h : Gal(Ω/K),
      Units.map F.toIntermediateField.val.toMonoidHom
        (Units.map (algebraMap E F).toMonoidHom
          (c (AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F g),
            AlgEquiv.restrictNormalHom E (AlgEquiv.restrictNormalHom F h)))) =
              g • b h / b (g * h) * b g := by
  letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
  haveI : IsScalarTower E F Ω := .of_algebraMap_eq' rfl
  intro g h
  rw [← hc, IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F g,
    IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E F h]
  apply Units.ext
  rfl

omit [TopologicalSpace (Rep.ofAlgebraAutOnUnits K E)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K E)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)] in
private theorem galoisUnitFiniteCocycle_zero_of_descended_witness
    (F : FiniteGaloisIntermediateField K Ω)
    [TopologicalSpace (Rep.ofAlgebraAutOnUnits K F)]
    [DiscreteTopology (Rep.ofAlgebraAutOnUnits K F)]
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K F))
    (b : Gal(Ω/K) → Ωˣ)
    (hv : ∀ g, (b g).val ∈ F.toIntermediateField)
    (hp : ∀ g u, AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g)
    (hc : ∀ g h : Gal(Ω/K),
      Units.map F.toIntermediateField.val.toMonoidHom
        (Additive.toMul (Rep.toAdditive (c.val
          (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)))) =
            g • b h / b (g * h) * b g) :
    (Submodule.Quotient.mk c : GaloisUnitContinuousH2 (K := K) (Ω := F)) = 0 := by
  obtain ⟨bF, hbF⟩ := galoisUnitFiniteCocycle_eq_coboundary_of_inflated_eq
    (K := K) (Ω := Ω) F (fun z => Additive.toMul (Rep.toAdditive (c.val z))) b hv hp hc
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  let bC : C(Gal(F/K), Rep.ofAlgebraAutOnUnits K F) :=
    ⟨fun g => Rep.toAdditive.symm (Additive.ofMul (bF g)), continuous_of_discreteTopology⟩
  refine ⟨bC, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext z
  change z.1 • bF z.2 / bF (z.1 * z.2) * bF z.1 =
    Additive.toMul (Rep.toAdditive (c.val z))
  exact (hbF z.1 z.2).symm

/-- If an original finite-stage H2 class vanishes after actual inflation,
the original continuous coboundary witness descends to a larger genuine finite
Galois stage. The same original class vanishes after the actual finite-tower
inflation there. No stagewise vanishing certificate is assumed. -/
theorem continuousGaloisUnitH2_zero_detected_at_finite_stage
    (x : GaloisUnitContinuousH2 (K := K) (Ω := E))
    (hx : galoisUnitFiniteStageH2Inflation E x = 0) :
    ∃ F : FiniteGaloisIntermediateField K Ω, ∃ hEF : E ≤ F,
      letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
      letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
      letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
      finiteGaloisUnitTowerH2Inflation K E F x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [galoisUnitFiniteStageH2Inflation_mk] at hx
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨F, hEF, hvalues, hperiod⟩ :=
      continuousGaloisUnitCochain_exists_finiteField E b
    refine ⟨F, hEF, ?_⟩
    letI : Algebra E F := (IntermediateField.inclusion hEF).toAlgebra
    haveI : IsScalarTower E F Ω := .of_algebraMap_eq' rfl
    letI : TopologicalSpace (Rep.ofAlgebraAutOnUnits K F) := ⊥
    letI : DiscreteTopology (Rep.ofAlgebraAutOnUnits K F) := ⟨rfl⟩
    let cF := finiteGaloisUnitTowerCocycleInflation K E F c
    let bU : Gal(Ω/K) → Ωˣ := fun g => Additive.toMul (Rep.toAdditive (b g))
    let f : Gal(F/K) × Gal(F/K) → Fˣ :=
      fun z => Additive.toMul (Rep.toAdditive (cF.val z))
    have hp : ∀ g u, AlgEquiv.restrictNormalHom F u = 1 → bU (g * u) = bU g := by
      intro g u hu
      exact congrArg (fun v => Additive.toMul (Rep.toAdditive v)) (hperiod g u hu)
    have hcE : ∀ g h : Gal(Ω/K),
        Units.map E.toIntermediateField.val.toMonoidHom
          (Additive.toMul (Rep.toAdditive (c.val
            (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)))) =
            g • bU h / bU (g * h) * bU g := by
      intro g h
      have hbb := congrArg (fun d : continuousRepresentationCocyclesTwo
        (Rep.ofAlgebraAutOnUnits K Ω) => d.val (g, h)) hb
      change g • bU h / bU (g * h) * bU g =
        Units.map E.toIntermediateField.val.toMonoidHom
          (Additive.toMul (Rep.toAdditive (c.val
            (AlgEquiv.restrictNormalHom E g, AlgEquiv.restrictNormalHom E h)))) at hbb
      exact hbb.symm
    have hc : ∀ g h : Gal(Ω/K),
        Units.map F.toIntermediateField.val.toMonoidHom
          (f (AlgEquiv.restrictNormalHom F g, AlgEquiv.restrictNormalHom F h)) =
            g • bU h / bU (g * h) * bU g :=
      galoisUnitCochain_tower_identity E F hEF
        (fun z => Additive.toMul (Rep.toAdditive (c.val z))) bU hcE
    have hv : ∀ g : Gal(Ω/K), (bU g).val ∈ F.toIntermediateField := hvalues
    rw [finiteGaloisUnitTowerH2Inflation_mk]
    exact galoisUnitFiniteCocycle_zero_of_descended_witness F cF bU hv hp hc

end
end Dubon2026
