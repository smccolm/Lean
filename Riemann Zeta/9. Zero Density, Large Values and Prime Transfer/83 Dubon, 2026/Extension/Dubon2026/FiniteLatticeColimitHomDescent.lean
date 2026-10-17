import Dubon2026.CompactCoefficientColimitLift
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # A finite free coefficient morphism descends to an actual stage

Lift only the finitely many basis values, extend them linearly, and kill
the compact family of equivariance defects on the same finite basis.
This is the required descent for the infinite underlying original relation
lattice in DUB-17's degree-one class/Ext comparison and reverse localization.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {R G ι : Type} [CommRing R] [Group G] [TopologicalSpace G] [CompactSpace G]
  [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirectedOrder ι]
  (A : ι → Rep.{0} R G) (f : ∀ i j, i ≤ j → (A i ⟶ A j))
  [DirectedSystem (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap)]
  [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
  [TopologicalSpace (coefficientRepresentationColimit A f)]
  [DiscreteTopology (coefficientRepresentationColimit A f)]
  (B : Rep.{0} R G) [Module.Finite R B] [Module.Free R B]
  [TopologicalSpace B] [DiscreteTopology B]

/-- An actual equivariant morphism from a finite free coefficient lattice
to the original discrete colimit lifts equivariantly to one actual stage. -/
theorem finiteLatticeColimitHom_exists_stage
    (hA : ∀ i, Continuous (fun z : G × A i => (A i).ρ z.1 z.2))
    (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
    (φ : B ⟶ coefficientRepresentationColimit A f) :
    ∃ i, ∃ ψ : B ⟶ A i, ψ ≫ coefficientRepresentationColimitOf A f i = φ := by
  classical
  let J := Module.Free.ChooseBasisIndex R B
  let β := Module.Free.chooseBasis R B
  letI : TopologicalSpace J := ⊥
  letI : DiscreteTopology J := ⟨rfl⟩
  have hφ : Continuous (fun e : J => φ.hom (β e)) := continuous_of_discreteTopology
  obtain ⟨i, b, _, hbc⟩ := @compactCoefficientColimit_exists_lift R ι
    _ _ _ _ _ (fun i => A i) (fun i => (A i).hV1) (fun i => (A i).hV2)
    (fun i j h => (f i j h).hom.toLinearMap)
    (inferInstance : TopologicalSpace (coefficientRepresentationColimit A f))
    (inferInstance : DiscreteTopology (coefficientRepresentationColimit A f))
    (fun i => (inferInstance : TopologicalSpace (A i)))
    (fun i => (inferInstance : DiscreteTopology (A i))) J
    (inferInstance : TopologicalSpace J) (inferInstance : CompactSpace J)
    (fun e => φ.hom (β e)) hφ
  let l : B →ₗ[R] A i := β.constr R b
  have hlmap : (coefficientRepresentationColimitOf A f i).hom.toLinearMap.comp l =
      φ.hom.toLinearMap := by
    apply β.ext
    intro e
    change (coefficientRepresentationColimitOf A f i).hom ((β.constr R b) (β e)) = φ.hom (β e)
    rw [β.constr_basis]
    exact hbc e
  have hl (x : B) : (coefficientRepresentationColimitOf A f i).hom (l x) = φ.hom x :=
    LinearMap.congr_fun hlmap x
  let d : G × J → A i := fun z => (A i).ρ z.1 (l (β z.2)) - l (B.ρ z.1 (β z.2))
  have hc : Continuous (fun z : G × J => β z.2) :=
    (continuous_of_discreteTopology : Continuous β).comp continuous_snd
  have hL : Continuous l := continuous_of_discreteTopology
  have hd : Continuous d :=
    ((hA i).comp (continuous_fst.prodMk (hL.comp hc))).sub
      (hL.comp (hB.comp (continuous_fst.prodMk hc)))
  have hr : (Set.range d).Finite := (isCompact_range hd).finite_of_discrete
  have hz (x : A i) (hx : x ∈ hr.toFinset) :
      Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i x = 0 := by
    obtain ⟨⟨g, e⟩, rfl⟩ := hr.mem_toFinset.mp hx
    change (coefficientRepresentationColimitOf A f i).hom
      ((A i).ρ g (l (β e)) - l (B.ρ g (β e))) = 0
    rw [map_sub, Rep.hom_comm_apply, hl, hl, Rep.hom_comm_apply, sub_self]
  obtain ⟨j, hij, hj⟩ := coefficientColimit_finite_zero_detected
    (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i hr.toFinset hz
  let ψ : B ⟶ A j := Rep.ofHom {
    toLinearMap := (f i j hij).hom.toLinearMap.comp l
    isIntertwining' g := by
      apply β.ext
      intro e
      have he := hj (d (g, e)) (hr.mem_toFinset.mpr (Set.mem_range_self (g, e)))
      change (f i j hij).hom ((A i).ρ g (l (β e)) - l (B.ρ g (β e))) = 0 at he
      rw [map_sub, Rep.hom_comm_apply] at he
      exact (sub_eq_zero.mp he).symm }
  refine ⟨j, ψ, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (Module.DirectLimit.of_f (f := fun i j h => (f i j h).hom.toLinearMap)
    (hij := hij) (x := l x)).trans (hl x)

/-- The actual finite free coefficient morphism can be descended above
any prescribed stage, retaining its original arithmetic field. -/
theorem finiteLatticeColimitHom_exists_stage_ge
    (hA : ∀ i, Continuous (fun z : G × A i => (A i).ρ z.1 z.2))
    (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
    (i₀ : ι) (φ : B ⟶ coefficientRepresentationColimit A f) :
    ∃ i, i₀ ≤ i ∧ ∃ ψ : B ⟶ A i, ψ ≫ coefficientRepresentationColimitOf A f i = φ := by
  obtain ⟨i, ψ, hψ⟩ := finiteLatticeColimitHom_exists_stage A f B hA hB φ
  obtain ⟨j, hij, hi₀j⟩ := exists_ge_ge i i₀
  refine ⟨j, hi₀j, ψ ≫ f i j hij, ?_⟩
  calc
    (ψ ≫ f i j hij) ≫ coefficientRepresentationColimitOf A f j =
        ψ ≫ coefficientRepresentationColimitOf A f i := by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro x
      exact Module.DirectLimit.of_f (f := fun i j h => (f i j h).hom.toLinearMap)
        (hij := hij) (x := ψ.hom x)
    _ = φ := hψ

end
end Dubon2026
