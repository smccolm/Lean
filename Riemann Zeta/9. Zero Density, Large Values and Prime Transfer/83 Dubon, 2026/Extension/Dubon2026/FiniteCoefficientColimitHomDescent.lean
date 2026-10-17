import Dubon2026.CompactCoefficientColimitLift

/-! # A finite coefficient morphism descends to an actual colimit stage

Finite coefficient values and compact action defects can be killed at one
common stage using the existing direct-limit zero detector. This represents
the actual invariant class-Hom coefficients in the degree-zero term of
DUB-17's source class/Ext comparison. Descent of the infinite underlying
relation lattice is a separate dependency of the degree-one criterion.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirectedOrder ι]
  (A : ι → Rep.{0} ℤ G) (f : ∀ i j, i ≤ j → (A i ⟶ A j))
  [DirectedSystem (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap)]
  [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
  [TopologicalSpace (coefficientRepresentationColimit A f)]
  [DiscreteTopology (coefficientRepresentationColimit A f)]
  (B : Rep.{0} ℤ G) [Finite B] [TopologicalSpace B] [DiscreteTopology B]

omit [IsTopologicalGroup G] in
/-- Every actual equivariant morphism from a finite integer coefficient
to the original discrete colimit lifts equivariantly to one original stage.
Only the original coefficient actions are assumed continuous. -/
theorem finiteCoefficientColimitHom_exists_stage
    (hA : ∀ i, Continuous (fun z : G × A i => (A i).ρ z.1 z.2))
    (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
    (φ : B ⟶ coefficientRepresentationColimit A f) :
    ∃ i, ∃ ψ : B ⟶ A i, ψ ≫ coefficientRepresentationColimitOf A f i = φ := by
  classical
  have hφ : Continuous (fun x : B => φ.hom x) := continuous_of_discreteTopology
  obtain ⟨i, b, hb, hbc⟩ := @compactCoefficientColimit_exists_lift ℤ ι
    _ _ _ _ _ (fun i => A i) (fun i => (A i).hV1) (fun i => (A i).hV2)
    (fun i j h => (f i j h).hom.toLinearMap)
    (inferInstance : TopologicalSpace (coefficientRepresentationColimit A f))
    (inferInstance : DiscreteTopology (coefficientRepresentationColimit A f))
    (fun i => (inferInstance : TopologicalSpace (A i)))
    (fun i => (inferInstance : DiscreteTopology (A i))) B
    (inferInstance : TopologicalSpace B) (inferInstance : CompactSpace B)
    (fun x => φ.hom x) hφ
  have hbc' (x : B) : (coefficientRepresentationColimitOf A f i).hom (b x) = φ.hom x := hbc x
  let da : B × B → A i := fun z => b (z.1 + z.2) - b z.1 - b z.2
  let dg : G × B → A i := fun z => (A i).ρ z.1 (b z.2) - b (B.ρ z.1 z.2)
  have hda : Continuous da := continuous_of_discreteTopology
  have hdg : Continuous dg :=
    ((hA i).comp (continuous_fst.prodMk (hb.comp continuous_snd))).sub (hb.comp hB)
  have hra : (Set.range da).Finite := (isCompact_range hda).finite_of_discrete
  have hrg : (Set.range dg).Finite := (isCompact_range hdg).finite_of_discrete
  let T := hra.toFinset ∪ hrg.toFinset
  have hz (x : A i) (hx : x ∈ T) :
      Module.DirectLimit.of ℤ ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i x = 0 := by
    rcases Finset.mem_union.mp hx with ha | hg
    · obtain ⟨⟨u, v⟩, rfl⟩ := hra.mem_toFinset.mp ha
      change (coefficientRepresentationColimitOf A f i).hom (b (u + v) - b u - b v) = 0
      rw [map_sub, map_sub, hbc', hbc', hbc', map_add]
      abel
    · obtain ⟨⟨g, u⟩, rfl⟩ := hrg.mem_toFinset.mp hg
      change (coefficientRepresentationColimitOf A f i).hom ((A i).ρ g (b u) - b (B.ρ g u)) = 0
      rw [map_sub, Rep.hom_comm_apply, hbc', hbc', Rep.hom_comm_apply, sub_self]
  obtain ⟨j, hij, hj⟩ := coefficientColimit_finite_zero_detected
    (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i T hz
  let b' : B → A j := fun x => (f i j hij).hom (b x)
  have hadd (u v : B) : b' (u + v) = b' u + b' v := by
    have he := hj (da (u, v)) (Finset.mem_union_left _
      (hra.mem_toFinset.mpr (Set.mem_range_self (u, v))))
    change (f i j hij).hom (b (u + v) - b u - b v) = 0 at he
    rw [map_sub, map_sub, sub_sub] at he
    exact sub_eq_zero.mp he
  let bHom : B →+ A j := AddMonoidHom.mk' b' hadd
  let bLin : B →ₗ[ℤ] A j := {
    toFun := bHom
    map_add' := bHom.map_add
    map_smul' := fun n x => by
      change bHom (B.hV2.toSMul.smul n x) = (A j).hV2.toSMul.smul n (bHom x)
      rw [int_smul_eq_zsmul B.hV2, int_smul_eq_zsmul (A j).hV2]
      exact map_zsmul bHom n x }
  let ψ : B ⟶ A j := Rep.ofHom {
    toLinearMap := bLin
    isIntertwining' g := by
      apply LinearMap.ext
      intro u
      have he := hj (dg (g, u)) (Finset.mem_union_right _
        (hrg.mem_toFinset.mpr (Set.mem_range_self (g, u))))
      change (f i j hij).hom ((A i).ρ g (b u) - b (B.ρ g u)) = 0 at he
      rw [map_sub, Rep.hom_comm_apply] at he
      exact (sub_eq_zero.mp he).symm }
  refine ⟨j, ψ, ?_⟩
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact (Module.DirectLimit.of_f (f := fun i j h => (f i j h).hom.toLinearMap)
    (hij := hij) (x := b x)).trans (hbc x)

omit [IsTopologicalGroup G] in
/-- The same actual morphism descends above any prescribed coefficient
stage, so its source finite field can be retained in the arithmetic application. -/
theorem finiteCoefficientColimitHom_exists_stage_ge
    (hA : ∀ i, Continuous (fun z : G × A i => (A i).ρ z.1 z.2))
    (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))
    (i₀ : ι) (φ : B ⟶ coefficientRepresentationColimit A f) :
    ∃ i, i₀ ≤ i ∧ ∃ ψ : B ⟶ A i, ψ ≫ coefficientRepresentationColimitOf A f i = φ := by
  obtain ⟨i, ψ, hψ⟩ := finiteCoefficientColimitHom_exists_stage A f B hA hB φ
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
