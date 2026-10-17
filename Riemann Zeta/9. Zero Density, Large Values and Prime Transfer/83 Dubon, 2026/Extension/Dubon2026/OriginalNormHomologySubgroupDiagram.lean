import Dubon2026.OriginalNormHomologySubgroupTransfer
import Dubon2026.OriginalCoinducedInvariantNorms

/-! # Norm-homology witnesses through an actual subgroup diagram

A commuting pair of coefficient sequences carries a source norm witness
to a full-group witness for the literal relative trace. The actual
homology boundary retains the same image. This is the transport used in
DUB-17's local/global fundamental norm comparison for inertia control.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2 Submodule.module
variable {k G : Type} [CommRing k] [Group G] [Fintype G]
  (S : Subgroup G) [S.Normal] [Fintype S] [Fintype (G ⧸ S)]

/-- A genuine group/coefficient diagram carries a literal source norm
witness and its homology boundary to the full-group trace witness. -/
theorem originalNormHomology_subgroup_diagram
    {X : ShortComplex (Rep.{0} k S)} {Y : ShortComplex (Rep.{0} k G)}
    (m : X ⟶ Y.map (Rep.resFunctor S.subtype))
    {P Z : Rep.{0} k S} (f : X.X₃ ⟶ P) (g : P ⟶ Z) (hfg : f ≫ g = 0)
    (hE : (ShortComplex.mk f g hfg).ShortExact)
    {Q W : Rep.{0} k G} (u : Y.X₃ ⟶ Q) (v : Q ⟶ W) (huv : u ≫ v = 0)
    (hF : (ShortComplex.mk u v huv).ShortExact)
    (n : ShortComplex.mk f g hfg ⟶
      (ShortComplex.mk u v huv).map (Rep.resFunctor S.subtype))
    (hn : n.τ₁ = m.τ₃)
    (x : X.X₁.ρ.invariants) (b : X.X₂) (hb : X.X₂.ρ.norm b = X.f.hom x.val)
    (y : groupHomology Z 1)
    (hy : (groupHomology.H0Iso X.X₃).hom (groupHomology.δ hE 1 0 rfl y) =
      Representation.Coinvariants.mk X.X₃.ρ (X.g.hom b)) :
    Y.X₂.ρ.norm (m.τ₂.hom b) = Y.f.hom
        (((Y.X₁.quotientToInvariants S).ρ.norm ((Rep.invariantsFunctor k S).map m.τ₁ x)).val) ∧
      (groupHomology.H0Iso Y.X₃).hom
        (groupHomology.δ hF 1 0 rfl (groupHomology.map S.subtype n.τ₃ 1 y)) =
        Representation.Coinvariants.mk Y.X₃.ρ (Y.g.hom (m.τ₂.hom b)) := by
  have hmid : (Rep.res S.subtype Y.X₂).ρ.norm (m.τ₂.hom b) =
      Y.f.hom (((Rep.invariantsFunctor k S).map m.τ₁ x).val) := by
    exact (originalCoefficientMorphism_norm m.τ₂ b).symm.trans
      ((congrArg m.τ₂.hom hb).trans (congrArg (fun j => j.hom x.val) m.comm₁₂.symm))
  refine ⟨originalSubgroup_norm_lift_trace S Y.f _ _ hmid, ?_⟩
  have hδ := originalHomology_groupChange_boundary_representative S.subtype n hE hF y
    (X.g.hom b) hy
  have hπ : n.τ₁.hom (X.g.hom b) = Y.g.hom (m.τ₂.hom b) := by
    rw [hn]
    exact congrArg (fun j => j.hom b) m.comm₂₃.symm
  exact hδ.trans (congrArg (Representation.Coinvariants.mk Y.X₃.ρ) hπ)

end
end Dubon2026
