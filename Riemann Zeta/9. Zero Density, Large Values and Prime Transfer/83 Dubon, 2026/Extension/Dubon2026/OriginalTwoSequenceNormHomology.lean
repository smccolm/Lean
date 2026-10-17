import Dubon2026.OriginalNormWitnessCoinvariants

/-! # A norm class represented in the actual first homology

Apply this to the internal-Hom fundamental and augmentation sequences
on DUB-17's converse norm route. The middle norm lift and the homology
boundary are retained explicitly. A zero resulting homology class is
equivalent to a literal norm witness in the original coefficient.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Two actual short exact coefficient sequences represent an invariant modulo norms by an original H1 class, with its exact boundary and zero criterion. -/
theorem originalTwoSequence_norm_homology_witness
    {k G : Type} [CommRing k] [Group G] [Fintype G]
    {Y : ShortComplex (Rep.{0} k G)} (hY : Y.ShortExact)
    {P Z : Rep.{0} k G} (f : Y.X₃ ⟶ P) (g : P ⟶ Z) (hfg : f ≫ g = 0)
    (hX : (ShortComplex.mk f g hfg).ShortExact)
    (hBnorm : ∀ x : Y.X₂, x ∈ Y.X₂.ρ.invariants → ∃ b, Y.X₂.ρ.norm b = x)
    (hBinj : OriginalNormCoinvariantInjective Y.X₂)
    (hPinj : OriginalNormCoinvariantInjective P)
    (hPfirst : Limits.IsZero (groupHomology P 1))
    (x : Y.X₁) (hx : x ∈ Y.X₁.ρ.invariants) :
    ∃ b : Y.X₂, Y.X₂.ρ.norm b = Y.f.hom x ∧
      ∃ y : groupHomology Z 1,
        (groupHomology.H0Iso Y.X₃).hom (groupHomology.δ hX 1 0 rfl y) =
          Representation.Coinvariants.mk Y.X₃.ρ (Y.g.hom b) ∧
        ((∃ t : Y.X₁, Y.X₁.ρ.norm t = x) ↔ y = 0) := by
  have hi : Y.f.hom x ∈ Y.X₂.ρ.invariants := by
    intro s
    rw [← Rep.hom_comm_apply, hx s]
  obtain ⟨b, hb⟩ := hBnorm (Y.f.hom x) hi
  have hn : Y.X₃.ρ.norm (Y.g.hom b) = 0 := by
    rw [← originalCoefficientMorphism_norm, hb]
    exact congrArg (fun j : Y.X₁ ⟶ Y.X₃ => j.hom x) Y.zero
  obtain ⟨y, hy⟩ := originalHomology_boundary_of_norm_zero hX hPinj (Y.g.hom b) hn
  have hm : Mono (groupHomology.δ hX 1 0 rfl) :=
    groupHomology.mono_δ_of_isZero hX 0 hPfirst
  have hδ := (ModuleCat.mono_iff_injective (groupHomology.δ hX 1 0 rfl)).mp hm
  have hc := originalNormWitness_iff_projectedCoinvariant_zero hY hBinj x b hb
  refine ⟨b, hb, y, hy, ?_⟩
  constructor
  · intro ht
    apply hδ
    have hz := hy.trans (hc.mp ht)
    have h0 : groupHomology.δ hX 1 0 rfl y = 0 := by
      apply (groupHomology.H0Iso Y.X₃).toLinearEquiv.injective
      exact hz.trans (groupHomology.H0Iso Y.X₃).toLinearEquiv.map_zero.symm
    exact h0.trans (groupHomology.δ hX 1 0 rfl).hom.map_zero.symm
  · intro hy0
    apply hc.mpr
    have hzero : (groupHomology.H0Iso Y.X₃).hom
        (groupHomology.δ hX 1 0 rfl y) = 0 := by
      rw [hy0]
      exact congrArg (fun v => (groupHomology.H0Iso Y.X₃).hom v)
        (groupHomology.δ hX 1 0 rfl).hom.map_zero |>.trans
          (groupHomology.H0Iso Y.X₃).hom.hom.map_zero
    exact hy.symm.trans hzero

end
end Dubon2026
