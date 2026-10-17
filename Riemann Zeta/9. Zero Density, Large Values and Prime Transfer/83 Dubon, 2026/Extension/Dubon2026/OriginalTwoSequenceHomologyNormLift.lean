import Dubon2026.OriginalTwoSequenceNormHomology

/-! # Every original homology class has a literal middle norm lift

The reverse construction for two short exact sequences is needed for
the actual abelian norm index. That index is an input to the prescribed
norm-field construction, then invariant norm divisibility, finite
relation extension and DUB-17's global-duality chain.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Every actual first homology class determines an invariant coefficient and a literal middle norm lift with exactly its original boundary. -/
theorem originalTwoSequence_homology_norm_lift
    {k G : Type} [CommRing k] [Group G] [Fintype G]
    {Y : ShortComplex (Rep.{0} k G)} (hY : Y.ShortExact)
    {P Z : Rep.{0} k G} (f : Y.X₃ ⟶ P) (g : P ⟶ Z) (hfg : f ≫ g = 0)
    (hX : (ShortComplex.mk f g hfg).ShortExact)
    (y : groupHomology Z 1) :
    ∃ x : Y.X₁, x ∈ Y.X₁.ρ.invariants ∧
      ∃ b : Y.X₂, Y.X₂.ρ.norm b = Y.f.hom x ∧
        (groupHomology.H0Iso Y.X₃).hom (groupHomology.δ hX 1 0 rfl y) =
          Representation.Coinvariants.mk Y.X₃.ρ (Y.g.hom b) := by
  let z := groupHomology.δ hX 1 0 rfl y
  obtain ⟨a, ha⟩ := Representation.Coinvariants.mk_surjective Y.X₃.ρ
    ((groupHomology.H0Iso Y.X₃).hom z)
  have hz : (groupHomology.functor k G 0).map f z = 0 :=
    congrArg (fun j : groupHomology Z 1 ⟶ groupHomology P 0 => j.hom y)
      (groupHomology.mapShortComplex₁ hX (i := 1) (j := 0) rfl).zero
  have hc : Representation.Coinvariants.mk P.ρ (f.hom a) = 0 := by
    have hn := originalHomologyH0_coinvariant_naturality f z
    rw [hz, ← ha, Representation.Coinvariants.map_mk] at hn
    exact hn.symm.trans (groupHomology.H0Iso P).hom.hom.map_zero
  have hna : Y.X₃.ρ.norm a = 0 := by
    apply (Rep.mono_iff_injective f).mp hX.mono_f
    have hn := congrArg (originalCoinvariantNorm P) hc
    rw [originalCoinvariantNorm_mk, map_zero] at hn
    rw [originalCoefficientMorphism_norm, hn, map_zero]
  obtain ⟨b, hb⟩ := (Rep.epi_iff_surjective Y.g).mp hY.epi_g a
  have hnb : Y.g.hom (Y.X₂.ρ.norm b) = 0 := by
    rw [originalCoefficientMorphism_norm, hb, hna]
  have he := (Y.exact_map_iff_of_faithful (forget₂ (Rep k G) (ModuleCat k))).mpr hY.exact
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp he _ hnb
  change Y.f.hom x = Y.X₂.ρ.norm b at hx
  refine ⟨x, ?_, b, hx.symm, ?_⟩
  · intro s
    apply (Rep.mono_iff_injective Y.f).mp hY.mono_f
    rw [Rep.hom_comm_apply, hx, Representation.self_norm_apply]
  · exact ha.symm.trans (congrArg (Representation.Coinvariants.mk Y.X₃.ρ) hb.symm)

end
end Dubon2026
