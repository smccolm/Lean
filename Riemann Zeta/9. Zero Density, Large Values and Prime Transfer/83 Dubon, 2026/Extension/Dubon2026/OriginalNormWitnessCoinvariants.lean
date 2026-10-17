import Dubon2026.OriginalNormHomologyBoundary

/-! # Norm witnesses detected by the actual projected coinvariant

For DUB-17's converse criterion, the fundamental coefficient supplies a
lift whose norm is the included original morphism. This lemma proves
that the projected coinvariant vanishes exactly when the original
morphism is itself a norm. It is the detection step preceding the
remaining fundamental-class pairing comparison.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

/-- In an actual short exact coefficient sequence with injective middle coinvariant norm, a chosen middle norm lift detects exactly whether the original coefficient is a norm. -/
theorem originalNormWitness_iff_projectedCoinvariant_zero
    {k G : Type} [CommRing k] [Group G] [Fintype G]
    {X : ShortComplex (Rep.{0} k G)} (hX : X.ShortExact)
    (hmid : OriginalNormCoinvariantInjective X.X₂)
    (x : X.X₁) (y : X.X₂) (hy : X.X₂.ρ.norm y = X.f.hom x) :
    (∃ t : X.X₁, X.X₁.ρ.norm t = x) ↔
      Representation.Coinvariants.mk X.X₃.ρ (X.g.hom y) = 0 := by
  constructor
  · rintro ⟨t, ht⟩
    have hd : X.X₂.ρ.norm (y - X.f.hom t) = 0 := by
      rw [map_sub, ← originalCoefficientMorphism_norm, ht, hy, sub_self]
    have hc := congrArg (Representation.Coinvariants.map X.X₂.ρ X.X₃.ρ X.g.hom)
      (hmid _ hd)
    rw [Representation.Coinvariants.map_mk, map_zero] at hc
    have hz : X.g.hom (X.f.hom t) = 0 :=
      congrArg (fun f : X.X₁ ⟶ X.X₃ => f.hom t) X.zero
    simpa only [map_sub, hz, sub_zero] using hc
  · intro hc
    have hg : Representation.Coinvariants.map X.X₂.ρ X.X₃.ρ X.g.hom
        (Representation.Coinvariants.mk X.X₂.ρ y) = 0 := by
      rw [Representation.Coinvariants.map_mk, hc]
    obtain ⟨a, ha⟩ := originalCoinvariant_exact_lift hX
      (Representation.Coinvariants.mk X.X₂.ρ y) hg
    obtain ⟨t, rfl⟩ := Representation.Coinvariants.mk_surjective X.X₁.ρ a
    rw [Representation.Coinvariants.map_mk] at ha
    have hn := congrArg (originalCoinvariantNorm X.X₂) ha
    rw [originalCoinvariantNorm_mk, originalCoinvariantNorm_mk] at hn
    refine ⟨t, (Rep.mono_iff_injective X.f).mp hX.mono_f ?_⟩
    calc
      X.f.hom (X.X₁.ρ.norm t) = X.X₂.ρ.norm (X.f.hom t) :=
        originalCoefficientMorphism_norm X.f t
      _ = X.X₂.ρ.norm y := hn
      _ = X.f.hom x := hy

end
end Dubon2026
