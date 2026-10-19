import Dubon2026.OriginalCoefficientFramedEquivalence

/-! The concrete two-map argument for the original-support ring
comparison. Matrix evaluation and the proved coefficient-map rigidity
force the two constructed algebra maps to be inverse. -/

namespace Dubon2026
noncomputable section
open Matrix IsLocalRing

/-- Residue-preserving maps that identify the actual universal
matrices are inverse once those matrices distinguish coefficient
endomorphisms. The arithmetic applications derive this rigidity from
their existing framed classifications. -/
def residueMatrixCoefficientEquiv
    {ι G O R S : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing O] [IsLocalRing O]
    [CommRing R] [IsLocalRing R] [Algebra O R]
    [CommRing S] [IsLocalRing S] [Algebra O S]
    (eR : ResidueField R ≃ₐ[O] ResidueField O)
    (eS : ResidueField S ≃ₐ[O] ResidueField O)
    (τR : G → GeneralLinearGroup ι R) (τS : G → GeneralLinearGroup ι S)
    (f : S →ₐ[O] R) (g : R →ₐ[O] S)
    (hfres : (localCoefficientReduction eR).comp f = localCoefficientReduction eS)
    (hgres : (localCoefficientReduction eS).comp g = localCoefficientReduction eR)
    (hf : ∀ x, GeneralLinearGroup.map f.toRingHom (τS x) = τR x)
    (hg : ∀ x, GeneralLinearGroup.map g.toRingHom (τR x) = τS x)
    (hR : ∀ (u : R →ₐ[O] R),
      (localCoefficientReduction eR).comp u = localCoefficientReduction eR →
      (∀ x, GeneralLinearGroup.map u.toRingHom (τR x) = τR x) → u = AlgHom.id O R)
    (hS : ∀ (u : S →ₐ[O] S),
      (localCoefficientReduction eS).comp u = localCoefficientReduction eS →
      (∀ x, GeneralLinearGroup.map u.toRingHom (τS x) = τS x) → u = AlgHom.id O S) :
    S ≃ₐ[O] R := by
  apply AlgEquiv.ofAlgHom f g
  · apply hR
    · rw [← AlgHom.comp_assoc, hfres, hgres]
    · intro x
      change GeneralLinearGroup.map (f.toRingHom.comp g.toRingHom) (τR x) = _
      rw [GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hg, hf]
  · apply hS
    · rw [← AlgHom.comp_assoc, hgres, hfres]
    · intro x
      change GeneralLinearGroup.map (g.toRingHom.comp f.toRingHom) (τS x) = _
      rw [GeneralLinearGroup.map_comp, MonoidHom.comp_apply, hf, hg]

end
end Dubon2026
