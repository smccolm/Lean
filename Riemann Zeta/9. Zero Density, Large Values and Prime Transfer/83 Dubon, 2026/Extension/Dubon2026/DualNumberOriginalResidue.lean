import Dubon2026.SurjectiveLocalResidue
import Dubon2026.LocalCoefficientReduction
import Mathlib.RingTheory.DualNumber

/-! # The true original residue of the actual dual-number coefficient algebra -/

namespace Dubon2026

noncomputable section

/-- The actual first-coordinate algebra map induces the original dual-number residue-field equivalence. -/
def dualNumberOriginalResidueEquiv (K : Type*) [Field K] :
    IsLocalRing.ResidueField (DualNumber K) ≃ₐ[K] IsLocalRing.ResidueField K := by
  let f := TrivSqZeroExt.fstHom K K K
  have hf : Function.Surjective f := fun k => ⟨TrivSqZeroExt.inl k, rfl⟩
  letI : IsLocalHom f.toRingHom := IsLocalHom.of_surjective f.toRingHom hf
  exact surjectiveLocalResidueAlgEquiv f hf

/-- Genuine coefficient reduction agrees with the original first coordinate followed by the actual base-field residue map. -/
theorem dualNumberOriginalResidueEquiv_reduction (K : Type*) [Field K]
    (z : DualNumber K) :
    localCoefficientReduction (dualNumberOriginalResidueEquiv K) z =
      IsLocalRing.residue K z.fst := rfl

end
end Dubon2026
