import Dubon2026.OriginalInertiaValuation
import Dubon2026.OriginalAdicDecompositionAction

/-! # Actual inertia is normal in the original decomposition group

The height-one prime stabilizer agrees with the stabilizer of its
literal ideal. Pinned ideal inertia normality therefore applies to the
original group used by the completion norm comparison in DUB-17.
-/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField Pointwise
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (w : HeightOneSpectrum (𝓞 L))

omit [NumberField L] in
/-- The original prime decomposition group is the literal ideal
stabilizer under the same Galois automorphisms. -/
theorem originalFiniteDecompositionGroup_eq_ideal_stabilizer :
    OriginalFiniteDecompositionGroup K L w = MulAction.stabilizer Gal(L/K) w.asIdeal := by
  ext σ
  change numberFieldGaloisPlaceEquiv K L σ w = w ↔ σ • w.asIdeal = w.asIdeal
  have he : (numberFieldGaloisPlaceEquiv K L σ w).asIdeal = σ • w.asIdeal := by
    rw [numberFieldGaloisPlaceEquiv_asIdeal, Ideal.pointwise_smul_def]
    rfl
  constructor
  · intro h
    rw [← he, h]
  · intro h
    apply HeightOneSpectrum.ext
    exact he.trans h

omit [NumberField L] in
/-- Actual ideal inertia, restricted to the original decomposition
group, is normal. -/
theorem originalDecompositionInertia_normal :
    ((w.asIdeal.inertia Gal(L/K)).comap
      (OriginalFiniteDecompositionGroup K L w).subtype).Normal := by
  change ((w.asIdeal.inertia Gal(L/K)).subgroupOf
    (OriginalFiniteDecompositionGroup K L w)).Normal
  rw [originalFiniteDecompositionGroup_eq_ideal_stabilizer]
  infer_instance

end
end Dubon2026
