import Dubon2026.CompleteLocalFiniteResidueNorm
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Original unit norms for finite free unramified algebras over complete local rings -/

namespace Dubon2026
noncomputable section

open IsLocalRing

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [IsAdicComplete (maximalIdeal R) R] [Finite (R ⧸ maximalIdeal R)]

/-- The original finite free unramified local algebra has surjective unit
norm over the complete local base with finite residue field. Pinned actual
unramified local-ring theory proves that its original special fiber is a
field, and the actual finite-field and Newton proofs supply unit preimages. -/
theorem unramifiedCompleteLocal_unit_norm_surjective :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) := by
  letI : (Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal := by
    rw [Algebra.FormallyUnramified.map_maximalIdeal]
    infer_instance
  exact completeLocalFiniteResidue_unit_norm_surjective

end
end Dubon2026
