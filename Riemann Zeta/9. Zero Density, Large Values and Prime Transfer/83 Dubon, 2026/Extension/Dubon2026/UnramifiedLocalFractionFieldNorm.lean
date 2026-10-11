import Dubon2026.UnramifiedCompleteLocalUnitNorm
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Algebraic.Integral

/-! # Actual unramified local ring-unit norm preimages retain their original field norms -/

namespace Dubon2026
noncomputable section

open IsLocalRing
open scoped nonZeroDivisors

variable {R S K L : Type} [CommRing R] [CommRing S] [IsDomain S]
  [Field K] [Field L] [Algebra R S] [FaithfulSMul R S]
  [Algebra R K] [Algebra S L] [Algebra K L] [Algebra R L]
  [IsFractionRing R K] [IsFractionRing S L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Free R S] [Module.Finite R S] [Algebra.FormallyUnramified R S]
  [IsAdicComplete (maximalIdeal R) R] [Finite (R ⧸ maximalIdeal R)]

/-- The actual unramified complete local ring-unit preimage maps to a
genuine original fraction-field norm preimage. Pinned localization proves
the norm comparison; no field-norm compatibility is assumed as a certificate. -/
theorem unramifiedLocal_exists_fraction_field_unit_norm (u : Rˣ) :
    ∃ v : Sˣ,
      Units.map (Algebra.norm K (S := L)) (Units.map (algebraMap S L).toMonoidHom v) =
        Units.map (algebraMap R K).toMonoidHom u := by
  obtain ⟨v, hv⟩ := unramifiedCompleteLocal_unit_norm_surjective (R := R) (S := S) u
  refine ⟨v, ?_⟩
  apply Units.ext
  change Algebra.norm K (algebraMap S L v.val) = algebraMap R K u.val
  rw [Algebra.norm_localization R R⁰]
  exact congrArg (algebraMap R K) (congrArg Units.val hv)

end
end Dubon2026
