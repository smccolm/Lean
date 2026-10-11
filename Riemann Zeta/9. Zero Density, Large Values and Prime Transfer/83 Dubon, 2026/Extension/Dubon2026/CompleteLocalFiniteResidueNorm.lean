import Dubon2026.AdicCompleteUnitNormLifting
import Dubon2026.LocalRingNormReduction
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic

/-! # Actual unit norm surjectivity with finite field special fiber over a complete local base -/

namespace Dubon2026
noncomputable section

open IsLocalRing

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [Module.Free R S] [Module.Finite R S]
  [IsAdicComplete (maximalIdeal R) R]
  [Finite (R ⧸ maximalIdeal R)]
  [(Ideal.map (algebraMap R S) (maximalIdeal R)).IsMaximal]

attribute [local instance] Ideal.Quotient.field

/-- If the actual special fiber is a finite field, the actual complete
finite-free local algebra unit norm is surjective. Finite-field trace and
norm surjectivity discharge both residual conditions of the genuine Newton
lift. The special-fiber maximality is explicit; it must be proved for each
intended unramified extension before this theorem is applied there. -/
theorem completeLocalFiniteResidue_unit_norm_surjective :
    Function.Surjective (Units.map (Algebra.norm R (S := S))) := by
  classical
  let p := maximalIdeal R
  let q := Ideal.map (algebraMap R S) p
  let b := Module.Free.chooseBasis R S
  letI : Module.Finite (R ⧸ p) (S ⧸ q) :=
    Module.Finite.of_basis (basisQuotient b)
  letI : Finite (S ⧸ q) := Module.finite_of_finite (R ⧸ p)
  obtain ⟨x₀, hx₀⟩ := Algebra.trace_surjective (R ⧸ p) (S ⧸ q) 1
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x₀
  have hx : IsUnit (Ideal.Quotient.mk p (Algebra.trace R S x)) := by
    rw [← Algebra.trace_quotient_mk, hx₀]
    exact isUnit_one
  apply adicComplete_unit_norm_surjective b p x hx
  intro u
  obtain ⟨a₀, ha₀⟩ := FiniteField.unitsMap_norm_surjective (R ⧸ p) (S ⧸ q)
    (Units.map (Ideal.Quotient.mk p).toMonoidHom u)
  have hlocal : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  obtain ⟨a, rfl⟩ := surjective_units_map_of_local_ringHom (Ideal.Quotient.mk q)
    Ideal.Quotient.mk_surjective hlocal a₀
  refine ⟨a, ?_⟩
  rw [← localRingNorm_quotient_mk]
  exact congrArg Units.val ha₀

end
end Dubon2026
