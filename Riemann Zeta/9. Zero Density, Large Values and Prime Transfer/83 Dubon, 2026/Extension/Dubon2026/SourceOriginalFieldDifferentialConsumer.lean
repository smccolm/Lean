import Dubon2026.SourceOriginalFieldFinite
import Mathlib.RingTheory.Etale.Field

/-! DUB-17/18 -> original cusp-form lower dimension bound -> regular
differential realization -> injectivity of the actual differential expansion
-> separability over the actual j coordinate. The conditional consumer here uses
monic relations for divisor j series and derives finite extension.
SourceAllDivisorMonicRelations proves those relations and
SourceOriginalDifferentialInjectivity assembles the original-field result. Exact polynomial degree and irreducibility
are unnecessary for this finite-extension step.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero.lean.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField Polynomial


variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem diffQExp_original_injective_of_monic_relations
    (hrelations : ∀ (d : ℕ) [NeZero d], d ∣ N →
      ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧
        P.eval₂ evalAtJ (qExpand ℚ d jq) = 0) :
    Function.Injective (SourceDifferential.diffQExp (modularFunctionFieldOver N L)) := by
  let K := IntermediateField.adjoin L ({jOver N L} : Set (modularFunctionFieldOver N L))
  letI : Algebra L (modularFunctionFieldOver N L) := inferInstance
  letI : Algebra L K := inferInstance
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap L K).injective
  haveI : FiniteDimensional K (modularFunctionFieldOver N L) :=
    finiteDimensional_original_of_monic_relations L N hrelations
  haveI : Algebra.IsSeparable K (modularFunctionFieldOver N L) := inferInstance
  exact diffQExp_original_injective_of_separable N L

end
end Dubon2026.SourceFunctionField
