import Dubon2026.SourcePerfectSeparatingCoordinate
import Dubon2026.SourceModularCoordinateNotPower
import Dubon2026.SourceModularCoefficientFieldFinite

/-! DUB-17/18 -> original Frobenius/inertia -> residue curve differentials ->
separating finite coordinate. Every positive-characteristic premise of the
no-pth-root criterion is discharged for the actual divisor-generated field;
characteristic zero uses native separability. Perfectness of constants is
the usual residue-curve hypothesis, not a separability assumption on the
function field. Exact degree and good reduction remain separate. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem isSeparable_coeff_field (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [PerfectField K] :
    Algebra.IsSeparable (IntermediateField.adjoin K ({jCoeff N K} :
      Set (modularFunctionFieldCoeff N K))) (modularFunctionFieldCoeff N K) := by
  let F := modularFunctionFieldCoeff N K
  letI : Algebra K F := inferInstance
  let J := IntermediateField.adjoin K ({jCoeff N K} : Set F)
  letI : Algebra K J := inferInstance
  haveI : FiniteDimensional J F := finiteDimensional_coeff_field N K
  haveI : Algebra.IsIntegral J F := Algebra.IsIntegral.of_finite J F
  change Algebra.IsSeparable J F
  obtain ⟨p, hp⟩ := CharP.exists K
  rcases CharP.char_is_prime_or_zero K p with hprime | rfl
  · haveI : Fact p.Prime := ⟨hprime⟩
    haveI : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
    haveI : PerfectRing K p := PerfectField.toPerfectRing p
    refine ⟨fun y => ?_⟩
    exact SourceCurve.isSeparable_of_forall_pow_ne p
      (pow_ne_jCoeff N K p hprime.two_le) (Algebra.IsIntegral.isIntegral (R := J) y)
  · haveI : CharZero K := CharP.charP_to_charZero K
    haveI : CharZero J := charZero_of_injective_algebraMap (algebraMap K J).injective
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField

end
end Dubon2026.SourceFunctionField
