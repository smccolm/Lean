import Dubon2026.SourceWeightTwoReflectionHecke
import Dubon2026.SourceOriginalPeriodSurjectivity

/-! DUB-17/18 -> actual parabolic Hecke eigensystem realization.
Both parts of the already proved original period isomorphism intertwine
the genuine good-prime Hecke operators, with their exact normalization.
-/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

theorem sourceWeightTwoPeriodPair_hecke (N : ℕ) [NeZero N]
    (ell : sourceBinaryHeckePrime N) (f g : CuspForm (Gamma0 N) 2) :
    sourceWeightTwoPeriodPair N (cuspHeckeLinear N 2 ell.val f, cuspHeckeLinear N 2 ell.val g) =
      sourceWeightTwoHeckeHom N ell (sourceWeightTwoPeriodPair N (f, g)) := by
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  rw [cuspHeckeLinear_prime N 2 ell.property.1]
  change sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property.1 f) +
    sourceWeightTwoPeriodReflection N (sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property.1 f)) +
    sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property.1 g) -
    sourceWeightTwoPeriodReflection N (sourceWeightTwoPeriodHom (Gamma0 N) (cuspHeckePrime ell.property.1 g)) = _
  simp only [sourceWeightTwoPeriodHom_hecke, sourceWeightTwoPeriodReflection_hecke]
  rw [← map_add, ← map_add, ← map_sub]
  rfl

end
end Dubon2026
