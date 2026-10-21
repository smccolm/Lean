import Dubon2026.SourceThreeAffinePrimitive
import Dubon2026.SourceHeckeEigenvectorLift
import Dubon2026.SourceIntegralCohomologyFinite

/-! The nonzero-image case of the original characteristic-three odd twist.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction -> characteristic-three odd twist. The actual cup primitive
and coefficient difference feed the existing prescribed-eigenvector theorem.
Native H1 finiteness and full-Hecke commutativity are derived here.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

variable (F : Type) [Field F] [CharP F 3] (Q : ℕ) [NeZero Q] (h3Q : 3 ∣ Q)

/-- If actual constant inclusion preserves the nonzero class, the original
affine-function H1 has a nonzero eigenclass with the exact prime twist. -/
theorem sourceThreeFunction_exists_twistedEigenclass
    (values : sourceBinaryHeckePrime Q → F)
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F))
    (hconst : sourceThreeConstantH1 F Q h3Q (H1π _ z) ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell (H1π _ z) =
      values ell • H1π _ z) :
    ∃ y : H1 (sourceAffineFunctionRep 3 Q F h3Q), y ≠ 0 ∧
      ∀ ell, sourceAffineFunctionHeckeOperators F 3 Q h3Q ell y =
        ((ell.val : F) * values ell) • y := by
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  letI : Module.Finite F (sourceAffineFunctionRep 3 Q F h3Q) :=
    show Module.Finite F (ZMod 3 → F) from inferInstance
  letI : Module.Finite F (H1 (sourceAffineFunctionRep 3 Q F h3Q)) :=
    sourceH1Finite (sourceAffineFunctionRep 3 Q F h3Q)
  let T := sourceAffineFunctionHeckeOperators F 3 Q h3Q
  let U : sourceBinaryHeckePrime Q →
      Module.End F (H1 (sourceAffineFunctionRep 3 Q F h3Q)) :=
    fun ell => (ell.val : F) • T ell
  apply sourceHeckeEigenvector_exists_in_source T U
    (sourceAffineFunctionHeckeOperators_commute F 3 Q h3Q)
    (sourceThreeFunctionDifferenceH1 F Q h3Q) _
    (fun ell => (ell.val : F) * values ell)
    (sourceThreeConstantH1 F Q h3Q (H1π _ z)) hconst _ _
  · intro ell
    apply LinearMap.ext
    intro x
    exact sourceThreeFunctionDifferenceH1_hecke F Q h3Q ell x
  · intro ell
    change (ell.val : F) •
      sourceAffineFunctionHeckeOperators F 3 Q h3Q ell
        (sourceThreeConstantH1 F Q h3Q (H1π _ z)) = _
    rw [← sourceThreeConstantH1_hecke, heig, map_smul, smul_smul]
  · exact sourceThreeConstantH1_difference_range F Q h3Q z

end
end Dubon2026
