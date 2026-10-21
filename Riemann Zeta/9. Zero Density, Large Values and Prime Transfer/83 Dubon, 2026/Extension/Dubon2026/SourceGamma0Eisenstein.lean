import Dubon2026.SourceTrivialCuspEvaluation
import Dubon2026.SourceCommutingPrescribedEigenvector
import Dubon2026.SourceIntegralCohomologyFinite

/-! The original nonzero Eisenstein eigensystem in full native H1.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> removal of the exact exceptional alternative. The genuine cusp
functional has value one and original Hecke eigenvalues ell+1. Existing
finite-dimensional H1 and prescribed common-eigenvector results now supply
the actual nonzero class, over every coefficient field and every level at least two.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped MatrixGroups

variable (F : Type) [Field F] (Q : ℕ)

/-- The full original good-prime Hecke actions on trivial-coefficient H1 commute. -/
theorem sourceTrivialCoefficientHeckeOperators_commute (a b : sourceBinaryHeckePrime Q) :
    Commute (sourceTrivialCoefficientHeckeOperators F Q a)
      (sourceTrivialCoefficientHeckeOperators F Q b) := by
  letI : NeZero a.val := ⟨a.property.1.ne_zero⟩
  letI : NeZero b.val := ⟨b.property.1.ne_zero⟩
  by_cases he : a.val = b.val
  · have hab : a = b := Subtype.ext he
    subst b
    exact Commute.refl _
  · exact sourcePrimeHeckeH1_commute a.property.1 (Rep.trivial F (Gamma0 Q) F)
      LinearMap.id (sourceTrivialCoefficient_intertwine F Q a.property.1)
      b.property.1 a.property.2 b.property.2 he LinearMap.id
      (sourceTrivialCoefficient_intertwine F Q b.property.1) rfl

/-- At every actual level at least two, full native trivial-coefficient H1
has a nonzero common eigenclass with the exact Eisenstein eigenvalues ell+1.
No nonzero class, cusp functional, finite-dimensionality or Hecke eigenvalue is assumed. -/
theorem sourceGamma0_exists_Eisenstein_eigenclass (hQ : 2 ≤ Q) :
    ∃ x : H1 (Rep.trivial F (Gamma0 Q) F), x ≠ 0 ∧
      ∀ ell : sourceBinaryHeckePrime Q,
        sourceTrivialCoefficientHeckeOperators F Q ell x = ((ell.val : F) + 1) • x := by
  letI : NeZero Q := ⟨by omega⟩
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  letI : Module.Finite F (H1 (Rep.trivial F (Gamma0 Q) F)) :=
    sourceH1Finite (Rep.trivial F (Gamma0 Q) F)
  apply sourceCommutingOperators_exists_prescribedEigenvector
    (sourceTrivialCoefficientHeckeOperators F Q)
    (sourceTrivialCoefficientHeckeOperators_commute F Q)
    (fun ell => (ell.val : F) + 1) (LinearMap.ker (sourceTrivialCuspEvaluation F Q))
  · intro htop
    obtain ⟨x, hx⟩ := sourceTrivialCuspEvaluation_one F Q hQ
    have hm : x ∈ LinearMap.ker (sourceTrivialCuspEvaluation F Q) := by
      rw [htop]
      trivial
    exact one_ne_zero (hx.symm.trans hm)
  · intro ell x
    rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul,
      sourceTrivialCuspEvaluation_hecke, sub_self]

end
end Dubon2026
