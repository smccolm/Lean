import Dubon2026.SourceBinaryFlagExactSequence
import Dubon2026.SourceBinaryFlagQuotientHecke
import Dubon2026.SourceBinaryH1HeckeAlgebra

/-! Eigenvalue descent through one step of the actual residual binary coefficient flag.
DUB-17/18 -> residual modular Galois association -> residual weight/level
reduction -> descent from the original binary H1 eigenclass to a character
piece. Coefficient exactness, finite dimensionality, full Hecke commutativity
and functorial compatibility are all derived for the original flag.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup CategoryTheory
open scoped MatrixGroups

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n j : ℕ)

private local instance flagPrimeNeZero (ell : sourceBinaryHeckePrime Q) : NeZero ell.val :=
  ⟨ell.property.1.ne_zero⟩

/-- All original good-prime H1 Hecke operators on the actual residual flag step. -/
def sourceBinaryFlagHeckeOperators :
    sourceBinaryHeckePrime Q → Module.End F (groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n j)) :=
  fun ell => sourceBinaryFlagHeckeH1 F p Q hpQ n j ell.property.1

/-- All original good-prime H1 Hecke operators on the actual coefficient-quotient character. -/
def sourceBinaryFlagQuotientOperators :
    sourceBinaryHeckePrime Q →
      Module.End F (groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j)) :=
  fun ell => sourceBinaryFlagQuotientHeckeH1 F p Q hpQ n j ell.property.1

/-- At a nonterminal original flag step, a nonzero H1 eigensystem survives in
the actual character quotient or in the next original flag step, with exactly
the same prescribed good-prime eigenvalues. No cohomological exactness,
finiteness, commutativity or operator-compatibility premise is supplied. -/
theorem sourceBinaryFlag_eigen_step [NeZero Q] (hj : j ≤ n)
    (eigenvalues : sourceBinaryHeckePrime Q → F)
    (x : groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n j)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagHeckeOperators F p Q hpQ n j ell x = eigenvalues ell • x) :
    (∃ y : groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ n j),
      y ≠ 0 ∧ ∀ ell, sourceBinaryFlagQuotientOperators F p Q hpQ n j ell y =
        eigenvalues ell • y) ∨
    (∃ y : groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n (j + 1)),
      y ≠ 0 ∧ ∀ ell, sourceBinaryFlagHeckeOperators F p Q hpQ n (j + 1) ell y =
        eigenvalues ell • y) := by
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  letI : Module.Finite F (MvPolynomial.homogeneousSubmodule (Fin 2) F n) :=
    Module.Finite.of_basis (binaryHomogeneousMonomialBasis (R := F) n)
  letI : Module.Finite F (sourceBinaryFlagRep F p Q hpQ n (j + 1)) :=
    show Module.Finite F (sourceBinaryCoefficientFlag F n (j + 1)) from inferInstance
  letI : Module.Finite F (sourceBinaryFlagShortComplex F p Q hpQ n j).X₁ :=
    show Module.Finite F (sourceBinaryFlagRep F p Q hpQ n (j + 1)) from inferInstance
  apply sourceNativeH1_eigen_exact_step (sourceBinaryFlagShortComplex F p Q hpQ n j)
    (sourceBinaryFlagShortComplex_shortExact F p Q hpQ n j hj)
    (sourceBinaryFlagHeckeOperators F p Q hpQ n (j + 1))
    (sourceBinaryFlagHeckeOperators F p Q hpQ n j)
    (sourceBinaryFlagQuotientOperators F p Q hpQ n j) _ _ _ eigenvalues x hx heig
  · intro a b
    exact sourceBinaryFlagHeckeH1_commute F p Q hpQ n (j + 1)
      a.property.1 b.property.1 a.property.2 b.property.2
  · intro ell
    apply LinearMap.ext
    intro y
    exact sourcePrimeHeckeH1_naturality ell.property.1 _ _
      (sourceBinaryFlagInclusion F p Q hpQ n j) _ _ _ _
      (sourceBinaryFlagInclusion_diagonal F p Q hpQ n j ell.val) y
  · intro ell
    apply LinearMap.ext
    intro y
    exact sourcePrimeHeckeH1_naturality ell.property.1 _ _
      (sourceBinaryFlagQuotientMap F p Q hpQ n j) _ _ _ _
      (sourceBinaryFlagQuotientMap_diagonal F p Q hpQ n j ell.val) y

end
end Dubon2026
