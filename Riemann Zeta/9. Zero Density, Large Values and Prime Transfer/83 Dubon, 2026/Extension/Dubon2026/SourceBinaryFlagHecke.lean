import Dubon2026.SourceBinaryFlagAction
import Dubon2026.SourcePrimeCoefficientHeckeH1
import Mathlib.RepresentationTheory.Subrepresentation

/-! Actual residual coefficient-flag representations and their full Hecke actions.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> native H1 eigenvalue descent through the binary coefficient flag. The
existing Mathlib subrepresentation, native H1 finiteness and original
product-correspondence theorem discharge the structural prerequisites.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

variable (F : Type) [Field F] (p Q : ℕ) [CharP F p] (hpQ : p ∣ Q) (n j : ℕ)

/-- The actual j-th residual coefficient step is a native subrepresentation
of the original binary polynomial representation. -/
def sourceBinaryFlagSubrepresentation :
    Subrepresentation (sourceBinaryCoefficientRep F Q n).ρ where
  toSubmodule := sourceBinaryCoefficientFlag F n j
  apply_mem_toSubmodule g _ hv := sourceBinaryFlag_group_stable F p Q hpQ n j g _ hv

/-- The actual residual coefficient-flag representation. -/
def sourceBinaryFlagRep : Rep F (Gamma0 Q) :=
  Rep.of (sourceBinaryFlagSubrepresentation F p Q hpQ n j).toRepresentation

/-- The original Hecke diagonal restricted to the actual residual coefficient step. -/
def sourceBinaryFlagDiagonal (ell : ℕ) :
    Module.End F (sourceBinaryCoefficientFlag F n j) :=
  (homogeneousMatrixAction n (Matrix.diagonal ![(ell : F), 1])).restrict
    (sourceBinaryFlag_hecke_stable F n j ell)

/-- The original Hecke diagonal intertwines the actual flag group action
with the original prime subgroup conjugation. -/
theorem sourceBinaryFlagDiagonal_intertwine {ell : ℕ} [NeZero ell] (hell : ell.Prime)
    (u : heckeUpperSubgroup Q ell) :
    (sourceBinaryFlagDiagonal F n j ell).comp
        ((sourceBinaryFlagRep F p Q hpQ n j).ρ (sourceHeckeConjugation hell u)) =
      ((sourceBinaryFlagRep F p Q hpQ n j).ρ u.val).comp (sourceBinaryFlagDiagonal F n j ell) := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact LinearMap.congr_fun (sourceBinaryHeckeDiagonal_intertwine F hell n u) P.val

/-- The full genuine prime correspondence on native H1 of the original residual coefficient step. -/
def sourceBinaryFlagHeckeH1 {ell : ℕ} [NeZero ell] (hell : ell.Prime) :
    Module.End F (groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n j)) :=
  sourcePrimeHeckeH1 hell (sourceBinaryFlagRep F p Q hpQ n j)
    (sourceBinaryFlagDiagonal F n j ell) (sourceBinaryFlagDiagonal_intertwine F p Q hpQ n j hell)

/-- The actual restricted coefficient diagonals commute on each original flag step. -/
theorem sourceBinaryFlagDiagonal_commute (a b : ℕ) :
    (sourceBinaryFlagDiagonal F n j a).comp (sourceBinaryFlagDiagonal F n j b) =
      (sourceBinaryFlagDiagonal F n j b).comp (sourceBinaryFlagDiagonal F n j a) := by
  have h := (Matrix.commute_diagonal ![(a : F), 1] ![(b : F), 1]).map
    (homogeneousMatrixRepresentation (R := F) n)
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  exact LinearMap.congr_fun h.eq P.val

/-- All actual good-prime H1 Hecke operators on every original residual flag
step commute; no flag-level commutativity assumption is supplied. -/
theorem sourceBinaryFlagHeckeH1_commute {a b : ℕ} [NeZero a] [NeZero b]
    (ha : a.Prime) (hb : b.Prime) (haQ : Nat.Coprime a Q) (hbQ : Nat.Coprime b Q) :
    Commute (sourceBinaryFlagHeckeH1 F p Q hpQ n j ha)
      (sourceBinaryFlagHeckeH1 F p Q hpQ n j hb) := by
  by_cases he : a = b
  · subst b
    exact Commute.refl _
  · exact sourcePrimeHeckeH1_commute ha (sourceBinaryFlagRep F p Q hpQ n j)
      (sourceBinaryFlagDiagonal F n j a) (sourceBinaryFlagDiagonal_intertwine F p Q hpQ n j ha)
      hb haQ hbQ he (sourceBinaryFlagDiagonal F n j b)
      (sourceBinaryFlagDiagonal_intertwine F p Q hpQ n j hb)
      (sourceBinaryFlagDiagonal_commute F n j a b)

/-- Every actual residual coefficient-flag H1 is finite dimensional; the
original congruence-group generators and finite homogeneous basis provide
all finiteness inputs. -/
theorem sourceBinaryFlagH1_finite [NeZero Q] :
    Module.Finite F (groupCohomology.H1 (sourceBinaryFlagRep F p Q hpQ n j)) := by
  letI : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T},
      SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  letI : Module.Finite F (MvPolynomial.homogeneousSubmodule (Fin 2) F n) :=
    Module.Finite.of_basis (binaryHomogeneousMonomialBasis (R := F) n)
  letI : Module.Finite F (sourceBinaryFlagRep F p Q hpQ n j) :=
    show Module.Finite F (sourceBinaryCoefficientFlag F n j) from inferInstance
  exact sourceH1Finite (sourceBinaryFlagRep F p Q hpQ n j)

end
end Dubon2026
