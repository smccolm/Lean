import Dubon2026.SourceAffineFlagHeckeQuotient
import Dubon2026.SourceGamma0H1Surjection

/-! An actual character H1 eigensystem lifts to the original finite-function flag.
DUB-17/18 -> residual modular Galois association -> character-to-weight-two
reduction -> this native coefficient lift -> survival in the whole function
representation and evaluation at the raised level. The actual Gamma0 H2
vanishing, finite flag, original coefficient surjection and full commuting
Hecke comparisons discharge all lifting prerequisites.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable (F : Type) [Field F] (p Q : ℕ) [Fact p.Prime] [CharP F p] [NeZero Q]
    (hpQ : p ∣ Q) (j : Fin p)

/-- Every actual nonzero character eigenclass lifts to a nonzero eigenclass in
the original affine function flag, with its exact inverse-prime eigenvalue
twist. No cohomological surjectivity, finite H1, commuting operators or
nonzero lifted class is assumed. -/
theorem sourceAffineFlag_exists_characterEigenlift (h6 : (6 : F) ≠ 0)
    (values : sourceBinaryHeckePrime Q → F)
    (x : groupCohomology.H1 (sourceBinaryFlagQuotientRep F p Q hpQ (2 * j.val) 0))
    (hx : x ≠ 0)
    (heig : ∀ ell, sourceBinaryFlagUntwistedOperators F p Q hpQ (2 * j.val) 0 ell x =
      values ell • x) :
    ∃ y : groupCohomology.H1 (sourceAffineFlagRep F p Q hpQ j), y ≠ 0 ∧
      ∀ ell, sourceAffineFlagHeckeOperators F p Q hpQ j ell y =
        (sourceAffineFlagHeckeScalar F p j ell.val * values ell) • y := by
  letI : Module.Finite F (sourceAffineFlagRep F p Q hpQ j) :=
    show Module.Finite F (sourceFiniteFunctionFlag F p j.val) from inferInstance
  apply sourceGamma0H1_eigen_lift Q h6
    (sourceAffineFlagQuotientMap F p Q hpQ j)
    (sourceAffineFlagQuotientMap_surjective F p Q hpQ j)
    (sourceAffineFlagHeckeOperators F p Q hpQ j)
    (sourceAffineFlagCharacterOperators F p Q hpQ j)
    (sourceAffineFlagHeckeOperators_commute F p Q hpQ j)
    (sourceAffineFlagQuotientMap_hecke F p Q hpQ j)
    (fun ell => sourceAffineFlagHeckeScalar F p j ell.val * values ell) x hx
  intro ell
  change sourceAffineFlagHeckeScalar F p j ell.val •
    sourceBinaryFlagUntwistedOperators F p Q hpQ (2 * j.val) 0 ell x = _
  rw [heig, smul_smul]

end
end Dubon2026
