import Dubon2026.SourceThreeConstantKernel
import Dubon2026.SourceThreeEigenLift
import Dubon2026.SourceRaisedLevelEigensystem

/-! The original weight-two odd twist in characteristic three.
DUB-17/18 -> residual modular Galois association -> all-prime weight-two
reduction. Constant inclusion either kills the original class, where the
proved cusp functional supplies the same-level twist, or the actual cup
primitive and eigenvector theorem supply a nonzero full-function class.
The proved raised-level evaluation then gives actual trivial coefficients.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] [CharP F 3] (Q : ℕ) [NeZero Q] (h3Q : 3 ∣ Q)

include h3Q in
/-- Every actual nonzero weight-two eigensystem in characteristic three
has its exact good-prime twist at an original level between Q and 3*Q.
No cup primitive, nonzero lift, Hecke comparison or finite-dimensionality
is assumed. -/
theorem sourceThreeWeightTwo_twist
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (Rep.trivial F (Gamma0 Q) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell x = values ell • x) :
    ∃ (M : ℕ) (hQM : Q ∣ M), M ∣ Q * 3 ∧
      ∃ y : H1 (Rep.trivial F (Gamma0 M) F), y ≠ 0 ∧
        ∀ ell : sourceBinaryHeckePrime M,
          sourceTrivialCoefficientHeckeOperators F M ell y =
            ((ell.val : F) * values (sourceBinaryGoodPrimeOfLevel hQM ell)) • y := by
  induction x using H1_induction_on with
  | h z =>
    by_cases hker : sourceThreeConstantH1 F Q h3Q (H1π _ z) = 0
    · refine ⟨Q, dvd_refl Q, dvd_mul_right Q 3, H1π _ z, hx, ?_⟩
      exact sourceThreeCocycle_twist_of_kernel F Q h3Q values z hx heig hker
    · obtain ⟨w, hw, hew⟩ :=
        sourceThreeFunction_exists_twistedEigenclass F Q h3Q values z hker heig
      obtain ⟨y, hy, hey⟩ := sourceAffineFunction_raiseLevel F 3 Q h3Q
        (fun ell => (ell.val : F) * values ell) w hw hew
      exact ⟨Q * 3, dvd_mul_right Q 3, dvd_refl _, y, hy, hey⟩

end
end Dubon2026
