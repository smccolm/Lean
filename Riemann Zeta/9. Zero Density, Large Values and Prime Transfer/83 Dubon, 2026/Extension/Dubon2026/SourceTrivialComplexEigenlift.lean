import Dubon2026.SourceTrivialComplexHeckeAction
import Dubon2026.SourceTrivialResidualHeckeCharacter
import Dubon2026.SourceIntegralResidualEigencharacter

/-! DUB-17/18 -> residual Galois association -> the actual characteristic-zero
weight-two cohomology input. The original residual eigensystem constructs its
integral Hecke character; the proved faithful action on the same full complex
H1 then supplies a nonzero eigenclass with integral eigenvalues and an exact
reduction map. No complex eigenclass or compatibility certificate is assumed.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology
open scoped IsMulCommutative

/-- A character of the original integral Hecke algebra lifts to a nonzero
class in the original full complex H1, with integral prime eigenvalues and
their prescribed simultaneous reduction. -/
theorem sourceTrivialHeckeCharacter_exists_complexEigenlift
    (F : Type) [Field F] [IsAlgClosed F] (Q : ℕ) [NeZero Q]
    (r : sourceTrivialHeckeAlgebra Q →ₐ[ℤ] F)
    (values : sourceBinaryHeckePrime Q → F)
    (hr : ∀ ell : sourceBinaryHeckePrime Q,
      r ⟨sourceTrivialRingHeckeOperators ℤ Q ell, Algebra.subset_adjoin ⟨ell, rfl⟩⟩ =
        values ell) :
    ∃ (θ : sourceBinaryHeckePrime Q → integralClosure ℤ ℂ)
      (φ : integralClosure ℤ ℂ →+* F)
      (y : H1 (Rep.trivial ℂ (Gamma0 Q) ℂ)),
      y ≠ 0 ∧
      (∀ ell, sourceTrivialCoefficientHeckeOperators ℂ Q ell y = (θ ell : ℂ) • y) ∧
      ∀ ell, φ (θ ell) = values ell := by
  let T := sourceTrivialHeckeAlgebra Q
  let V := H1 (Rep.trivial ℂ (Gamma0 Q) ℂ)
  letI : IsMulCommutative T := sourceTrivialHeckeAlgebra_commutative Q
  letI : Module.Finite ℤ T := sourceTrivialHeckeAlgebra_finite Q
  letI : FiniteDimensional ℂ V := sourceTrivialH1_finite ℂ Q
  letI : Module T V := Module.compHom V (sourceTrivialComplexHeckeAction Q)
  letI : SMulCommClass T ℂ V := ⟨fun t c v =>
    (sourceTrivialComplexHeckeAction Q t).map_smul c v⟩
  letI : FaithfulSMul T V := ⟨fun {t u} h =>
    sourceTrivialComplexHeckeAction_injective Q (LinearMap.ext h)⟩
  obtain ⟨χ, φ, y, hy, heig, hφ⟩ :=
    sourceIntegralFaithfulAction_exists_residualEigencharacter (V := V) r.toRingHom
  let t (ell : sourceBinaryHeckePrime Q) : T :=
    ⟨sourceTrivialRingHeckeOperators ℤ Q ell, Algebra.subset_adjoin ⟨ell, rfl⟩⟩
  have ht (ell : sourceBinaryHeckePrime Q) :
      sourceTrivialComplexHeckeAction Q (t ell) =
        sourceTrivialCoefficientHeckeOperators ℂ Q ell := by
    have hw : sourceTrivialIntegralHeckeWord Q (FreeAlgebra.ι ℤ ell) = t ell := by
      apply Subtype.ext
      rw [sourceTrivialIntegralHeckeWord_coe, FreeAlgebra.lift_ι_apply]
    rw [← hw, sourceTrivialComplexHeckeAction_word, FreeAlgebra.lift_ι_apply]
    rfl
  refine ⟨fun ell => χ (t ell), φ, y, hy, ?_, ?_⟩
  · intro ell
    have h := heig (t ell)
    change sourceTrivialComplexHeckeAction Q (t ell) y = _ at h
    rwa [ht] at h
  · intro ell
    exact (RingHom.congr_fun hφ (t ell)).trans (hr ell)

/-- Every original nonzero residual weight-two eigensystem either has an
actual complex lift with integral eigenvalues and exact reduction, or has
the exact Eisenstein eigenvalues at all original good primes. -/
theorem sourceTrivialH1Eigen_complexLift_or_eisenstein
    (F : Type) [Field F] [IsAlgClosed F] (Q : ℕ) [NeZero Q]
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (Rep.trivial F (Gamma0 Q) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell x = values ell • x) :
    (∃ (θ : sourceBinaryHeckePrime Q → integralClosure ℤ ℂ)
      (φ : integralClosure ℤ ℂ →+* F)
      (y : H1 (Rep.trivial ℂ (Gamma0 Q) ℂ)),
      y ≠ 0 ∧
      (∀ ell, sourceTrivialCoefficientHeckeOperators ℂ Q ell y = (θ ell : ℂ) • y) ∧
      ∀ ell, φ (θ ell) = values ell) ∨
      ∀ ell, values ell = (ell.val : F) + 1 := by
  rcases sourceTrivialH1Eigen_HeckeCharacter_or_eisenstein F Q values x hx heig with
    ⟨r, hr⟩ | h
  · exact Or.inl (sourceTrivialHeckeCharacter_exists_complexEigenlift F Q r values hr)
  · exact Or.inr h

end
end Dubon2026
