import Dubon2026.SourceFiniteOrderHeckeTransfer
import Dubon2026.SourceTrivialH1IntegralAlternative
import Dubon2026.SourceTrivialCoefficientHecke

/-! DUB-17/18 -> residual Galois association -> the original weight-two
eigensystem either comes from the integral span or has the exact Eisenstein
eigenvalues ell+1. The complete native Hecke operator is evaluated on the
actual detected finite-order element; neither scalar equality nor an
integral lift is assumed.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup groupCohomology

variable (F : Type) [Field F] (Q ℓ : ℕ) [NeZero ℓ]
    (hℓ : ℓ.Prime) (hℓQ : Nat.Coprime ℓ Q)

include hℓQ in
/-- The full native Hecke cocycle has its exact ell+1 evaluation on every
actual finite-order congruence element. -/
theorem sourceTrivialCoefficientHecke_finiteOrder
    (z : cocycles₁ (Rep.trivial F (Gamma0 Q) F))
    (γ : Gamma0 Q) (hγ : IsOfFinOrder γ) :
    sourcePrimeHeckeCocycles hℓ (Rep.trivial F (Gamma0 Q) F) LinearMap.id
        (sourceTrivialCoefficient_intertwine F Q hℓ) z γ =
      ((ℓ : F) + 1) * z γ := by
  let φ : Additive (Gamma0 Q) →+ F :=
    (cocycles₁IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom z
  have h := sourceFiniteOrderHecke_sum Q ℓ hℓ hℓQ φ γ hγ
  change sourcePrimeHeckeCocycles hℓ (Rep.trivial F (Gamma0 Q) F) LinearMap.id
      (sourceTrivialCoefficient_intertwine F Q hℓ) z γ = (ℓ + 1) • z γ at h
  rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  exact h

/-- The actual native H1 Hecke evaluation on a finite-order congruence
element is the exact Eisenstein scalar times its original evaluation. -/
theorem sourceTrivialH1Hecke_finiteOrder
    (ell : sourceBinaryHeckePrime Q)
    (x : H1 (Rep.trivial F (Gamma0 Q) F))
    (γ : Gamma0 Q) (hγ : IsOfFinOrder γ) :
    (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom
        (sourceTrivialCoefficientHeckeOperators F Q ell x) (Additive.ofMul γ) =
      ((ell.val : F) + 1) *
        (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom x (Additive.ofMul γ) := by
  letI : NeZero ell.val := ⟨ell.property.1.ne_zero⟩
  induction x using H1_induction_on with
  | h z =>
    change (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom
      (sourcePrimeHeckeH1 _ _ _ _ (H1π _ z)) (Additive.ofMul γ) = _
    rw [sourcePrimeHeckeH1_cocycle, H1IsoOfIsTrivial_H1π_apply_apply,
      H1IsoOfIsTrivial_H1π_apply_apply]
    exact sourceTrivialCoefficientHecke_finiteOrder F Q ell.val
      ell.property.1 ell.property.2 z γ hγ

/-- Detection of one actual finite-order element forces every original
good-prime eigenvalue to be exactly ell+1. -/
theorem sourceTrivialH1Eigen_eisenstein_of_torsion
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (Rep.trivial F (Gamma0 Q) F))
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell x = values ell • x)
    (γ : Gamma0 Q) (hγ : IsOfFinOrder γ)
    (hxγ : (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom x
      (Additive.ofMul γ) ≠ 0) :
    ∀ ell, values ell = (ell.val : F) + 1 := by
  intro ell
  have h := sourceTrivialH1Hecke_finiteOrder F Q ell x γ hγ
  rw [heig ell, map_smul] at h
  change values ell *
    (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom x (Additive.ofMul γ) =
    ((ell.val : F) + 1) *
      (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).hom x (Additive.ofMul γ) at h
  exact mul_right_cancel₀ hxγ h

/-- The original native weight-two eigensystem lies in the integral span
or has the exact Eisenstein eigenvalues at all original good primes. -/
theorem sourceTrivialH1Eigen_integral_or_eisenstein [NeZero Q]
    (values : sourceBinaryHeckePrime Q → F)
    (x : H1 (Rep.trivial F (Gamma0 Q) F))
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F Q ell x = values ell • x) :
    x ∈ Submodule.span F (Set.range fun y : Additive (Gamma0 Q) →+ ℤ =>
      (H1IsoOfIsTrivial (Rep.trivial F (Gamma0 Q) F)).inv ((Int.castAddHom F).comp y)) ∨
    ∀ ell, values ell = (ell.val : F) + 1 := by
  rcases sourceTrivialH1_integral_or_torsion Q F x with h | ⟨γ, hγ, hxγ⟩
  · exact Or.inl h
  · exact Or.inr (sourceTrivialH1Eigen_eisenstein_of_torsion F Q values x heig γ hγ hxγ)

end
end Dubon2026
