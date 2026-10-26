import Dubon2026.SourceGammaOneHeckeArithmeticDivisors

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> original all-weight
characteristic-zero Galois association -> arithmetic realization of the
actual finite Gamma1 Hecke characters. The genuine coefficient action on
the actual Gamma1 Picard group commutes with the literal finite Hecke
correspondence. Place restriction, ramification, norm and degree inputs
are derived. No arithmetic-equivariance certificate remains.
Geometric/H1, diamond, Frobenius/inertia and finite-character Galois
realization are still separate required obligations. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup
variable {L : Type*} [Field L] [Algebra ℚ L] [CharZero L]
variable (M d : ℕ) [NeZero M] [NeZero d]

theorem heckeDivisor_arithmetic (σ : L ≃ₐ[ℚ] L)
    (D : Divisor L (laurentBaseChange L (x1FunctionField M))) :
    arithmeticDivisorEquiv (Gamma1 M) σ (heckeDivisor L M d D) =
      heckeDivisor L M d (arithmeticDivisorEquiv (Gamma1 M) σ D) := by
  change arithmeticDivisorEquiv (Gamma1 M) σ
    (Divisor.geometricPushforwardAlong (heckeAlpha L M d) (heckeAlpha_finite L M d)
      (Divisor.finitePullbackAlong (heckeBeta L M d) (heckeBeta_finite L M d) D)) = _
  exact (geometricPushforwardAlong_arithmetic (Gamma1 M) (Gamma1 M ⊓ Gamma0 (d * M))
    (heckeAlpha L M d) (heckeAlpha_finite L M d) (heckeAlpha_arithmetic M d) σ
    (Divisor.finitePullbackAlong (heckeBeta L M d) (heckeBeta_finite L M d) D)).symm.trans
      (congrArg (Divisor.geometricPushforwardAlong (heckeAlpha L M d)
        (heckeAlpha_finite L M d))
        (finitePullbackAlong_arithmetic (Gamma1 M) (Gamma1 M ⊓ Gamma0 (d * M))
          (heckeBeta L M d) (heckeBeta_finite L M d) (heckeBeta_arithmetic M d) σ D))

variable [IsAlgClosed L]

/-- The genuine arithmetic coefficient action on the actual Gamma1 Picard group. -/
def gamma1ArithmeticPicardRep (K : Type*) [Field K] [Algebra ℚ K] [IsAlgClosed K]
    (N : ℕ) [NeZero N] :
    (K ≃ₐ[ℚ] K) →* AddMonoid.End (Pic0 K (laurentBaseChange K (x1FunctionField N))) :=
  arithmeticPicardRep (Gamma1 N) (by simp [Gamma1_mem, ModularGroup.T])

theorem heckePicard_arithmetic (σ : L ≃ₐ[ℚ] L)
    (x : Pic0 L (laurentBaseChange L (x1FunctionField M))) :
    gamma1ArithmeticPicardRep L M σ (heckePicard L M d x) =
      heckePicard L M d (gamma1ArithmeticPicardRep L M σ x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  have hT : ModularGroup.T ∈ Gamma1 M := by simp [Gamma1_mem, ModularGroup.T]
  change Pic0.mk (arithmeticDegZero (Gamma1 M) hT σ
    ⟨heckeDivisor L M d D.val, heckeDivisor_mem_degZero L M d D.2⟩) =
      Pic0.mk ⟨heckeDivisor L M d (arithmeticDegZero (Gamma1 M) hT σ D).val,
        heckeDivisor_mem_degZero L M d (arithmeticDegZero (Gamma1 M) hT σ D).2⟩
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact heckeDivisor_arithmetic M d σ D.val

omit [CharZero L] [NeZero d] in
theorem gamma1ArithmeticPicardRep_torsion (σ : L ≃ₐ[ℚ] L) (n : ℕ)
    (x : Pic0 L (laurentBaseChange L (x1FunctionField M))) (hx : x ∈ Pic0.torsion n) :
    gamma1ArithmeticPicardRep L M σ x ∈ Pic0.torsion n :=
  arithmeticPicard_torsion (Gamma1 M) (by simp [Gamma1_mem, ModularGroup.T]) σ n x hx

end
end Dubon2026.SourceFunctionField.GammaOne
