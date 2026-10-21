import Dubon2026.SourceFiniteOrderHeckeEigen
import Dubon2026.SourcePrimitiveWeightTwo

/-! DUB-17/18 -> residual Galois association -> the actual primitive-form
weight-two class either lies in the integral span or has the exact
Eisenstein eigenvalues. Both original field-entry consumers are composed,
retaining every source weight at least two, every prime, the genuine local
coefficient field, exact Fourier factor and level bound.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open CongruenceSubgroup groupCohomology
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The original primitive form supplies a weight-two class satisfying the
proved integral-span or exact Eisenstein alternative. -/
theorem sourcePrimitive_exists_weightTwo_integral_or_eisenstein
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [IsAlgClosed K] [Algebra 𝓀[E] K]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ (M : ℕ), Q ∣ M ∧ M ∣ Q * p ^ 2 ∧
      ∃ (values : sourceBinaryHeckePrime M → K)
        (y : H1 (Rep.trivial K (Gamma0 M) K)), y ≠ 0 ∧
        (∀ ell : sourceBinaryHeckePrime M,
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
              ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
            (ell.val : K) ^ ((k - 2).toNat / 2) * values ell) ∧
        (∀ ell, sourceTrivialCoefficientHeckeOperators K M ell y = values ell • y) ∧
        (y ∈ Submodule.span K (Set.range fun z : Additive (Gamma0 M) →+ ℤ =>
          (H1IsoOfIsTrivial (Rep.trivial K (Gamma0 M) K)).inv ((Int.castAddHom K).comp z)) ∨
          ∀ ell, values ell = (ell.val : K) + 1) := by
  obtain ⟨M, hQM, hM, values, y, hy, hvalues, heig⟩ :=
    sourcePrimitive_exists_residualWeightTwo (K := K) p hp f hk τ
  letI : NeZero M := ⟨by
    intro hm
    rw [hm, zero_dvd_iff] at hM
    exact mul_ne_zero (NeZero.ne Q) (pow_ne_zero 2 hp.ne_zero) hM⟩
  exact ⟨M, hQM, hM, values, y, hy, hvalues, heig,
    sourceTrivialH1Eigen_integral_or_eisenstein K M values y heig⟩

/-- Every original primitive form and every prescribed prime construct the
genuine local field and weight-two class with the integral/Eisenstein alternative. -/
theorem sourcePrimitive_exists_weightTwo_integral_or_eisenstein_charP
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero p hp
    let F := rationalPrimeLocalField p hp
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace L) (_ : ValuativeRel L),
      letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
        @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ Finite 𝓀[L] ∧
      ∃ hchar : CharP (AlgebraicClosure 𝓀[L]) p,
      letI := hchar
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L)
        (M : ℕ), Q ∣ M ∧ M ∣ Q * p ^ 2 ∧
        ∃ (values : sourceBinaryHeckePrime M → AlgebraicClosure 𝓀[L])
          (y : H1 (Rep.trivial (AlgebraicClosure 𝓀[L]) (Gamma0 M) (AlgebraicClosure 𝓀[L]))),
          y ≠ 0 ∧
          (∀ ell : sourceBinaryHeckePrime M,
            algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L])
              (sourcePrimitiveResidualHeckeCharacter f hk τ
                ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
                  ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
              (ell.val : AlgebraicClosure 𝓀[L]) ^ ((k - 2).toNat / 2) * values ell) ∧
          (∀ ell, sourceTrivialCoefficientHeckeOperators (AlgebraicClosure 𝓀[L]) M ell y =
            values ell • y) ∧
          (y ∈ Submodule.span (AlgebraicClosure 𝓀[L])
            (Set.range fun z : Additive (Gamma0 M) →+ ℤ =>
              (H1IsoOfIsTrivial (Rep.trivial (AlgebraicClosure 𝓀[L]) (Gamma0 M)
                (AlgebraicClosure 𝓀[L]))).inv ((Int.castAddHom (AlgebraicClosure 𝓀[L])).comp z)) ∨
            ∀ ell, values ell = (ell.val : AlgebraicClosure 𝓀[L]) + 1) := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_residualWeightTwo_charP f hk p hp
  dsimp only at hc
  obtain ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, M, hQM, hM,
    values, y, hy, hvalues, heig⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
    @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
  letI : CharP (AlgebraicClosure 𝓀[L]) p := hchar
  letI : NeZero M := ⟨by
    intro hm
    rw [hm, zero_dvd_iff] at hM
    exact mul_ne_zero (NeZero.ne Q) (pow_ne_zero 2 hp.ne_zero) hM⟩
  exact ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, M, hQM, hM,
    values, y, hy, hvalues, heig,
    sourceTrivialH1Eigen_integral_or_eisenstein _ M values y heig⟩

end
end Dubon2026
