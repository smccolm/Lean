import Dubon2026.SourceResidualWeightTwoAlternatives
import Dubon2026.SourcePrimitiveWeightTwo

/-! DUB-17/18 -> residual Galois association -> every original primitive
form, source weight and prescribed prime constructs the two exact
weight-two branches: a genuine nonzero parabolic complex lift with
integral eigenvalues and exact reduction, or actual residual unit
characters with product one and the exact prime eigenvalues. The original
local field, residue characteristic, level bound and Fourier twist remain.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open CongruenceSubgroup groupCohomology SourceCuspBoundary
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- The original primitive form supplies a weight-two class satisfying the
proved parabolic-lift or residual-character alternative. -/
theorem sourcePrimitive_exists_weightTwo_parabolicLift_or_dirichletPair
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
        ((∃ (θ : sourceBinaryHeckePrime M → integralClosure ℤ ℂ)
          (φ : integralClosure ℤ ℂ →+* K)
          (v : H1 (Rep.trivial ℂ (Gamma0 M) ℂ)), v ≠ 0 ∧
          (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 M) ℂ)).hom v ∈ parabolicHoms M ∧
          (∀ ell, sourceTrivialCoefficientHeckeOperators ℂ M ell v = (θ ell : ℂ) • v) ∧
          ∀ ell, φ (θ ell) = values ell) ∨
          ∃ ψ₁ ψ₂ : (ZMod M)ˣ →* (K)ˣ,
            (∀ u, (ψ₁ u : K) * (ψ₂ u : K) = 1) ∧
            ∀ ell : sourceBinaryHeckePrime M,
              values ell = (ψ₁ (ZMod.unitOfCoprime ell.val ell.property.2) : K) +
                (ell.val : K) * (ψ₂ (ZMod.unitOfCoprime ell.val ell.property.2) : K)) := by
  obtain ⟨M, hQM, hM, values, y, hy, hvalues, heig⟩ :=
    sourcePrimitive_exists_residualWeightTwo (K := K) p hp f hk τ
  letI : NeZero M := ⟨by
    intro hm
    rw [hm, zero_dvd_iff] at hM
    exact mul_ne_zero (NeZero.ne Q) (pow_ne_zero 2 hp.ne_zero) hM⟩
  exact ⟨M, hQM, hM, values, y, hy, hvalues, heig,
    sourceTrivialH1Eigen_parabolicLift_or_dirichletPair K M values y hy heig⟩

/-- Every original primitive form and every prescribed prime construct the
genuine local field and weight-two class with the parabolic-lift/residual-character alternative. -/
theorem sourcePrimitive_exists_weightTwo_parabolicLift_or_dirichletPair_charP
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
          ((∃ (θ : sourceBinaryHeckePrime M → integralClosure ℤ ℂ)
            (φ : integralClosure ℤ ℂ →+* AlgebraicClosure 𝓀[L])
            (v : H1 (Rep.trivial ℂ (Gamma0 M) ℂ)), v ≠ 0 ∧
            (H1IsoOfIsTrivial (Rep.trivial ℂ (Gamma0 M) ℂ)).hom v ∈ parabolicHoms M ∧
            (∀ ell, sourceTrivialCoefficientHeckeOperators ℂ M ell v = (θ ell : ℂ) • v) ∧
            ∀ ell, φ (θ ell) = values ell) ∨
            ∃ ψ₁ ψ₂ : (ZMod M)ˣ →* (AlgebraicClosure 𝓀[L])ˣ,
              (∀ u, (ψ₁ u : AlgebraicClosure 𝓀[L]) * (ψ₂ u : AlgebraicClosure 𝓀[L]) = 1) ∧
              ∀ ell : sourceBinaryHeckePrime M,
                values ell = (ψ₁ (ZMod.unitOfCoprime ell.val ell.property.2) : AlgebraicClosure 𝓀[L]) +
                  (ell.val : AlgebraicClosure 𝓀[L]) * (ψ₂ (ZMod.unitOfCoprime ell.val ell.property.2) : AlgebraicClosure 𝓀[L])) := by
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
    sourceTrivialH1Eigen_parabolicLift_or_dirichletPair _ M values y hy heig⟩

end
end Dubon2026
