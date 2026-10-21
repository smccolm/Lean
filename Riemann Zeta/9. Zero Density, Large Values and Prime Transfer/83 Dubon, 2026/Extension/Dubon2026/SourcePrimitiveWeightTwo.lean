import Dubon2026.SourceBinaryWeightTwo
import Dubon2026.SourcePrimitiveWeightParity
import Dubon2026.SourceOriginalResidualH1Eigensystem

/-! Every original primitive form supplies its actual residual weight-two class.
DUB-17/18 -> residual modular Galois association -> original weight-two
cohomological input. All source weights at least two and every prescribed
rational prime are retained. The genuine residue field, nonzero binary
class, weight parity, character descent, small-prime cases, exact twist
and level bound are derived from the original primitive form.
Geometric Galois association and the subsequent adic and symmetric-power
inputs remain separate required obligations.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel
open CongruenceSubgroup groupCohomology

variable {Q : ℕ} [NeZero Q] {k : ℤ}

private theorem primitiveWeightTwoFromBinary
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [Algebra 𝓀[E] K]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (x : H1 (sourceBinaryCoefficientRep K Q (k - 2).toNat)) (hx : x ≠ 0)
    (heig : ∀ ell : sourceBinaryHeckePrime Q,
      sourceBinaryH1PrimeOperators K Q (k - 2).toNat ell x =
        algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
          ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
            ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) • x) :
    ∃ (M : ℕ), Q ∣ M ∧ M ∣ Q * p ^ 2 ∧
      ∃ (values : sourceBinaryHeckePrime M → K)
        (y : H1 (Rep.trivial K (Gamma0 M) K)), y ≠ 0 ∧
        (∀ ell : sourceBinaryHeckePrime M,
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
              ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
            (ell.val : K) ^ ((k - 2).toNat / 2) * values ell) ∧
        ∀ ell, sourceTrivialCoefficientHeckeOperators K M ell y = values ell • y := by
  obtain ⟨M, hQM, hM, values, y, hy, hvalues, hey⟩ :=
    sourceBinaryH1_exists_weightTwo K Q p (k - 2).toNat hp
      (Or.inl (sourcePrimitive_binaryDegree_even f hk)) _ x hx heig
  exact ⟨M, hQM, hM, values, y, hy, hvalues, hey⟩

/-- The original primitive form and its existing local coefficient embedding
supply an actual nonzero weight-two eigensystem at a level dividing Q*p squared.
The exact original Fourier reductions equal ell^((k-2)/2) times its eigenvalues,
including residue characteristics two and three. -/
theorem sourcePrimitive_exists_residualWeightTwo
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
        ∀ ell, sourceTrivialCoefficientHeckeOperators K M ell y = values ell • y := by
  obtain ⟨x, hx, heig⟩ := sourcePrimitive_exists_residualH1Eigensystem (K := K) p hp f hk τ
  exact primitiveWeightTwoFromBinary p hp f hk τ x hx heig

/-- At every prescribed rational prime, every original primitive form of
source weight at least two supplies its genuine local coefficient field
and a nonzero original weight-two H1 eigensystem with exact Fourier factors
and level dividing Q*p squared. No parity, residual class, surviving
character, small-prime lift, field or Hecke-compatibility premise remains. -/
theorem sourcePrimitive_exists_residualWeightTwo_charP
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
          ∀ ell, sourceTrivialCoefficientHeckeOperators (AlgebraicClosure 𝓀[L]) M ell y =
            values ell • y := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_residualH1Eigensystem_charP f hk p hp
  dsimp only at hc
  obtain ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, x, hx, heig⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
    @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
  letI : CharP (AlgebraicClosure 𝓀[L]) p := hchar
  exact ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar,
    τ, primitiveWeightTwoFromBinary p hp f hk τ x hx heig⟩

end
end Dubon2026
