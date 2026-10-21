import Dubon2026.SourceBinaryCharacterLevel
import Dubon2026.SourceOriginalResidualH1Eigensystem

/-! Every original primitive form supplies a genuine residual character eigensystem.
DUB-17/18 -> residual modular Galois association -> weight/level reduction
-> original character eigensystem at a level dividing Q*p. All source
weights at least two and every prescribed rational prime are retained.
The native binary class, nonvanishing, level change and exact character
and Hecke scalar comparisons are constructed from the original form.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- Every original primitive form and its existing local coefficient embedding
give a nonzero actual character H1 eigensystem at a level dividing Q*p,
with the original good-prime Fourier reductions and exact ell^j twist.
The prescribed residue prime may divide the original level or lie outside it. -/
theorem sourcePrimitive_exists_residualCharacterLevel
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [IsAlgClosed K] [Algebra 𝓀[E] K]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ (M : ℕ) (hQM : Q ∣ M) (hpM : p ∣ M), M ∣ Q * p ∧
      ∃ j : ℕ, j ≤ (k - 2).toNat ∧
        (sourceBinaryFlagExponentOf p (k - 2).toNat j + 2 * j ≡ (k - 2).toNat [MOD (p - 1)]) ∧
        ∃ (values : sourceBinaryHeckePrime M → K)
          (y : groupCohomology.H1 (sourceBinaryFlagQuotientRep K p M hpM (k - 2).toNat j)),
          y ≠ 0 ∧
          (∀ ell : sourceBinaryHeckePrime M,
            algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
              ⟨cuspHeckeLinear Q k (sourceBinaryGoodPrimeOfLevel hQM ell).val,
                Algebra.subset_adjoin
                  ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
              (ell.val : K) ^ j * values ell) ∧
          ∀ ell, sourceBinaryFlagUntwistedOperators K p M hpM (k - 2).toNat j ell y =
            values ell • y := by
  obtain ⟨x, hx, heig⟩ := sourcePrimitive_exists_residualH1Eigensystem (K := K) p hp f hk τ
  obtain ⟨M, hQM, hpM, hM, j, hj, hmod, _, values, y, hy, hvalues, he⟩ :=
    sourceBinaryH1_exists_characterLevel K Q p (k - 2).toNat hp _ x hx heig
  exact ⟨M, hQM, hpM, hM, j, hj, hmod, values, y, hy, hvalues, he⟩

private theorem primitiveCharacterLevelFromBinary
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [Algebra 𝓀[E] K]
    (p : ℕ) (hp : p.Prime) [CharP K p]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep K Q (k - 2).toNat))
    (hx : x ≠ 0)
    (heig : ∀ ell : sourceBinaryHeckePrime Q,
      sourceBinaryH1PrimeOperators K Q (k - 2).toNat ell x =
        algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
          ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
            ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) • x) :
    ∃ (M : ℕ) (hpM : p ∣ M), Q ∣ M ∧ M ∣ Q * p ∧
      ∃ j : ℕ, j ≤ (k - 2).toNat ∧
        (sourceBinaryFlagExponentOf p (k - 2).toNat j + 2 * j ≡ (k - 2).toNat [MOD (p - 1)]) ∧
        ∃ (values : sourceBinaryHeckePrime M → K)
          (y : groupCohomology.H1 (sourceBinaryFlagQuotientRep K p M hpM (k - 2).toNat j)),
          y ≠ 0 ∧
          (∀ ell : sourceBinaryHeckePrime M,
            algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
              ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
                ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
              (ell.val : K) ^ j * values ell) ∧
          ∀ ell, sourceBinaryFlagUntwistedOperators K p M hpM (k - 2).toNat j ell y =
            values ell • y := by
  obtain ⟨M, hQM, hpM, hM, j, hj, hmod, _, values, y, hy, hvalues, he⟩ :=
    sourceBinaryH1_exists_characterLevel K Q p (k - 2).toNat hp _ x hx heig
  exact ⟨M, hpM, hQM, hM, j, hj, hmod, values, y, hy, hvalues, he⟩

/-- At every prescribed rational prime, the original primitive form supplies
its genuine local coefficient field and a nonzero native character H1
eigensystem at a level dividing Q*p. No coefficient-field, binary eigenclass,
level-divisibility, surviving character or Hecke-compatibility input is supplied. -/
theorem sourcePrimitive_exists_residualCharacterLevel_charP
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
        (M : ℕ) (hpM : p ∣ M), Q ∣ M ∧ M ∣ Q * p ∧
        ∃ j : ℕ, j ≤ (k - 2).toNat ∧
          (sourceBinaryFlagExponentOf p (k - 2).toNat j + 2 * j ≡ (k - 2).toNat [MOD (p - 1)]) ∧
          ∃ (values : sourceBinaryHeckePrime M → AlgebraicClosure 𝓀[L])
            (y : groupCohomology.H1 (sourceBinaryFlagQuotientRep
              (AlgebraicClosure 𝓀[L]) p M hpM (k - 2).toNat j)),
            y ≠ 0 ∧
            (∀ ell : sourceBinaryHeckePrime M,
              algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L])
                (sourcePrimitiveResidualHeckeCharacter f hk τ
                  ⟨cuspHeckeLinear Q k ell.val, Algebra.subset_adjoin
                    ⟨(⟨ell.val, ell.property.1.pos⟩ : ℕ+), rfl⟩⟩) =
                (ell.val : AlgebraicClosure 𝓀[L]) ^ j * values ell) ∧
            ∀ ell, sourceBinaryFlagUntwistedOperators
              (AlgebraicClosure 𝓀[L]) p M hpM (k - 2).toNat j ell y = values ell • y := by
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
    τ, primitiveCharacterLevelFromBinary p hp f hk τ x hx heig⟩

end
end Dubon2026
