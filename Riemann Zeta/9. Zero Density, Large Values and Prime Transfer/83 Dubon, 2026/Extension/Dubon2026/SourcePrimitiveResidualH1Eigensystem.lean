import Dubon2026.SourceBinaryResidualH1Eigensystem

/-! Original primitive residual H1 eigensystems, conditional only on actual Hecke commutativity.
DUB-17/18 -> residual modular Galois association -> original residual H1
eigensystem. The original integral character, prescribed-prime local field,
coefficient reduction, nonzero tensor eigenclass and injective Hecke-compatible
tensor map are all consumed. The remaining commutativity hypothesis is stated
on the actual full integral H1 operators, not on the intended conclusion.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}

private theorem primitiveResidualEigenclass
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [Algebra 𝓀[E] K]
    (ell : ℕ) (hell : ell.Prime) [CharP K ell]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hcomm : ∀ p q : sourceBinaryHeckePrime Q,
      Commute (sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p)
        (sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat q))
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (χ : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] K)
    (hχ : ∀ p : sourceBinaryHeckePrime Q,
      χ ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
        Algebra.subset_adjoin ⟨p, rfl⟩⟩ =
        algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
          ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
            ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩)) :
    ∃ x : groupCohomology.H1 (sourceBinaryCoefficientRep K Q (k - 2).toNat),
      x ≠ 0 ∧ ∀ p : sourceBinaryHeckePrime Q,
        sourceBinaryH1PrimeOperators K Q (k - 2).toNat p x =
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
              ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) • x := by
  obtain ⟨x, hx, heig⟩ :=
    sourceBinaryH1HeckeCharacter_exists_residualEigenclass Q (k - 2).toNat ell hell K hcomm χ
  exact ⟨x, hx, fun p => (heig p).trans (congrArg (· • x) (hχ p))⟩

/-- The original primitive form and its actual local coefficient embedding supply a nonzero
residual H1 eigenclass with the original eigenvalues, conditional only on commutativity of
the genuine full integral H1 Hecke operators. -/
theorem sourcePrimitive_exists_residualH1Eigensystem_of_commute
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type} [Field K] [IsAlgClosed K] [Algebra 𝓀[E] K]
    (ell : ℕ) (hell : ell.Prime) [CharP K ell]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (hcomm : ∀ p q : sourceBinaryHeckePrime Q,
      Commute (sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p)
        (sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat q))
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ x : groupCohomology.H1 (sourceBinaryCoefficientRep K Q (k - 2).toNat),
      x ≠ 0 ∧ ∀ p : sourceBinaryHeckePrime Q,
        sourceBinaryH1PrimeOperators K Q (k - 2).toNat p x =
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
              ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) • x := by
  obtain ⟨χ, hχ⟩ := sourcePrimitive_exists_residualH1HeckeCharacter (K := K) f hk τ
  exact primitiveResidualEigenclass ell hell f hk hcomm τ χ hχ

/-- At every prescribed rational prime, the original primitive form supplies the genuine
local field and nonzero residual binary H1 eigensystem with its original Fourier reduction.
Only pairwise commutativity of the actual integral H1 Hecke operators remains explicit. -/
theorem sourcePrimitive_exists_residualH1Eigensystem_charP_of_commute
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (ell : ℕ) (hell : ell.Prime)
    (hcomm : ∀ p q : sourceBinaryHeckePrime Q,
      Commute (sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p)
        (sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat q)) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero ell hell
    let F := rationalPrimeLocalField ell hell
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (_ : UniformSpace L) (_ : ValuativeRel L),
      letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
        @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ Finite 𝓀[L] ∧
      CharP (AlgebraicClosure 𝓀[L]) ell ∧
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L)
        (x : groupCohomology.H1
          (sourceBinaryCoefficientRep (AlgebraicClosure 𝓀[L]) Q (k - 2).toNat)),
        x ≠ 0 ∧ ∀ p : sourceBinaryHeckePrime Q,
          sourceBinaryH1PrimeOperators (AlgebraicClosure 𝓀[L]) Q (k - 2).toNat p x =
            algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L])
              (sourcePrimitiveResidualHeckeCharacter f hk τ
                ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
                  ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) • x := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero ell hell
  let F := rationalPrimeLocalField ell hell
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_residualH1HeckeCharacter_charP f hk ell hell
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hfin, hres, hchar, τ, χ, hχ⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
    @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
  letI : CharP (AlgebraicClosure 𝓀[L]) ell := hchar
  exact ⟨u, v, hu, hv, hext, hfin, hres, hchar, τ,
    primitiveResidualEigenclass ell hell f hk hcomm τ χ hχ⟩

end
end Dubon2026
