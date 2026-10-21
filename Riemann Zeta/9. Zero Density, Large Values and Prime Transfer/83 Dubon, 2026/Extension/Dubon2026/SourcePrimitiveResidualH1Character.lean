import Dubon2026.SourcePrimitiveIntegralH1Character

/-! The actual integral H1 Hecke character specializes in the original local residue field.
DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> higher symmetric-power
continuation -> residual modular Galois association -> residual H1
eigensystem -> original integral H1 character and its prescribed-prime reduction.
The existing algebraic-integer extension supplies the specialization, with
every good-prime value identified with the original local eigencharacter.
This does not yet assert the existence of a nonzero residual H1 eigenclass.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel
variable {Q : ℕ} [NeZero Q] {k : ℤ}

/-- Any specialization of the algebraic integers induces the actual integral H1 character. -/
def sourcePrimitiveResidualH1HeckeCharacter {K : Type*} [Field K]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (φ : integralClosure ℤ ℂ →+* K) :
    sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] K :=
  φ.toIntAlgHom.comp (sourcePrimitiveIntegralH1HeckeCharacter f hk)

/-- The H1 specialization has exactly the same original good-prime values as the analytic specialization. -/
theorem sourcePrimitiveResidualH1HeckeCharacter_hecke {K : Type*} [Field K]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (φ : integralClosure ℤ ℂ →+* K)
    (p : sourceBinaryHeckePrime Q) :
    sourcePrimitiveResidualH1HeckeCharacter f hk φ
      ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
        Algebra.subset_adjoin ⟨p, rfl⟩⟩ =
      φ (sourcePrimitiveIntegralHeckeCharacter f hk
        ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
          ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) := by
  change φ (sourcePrimitiveIntegralH1HeckeCharacter f hk _) = _
  rw [sourcePrimitiveIntegralH1HeckeCharacter_original]

private theorem residualH1Specialization
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type*} [Field K] [Algebra 𝓀[E] K]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E)
    (φ : integralClosure ℤ ℂ →+* K)
    (hφ : ∀ T : sourceOriginalIntegralHeckeAlgebra Q k,
      φ (sourcePrimitiveIntegralHeckeCharacter f hk T) =
        algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ T)) :
    ∃ χ : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] K,
      ∀ p : sourceBinaryHeckePrime Q,
        χ ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
          Algebra.subset_adjoin ⟨p, rfl⟩⟩ =
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
              ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) := by
  refine ⟨sourcePrimitiveResidualH1HeckeCharacter f hk φ, fun p => ?_⟩
  rw [sourcePrimitiveResidualH1HeckeCharacter_hecke, hφ]

/-- The actual original local coefficient reduction supplies the H1 Hecke character;
no specialization of the algebraic integers is an input. -/
theorem sourcePrimitive_exists_residualH1HeckeCharacter
    {E : Type} [Field E] [CharZero E] [ValuativeRel E]
    {K : Type*} [Field K] [IsAlgClosed K] [Algebra 𝓀[E] K]
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k)
    (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] E) :
    ∃ χ : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] K,
      ∀ p : sourceBinaryHeckePrime Q,
        χ ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
          Algebra.subset_adjoin ⟨p, rfl⟩⟩ =
          algebraMap 𝓀[E] K (sourcePrimitiveResidualHeckeCharacter f hk τ
            ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
              ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) := by
  obtain ⟨φ, hφ⟩ := sourcePrimitive_exists_algebraicIntegerReduction (K := K) f hk τ
  exact residualH1Specialization f hk τ φ hφ

/-- At every prescribed rational prime, the original primitive form supplies a character
of its actual integral H1 Hecke algebra in the algebraic closure of its genuine finite
local residue field. No local coefficient field, specialization, residue characteristic,
H1 character or prime eigenvalue compatibility is supplied as a hypothesis. -/
theorem sourcePrimitive_exists_residualH1HeckeCharacter_charP
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (ell : ℕ) (hell : ell.Prime) :
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
        (χ : sourceBinaryH1HeckeAlgebra Q (k - 2).toNat →ₐ[ℤ] AlgebraicClosure 𝓀[L]),
        ∀ p : sourceBinaryHeckePrime Q,
          χ ⟨sourceBinaryH1PrimeOperators ℤ Q (k - 2).toNat p,
            Algebra.subset_adjoin ⟨p, rfl⟩⟩ =
            algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L])
              (sourcePrimitiveResidualHeckeCharacter f hk τ
                ⟨cuspHeckeLinear Q k p.val, Algebra.subset_adjoin
                  ⟨(⟨p.val, p.property.1.pos⟩ : ℕ+), rfl⟩⟩) := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero ell hell
  let F := rationalPrimeLocalField ell hell
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hc := sourcePrimitive_exists_algebraicIntegerReduction_charP f hk ell hell
  dsimp only at hc
  obtain ⟨u, v, hu, hv, hext, hfin, hres, hchar, τ, φ, hφ⟩ := hc
  letI : UniformSpace L := u
  letI : ValuativeRel L := v
  letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
    @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
  exact ⟨u, v, hu, hv, hext, hfin, hres, hchar, τ,
    residualH1Specialization f hk τ φ hφ⟩

end
end Dubon2026
