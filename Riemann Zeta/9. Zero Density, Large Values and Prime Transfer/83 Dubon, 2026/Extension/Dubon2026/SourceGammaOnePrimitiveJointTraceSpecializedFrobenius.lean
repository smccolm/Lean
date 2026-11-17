import Dubon2026.SourceGammaOnePrimitiveJointTraceSpecialization

/-! DUB-17/18 -> original all-weight association -> original adic traces.
Specialization preserves the actual norm-Frobenius trace. The original
trivial diamond character discharges the determinant diamond term,
leaving the precise weight power at each good prime. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve CongruenceSubgroup SourceCuspBoundary CoefficientReduction
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
private theorem map_weighted_one {A B : Type} [Ring A] [Ring B]
    (χ : A →+* B) (a : A) (q v : ℕ) (ha : χ a = 1) : χ ((q ^ v) • a) = (q : B) ^ v := by
  simp only [map_nsmul, ha, nsmul_one, Nat.cast_pow]

variable (Q p n w : ℕ) [NeZero Q] [Fact p.Prime]
local notation "N" => p ^ (n + 1)
local notation "M" => Q * N ^ 2
local notation "V" => sourceBinaryCoefficientRep (ZMod N) Q w
local notation "T" => TateModule p (Pic0 Qbar (functionFieldOver (Gamma1 M) Qbar))
private local instance : Algebra ℤ_[p] (ZMod N) := (PadicInt.toZModPow (n + 1)).toAlgebra
private local instance : Module ℤ_[p] V := Module.restrictScalars ℤ_[p] (ZMod N) V
private local instance : IsScalarTower ℤ_[p] (ZMod N) V :=
  IsScalarTower.restrictScalars ℤ_[p] (ZMod N) V
private local instance : AddCommGroup (T →ₗ[ℤ_[p]] V) := inferInstance
private local instance : Module (ZMod N) (T →ₗ[ℤ_[p]] V) := inferInstance
local notation "J" => (T →ₗ[ℤ_[p]] V) ⧸ binaryTateDiamondRelations Q p n w
local notation "S" => sourceBinaryHeckePrime (Q * N) ⊕ Gamma0 M

/-- At every actual norm Frobenius, the specialized trace is the same
character applied to the original good-prime Hecke generator. -/
theorem binaryPrimitiveJointSpecializedTrace_norm_frobenius
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C)
    (ell : sourceBinaryHeckePrime (Q * N))
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure ell.val ell.property.1)
    (φ : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
      rationalPrimeLocalField ell.val ell.property.1))
    (hφ : ∀ a : IsLocalRing.ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure ell.val ell.property.1)), φ • a = a ^ ell.val) :
    binaryPrimitiveJointSpecializedTrace Q p n w Hq hH χ (embeddedNormalGaloisRestriction e φ) =
      χ ((binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).rangeRestrict
        (FreeAlgebra.ι ℤ (Sum.inl ell))) :=
  congrArg χ (Subtype.ext (binaryPrimitiveJointTrace_norm_frobenius Q p n w Hq hH ell e φ hφ))

/-- The original diamond value one gives the exact weight determinant at
all actual norm Frobenius elements, without a supplied Frobenius polynomial. -/
theorem binaryPrimitiveJointSpecializedDeterminant_norm_frobenius
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    {C : Type} [Ring C] (χ : (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).range →+* C)
    (hχ : ∀ g : Gamma0 M, χ ((binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).rangeRestrict
      (FreeAlgebra.ι ℤ (Sum.inr g))) = 1)
    (ell : sourceBinaryHeckePrime (Q * N))
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure ell.val ell.property.1)
    (φ : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
      rationalPrimeLocalField ell.val ell.property.1))
    (hφ : ∀ a : IsLocalRing.ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure ell.val ell.property.1)), φ • a = a ^ ell.val) :
    binaryPrimitiveJointSpecializedDeterminant Q p n w Hq χ (embeddedNormalGaloisRestriction e φ) =
      (ell.val : C) ^ (w + 1) := by
  obtain ⟨g, hg⟩ := sourceGammaOneDiamondLabel_lift M
    (ZMod.unitOfCoprime ell.val (binaryPrimitiveLevelPrime Q N ell).property.2)
  have hlabel : (g.val 1 1 : ZMod M) = ell.val := by
    simpa only [Gamma0Map, ZMod.coe_unitOfCoprime] using hg
  obtain ⟨hd, hres⟩ := sourceRationalLocalValuation_frobenius ell.val ell.property.1 e φ hφ
  let A := sourceRationalLocalValuation ell.val ell.property.1 e
  letI := GaussReduction.residue_charP_of_prime_mem_nonunits A ell.val ell.property.1
    (sourceRationalLocalValuation_prime ell.val ell.property.1 e)
  have he : binaryPrimitiveJointHeckeDeterminant Q p n w Hq (embeddedNormalGaloisRestriction e φ) =
      (ell.val ^ (w + 1)) • (binaryPrimitiveJointHeckeDiamondWord Q p n w Hq).rangeRestrict
        (FreeAlgebra.ι ℤ (Sum.inr g)) :=
    Subtype.ext (binaryPrimitiveJointDeterminant_frobenius Q p n w A ell Hq g hlabel
      ⟨embeddedNormalGaloisRestriction e φ, hd⟩ hres)
  change χ (binaryPrimitiveJointHeckeDeterminant Q p n w Hq (embeddedNormalGaloisRestriction e φ)) = _
  rw [he]
  exact map_weighted_one χ _ ell.val (w + 1) (hχ g)

end
end Dubon2026.SourceFunctionField.GammaOne
