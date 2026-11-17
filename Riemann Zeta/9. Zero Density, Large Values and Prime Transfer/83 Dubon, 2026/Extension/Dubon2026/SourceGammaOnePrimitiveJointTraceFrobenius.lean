import Dubon2026.SourceGammaOnePrimitiveJointTrace

/-! DUB-17/18 -> all-weight association -> finite traces. The same trace
has the original Hecke value at every original local residue Frobenius,
including the norm Frobenius selected by native Chebotarev. -/
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
private theorem trace_of_quadratic {G R : Type} [Group G] [Ring R]
    (ρ : G →* R) (g : G) (H D : R) (h : ρ g * H = ρ g * ρ g + D) :
    ρ g + ρ g⁻¹ * D = H := by
  apply ((Group.isUnit g).map ρ).mul_left_cancel
  calc
    ρ g * (ρ g + ρ g⁻¹ * D) = ρ g * ρ g + D := by
      rw [mul_add, ← mul_assoc, ← map_mul ρ g g⁻¹, mul_inv_cancel, map_one, one_mul]
    _ = ρ g * H := h.symm

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

/-- Every original local residue Frobenius has the original trace value. -/
theorem binaryPrimitiveJointTrace_local_frobenius
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    (ell : sourceBinaryHeckePrime (Q * N))
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure ell.val ell.property.1)
    (d : (sourceRationalLocalValuation ell.val ell.property.1 e).decompositionSubgroup ℚ)
    (hd : ∀ a : IsLocalRing.ResidueField (sourceRationalLocalValuation ell.val ell.property.1 e),
      d • a = a ^ ell.val) :
    binaryPrimitiveJointTrace Q p n w d.val =
      binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inl ell)) := by
  obtain ⟨g, hg⟩ := sourceGammaOneDiamondLabel_lift M
    (ZMod.unitOfCoprime ell.val (binaryPrimitiveLevelPrime Q N ell).property.2)
  have hlabel : (g.val 1 1 : ZMod M) = ell.val := by
    simpa only [Gamma0Map, ZMod.coe_unitOfCoprime] using hg
  let A := sourceRationalLocalValuation ell.val ell.property.1 e
  letI := GaussReduction.residue_charP_of_prime_mem_nonunits A ell.val ell.property.1
    (sourceRationalLocalValuation_prime ell.val ell.property.1 e)
  have haway := ell.property.1.coprime_iff_not_dvd.mp (binaryPrimitiveLevelPrime Q N ell).property.2
  have hgeo := gammaOne_local_degree_and_genus_eq M ell.val ell.property.1 haway e
  have hp : (p : IsLocalRing.ResidueField A) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff _ ell.val]
    intro h
    exact (ell.property.1.coprime_iff_not_dvd.mp ell.property.2)
      (dvd_mul_of_dvd_right (h.trans (dvd_pow_self p (Nat.succ_ne_zero n))) Q)
  have hpoly := binaryPrimitiveJointGaloisRep_frobenius_of_degree_genus_eq Q p n w A ell
    hgeo.1 hgeo.2 d hd hp Hq hH g hlabel
  have hD := binaryPrimitiveJointDeterminant_frobenius Q p n w A ell Hq g hlabel d hd
  exact trace_of_quadratic (binaryPrimitiveJointGaloisRep Q p n w) d.val _ _
    (hpoly.trans (congrArg
      (binaryPrimitiveJointGaloisRep Q p n w d.val * binaryPrimitiveJointGaloisRep Q p n w d.val + ·)
      hD.symm))

/-- The actual norm Frobenius has the original Hecke trace under the same embedding. -/
theorem binaryPrimitiveJointTrace_norm_frobenius
    (Hq : sourceBinaryHeckePrime (Q * N) → Module.End (ZMod N) J)
    (hH : ∀ ell, (Hq ell).comp (binaryTateDiamondRelations Q p n w).mkQ =
      (binaryTateDiamondRelations Q p n w).mkQ.comp (binaryTatePrimeOperators Q p n w ell))
    (ell : sourceBinaryHeckePrime (Q * N))
    (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure ell.val ell.property.1)
    (φ : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
      rationalPrimeLocalField ell.val ell.property.1))
    (hφ : ∀ a : IsLocalRing.ResidueField (algebraicLocalIntegerRing
      (rationalPrimeLocalClosure ell.val ell.property.1)), φ • a = a ^ ell.val) :
    binaryPrimitiveJointTrace Q p n w (embeddedNormalGaloisRestriction e φ) =
      binaryPrimitiveJointHeckeDiamondWord Q p n w Hq (FreeAlgebra.ι ℤ (Sum.inl ell)) := by
  obtain ⟨hd, hres⟩ := sourceRationalLocalValuation_frobenius ell.val ell.property.1 e φ hφ
  exact binaryPrimitiveJointTrace_local_frobenius Q p n w Hq hH ell e
    ⟨embeddedNormalGaloisRestriction e φ, hd⟩ hres

end
end Dubon2026.SourceFunctionField.GammaOne
