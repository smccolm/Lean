import Dubon2026.SourceGammaOneOriginalCMConsequences
import Dubon2026.SourceOriginalRationalCMPolarizationProperty

/-! DUB-17/18 -> actual original residual inputs -> original-field local unramified adjoint H1/invariant dimensions in every symmetric degree at every rational prime, together with the preceding finite detecting families on the finite linear subfield branch. The same original representation also has split regular detecting primes with exact original unramified adjoint H1 dimension equal to the symmetric degree. Every original symmetric twisted-H1 subspace also has a jointly detecting family bounded by its original-field dimension, with the exact local dimension and original torus at every selected prime. The same original representation now supplies the native CM-kernel symmetric matrix spanning and absolute irreducibility, without a full-original-field SL2-image premise. The actual cyclotomic determinant also constructs the native polarized symmetric representation for each genuine CM subfield in every degree below p, with exact original kernel matrices, component and odd similitude. No CM field existence or automorphy conclusion is asserted; every prior original conclusion is retained. Small-image exclusions and the remaining local and automorphy obligations stay open. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
open Dubon2026.SourceDickson
noncomputable section
open Matrix Polynomial
open scoped ValuativeRel NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
variable (Q p : ℕ) [NeZero Q] [Fact p.Prime] {k : ℤ}

/-- The actual original residual action has projective classification and actual finite-field linear subfield alternatives
and retains its integral origin, fixed-local Hecke data, determinant and oddness. -/
theorem exists_gammaOne_original_polarized_symmetric_residual
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (hlarge : 3 < p) :
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero p (Fact.out : p.Prime)
    let F := rationalPrimeLocalField p (Fact.out : p.Prime)
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (u : UniformSpace L) (_ : ValuativeRel L),
      letI : TopologicalSpace L := u.toTopologicalSpace
      letI : TopologicalSpace 𝓀[L] :=
        inferInstanceAs (TopologicalSpace (𝒪[L] ⧸ IsLocalRing.maximalIdeal 𝒪[L]))
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ Finite 𝓀[L] ∧ DiscreteTopology 𝓀[L] ∧
      ∃ hchar : CharP 𝓀[L] p, letI := hchar;
      ∃ τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L,
      ∃ (ρint : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →*
          Matrix.GeneralLinearGroup (Fin 2) 𝒪[L])
        (ρres : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →*
          Matrix.GeneralLinearGroup (Fin 2) 𝓀[L]),
        Continuous ρint ∧ Continuous ρres ∧
        (∀ g i j, (ρres g).val i j = IsLocalRing.residue 𝒪[L] ((ρint g).val i j)) ∧
        (Matrix.GeneralLinearGroup.det.comp ρres =
          (sourceArithmeticCyclotomicUnitCharacter (F := 𝓀[L]) p
            ((Q * p : ℕ) : 𝓞 ℚ) ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩).toMonoidHom ^
              Int.toNat (k - 1)) ∧
        (RingHom.ker (sourcePrimitiveResidualHeckeCharacter f hk τ)).IsMaximal ∧
        (Set.range ρres).Finite ∧
        (∀ (q : ℕ) (hq : q.Prime), ¬q ∣ Q * p →
      (∀ g ∈ rationalPrimeNormInertia q hq,
        ρres (rationalPrimeArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) q hq g) = 1) ∧
      ∀ g : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), g • z = z ^ q) →
        let a : 𝓀[L] := sourcePrimitiveResidualHeckeCharacter f hk τ
          ⟨Dubon2026.cuspHeckeLinear Q k q,
            Algebra.subset_adjoin ⟨(⟨q, hq.pos⟩ : ℕ+), rfl⟩⟩
        let A := (ρres (rationalPrimeArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ) q hq g)).val
        A.charpoly = (Polynomial.X : Polynomial 𝓀[L]) ^ 2 - Polynomial.C a * (Polynomial.X : Polynomial 𝓀[L]) +
          Polynomial.C ((q : 𝓀[L]) ^ Int.toNat (k - 1)) ∧
        A.trace = a ∧ A.det = (q : 𝓀[L]) ^ Int.toNat (k - 1)) ∧
        (∃ j : 𝓀[L] →+* K p,
          HasProjectiveMatrixAlternatives p (residualProjectiveAction p j ρres).range ∧
          (HasSmallProjectiveImage p (residualProjectiveAction p j ρres).range ∨
            (HasFiniteLinearSubfieldBounds p j ρres ∧
              HasOriginalSymmetricKernelConsequences p
                (ρres.comp (rationalArithmeticCyclotomicCharacter
                  ((Q * p : ℕ) : 𝓞 ℚ) p ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩).toMonoidHom.ker.subtype) ∧
              HasOriginalSymmetricKernelConsequences p
                ((ρres.comp (sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ)).toMonoidHom).comp
                  (sourceAbsoluteCyclotomicCharacter p).toMonoidHom.ker.subtype) ∧
              HasOriginalArithmeticSymmetricTwistedKernelDetection
                ((Q * p : ℕ) : 𝓞 ℚ) p ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩ ρres ∧
              HasOriginalArithmeticRegularPrimeDetection
                ((Q * p : ℕ) : 𝓞 ℚ) p ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩ ρres ∧
              HasOriginalArithmeticDetectingFamilies
                ((Q * p : ℕ) : 𝓞 ℚ) p ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩ ρres ∧
              HasOriginalArithmeticTorusPrimeDetection
                ((Q * p : ℕ) : 𝓞 ℚ) p ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩ ρres ∧
              HasOriginalArithmeticTorusFamilies
                ((Q * p : ℕ) : 𝓞 ℚ) p ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩ ρres ∧
              HasOriginalRationalCMConsequences ((Q * p : ℕ) : 𝓞 ℚ) p ρres))) ∧
        HasOriginalUnramifiedAdjointDimensions ((Q * p : ℕ) : 𝓞 ℚ) ρres ∧
        HasOriginalRationalCMPolarizations ((Q * p : ℕ) : 𝓞 ℚ) p ρres ∧
        ∀ e : Qbar →ₐ[ℚ] ℂ,
          let g := sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ)
            (sourceAbsoluteComplexConjugation e)
          (ρres g).val.det = -1 ∧ Matrix.trace (ρres g).val = 0 := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p (Fact.out : p.Prime)
  let F := rationalPrimeLocalField p (Fact.out : p.Prime)
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hs := exists_gammaOne_original_cm_kernel_consequences Q p f hk hlarge
  dsimp only at hs
  obtain ⟨u, v, hu, hv, hext, hfin, hfinite, hdiscrete, hchar,
    τ, ρint, ρres, hi, hr, hred, hdet, hmax, himage, hlocal, hclass, hdims, hodd⟩ := hs
  letI : UniformSpace L := u
  letI : TopologicalSpace L := u.toTopologicalSpace
  letI : ValuativeRel L := v
  letI : TopologicalSpace 𝓀[L] :=
    inferInstanceAs (TopologicalSpace (𝒪[L] ⧸ IsLocalRing.maximalIdeal 𝒪[L]))
  letI : CharP 𝓀[L] p := hchar
  letI : Finite 𝓀[L] := hfinite
  letI : Fact (2 < p) := ⟨by omega⟩
  refine ⟨u, v, hu, hv, hext, hfin, hfinite, hdiscrete, hchar,
    τ, ρint, ρres, hi, hr, hred, hdet, hmax, himage, hlocal, hclass, hdims, ?_, hodd⟩
  exact original_rational_cyclotomic_cm_polarizations
    ((Q * p : ℕ) : 𝓞 ℚ) p (k - 1).toNat
    ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩
    (original_primitive_determinantExponent_odd f hk) ρres hdet

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
