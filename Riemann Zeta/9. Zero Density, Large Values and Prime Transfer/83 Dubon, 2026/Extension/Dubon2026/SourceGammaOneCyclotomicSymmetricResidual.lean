import Dubon2026.SourceGammaOneAbsoluteSymmetricResidual
import Dubon2026.SourceFiniteLinearKernelSymmetric

/-! DUB-17/18 -> actual original residual image -> projective classification and finite coefficient realization and absolute symmetric-power irreducibility before and after cyclotomic-kernel restriction in the large-image branch.
This consumer constructs the actual original integral/residual actions and then
classifies their embedded projective image, preserving the fixed-local data,
global cyclotomic determinant and oddness. Arithmetic exclusions remain open. -/
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

/-- The actual original residual action has projective classification and finite coefficient realization and absolute symmetric-power irreducibility before and after cyclotomic-kernel restriction in the large-image branch
and retains its integral origin, fixed-local Hecke data, determinant and oddness. -/
theorem exists_gammaOne_original_cyclotomic_symmetric_residual
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
              (∃ E : IntermediateField (ZMod p) (K p), Finite E ∧
      ∃ (jE : 𝓀[L] →+* E) (B : GL (Fin 2) E), E.subtype.comp jE = j ∧
        ∀ (n : ℕ), 2 * n < p - 1 →
          ∀ (L' : Type) (_ : Field L') (_ : Algebra E L'),
            Representation.IsIrreducible (matrixStandardRepresentation
              (matrixCoefficientExtension (L := L') ((homogeneousSymmetricGL n).comp
                ((MulEquiv.toMonoidHom (MulAut.conj B)).comp
                  ((GeneralLinearGroup.map jE).comp ρres)))))) ∧
              (∃ E : IntermediateField (ZMod p) (K p), Finite E ∧
      ∃ (jE : 𝓀[L] →+* E) (B : GL (Fin 2) E), E.subtype.comp jE = j ∧
        let ρresE := (MulEquiv.toMonoidHom (MulAut.conj B)).comp
          ((GeneralLinearGroup.map jE).comp ρres)
        ∀ (n : ℕ), 2 * n < p - 1 →
          ∀ (L' : Type) (_ : Field L') (_ : Algebra E L'),
            Representation.IsIrreducible (matrixStandardRepresentation
              (matrixCoefficientExtension (L := L')
                ((homogeneousSymmetricGL n).comp (ρresE.comp ((sourceArithmeticCyclotomicUnitCharacter (F := 𝓀[L]) p
             ((Q * p : ℕ) : 𝓞 ℚ) ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩).toMonoidHom).ker.subtype)))))))) ∧
        ∀ e : Qbar →ₐ[ℚ] ℂ,
          let g := sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ)
            (sourceAbsoluteComplexConjugation e)
          (ρres g).val.det = -1 ∧ Matrix.trace (ρres g).val = 0 := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p (Fact.out : p.Prime)
  let F := rationalPrimeLocalField p (Fact.out : p.Prime)
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hs := exists_gammaOne_original_absolute_symmetric_residual Q p f hk hlarge
  dsimp only at hs
  obtain ⟨u, v, hu, hv, hext, hfin, hfinite, hdiscrete, hchar,
    τ, ρint, ρres, hi, hr, hred, hdet, hmax, himage, hlocal, hclass, hodd⟩ := hs
  letI : UniformSpace L := u
  letI : TopologicalSpace L := u.toTopologicalSpace
  letI : ValuativeRel L := v
  letI : TopologicalSpace 𝓀[L] :=
    inferInstanceAs (TopologicalSpace (𝒪[L] ⧸ IsLocalRing.maximalIdeal 𝒪[L]))
  letI : CharP 𝓀[L] p := hchar
  letI : Finite 𝓀[L] := hfinite
  refine ⟨u, v, hu, hv, hext, hfin, hfinite, hdiscrete, hchar,
    τ, ρint, ρres, hi, hr, hred, hdet, hmax, himage, hlocal, ?_, hodd⟩
  obtain ⟨j, hj, hAlt⟩ := hclass
  exact ⟨j, hj, hAlt.elim Or.inl (fun ha =>
    Or.inr ⟨ha.1, ha.2,
      finite_linear_bounds_kernel_absolute_symmetric_irreducibility p j ρres
        (sourceArithmeticCyclotomicUnitCharacter (F := 𝓀[L]) p
             ((Q * p : ℕ) : 𝓞 ℚ) ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩).toMonoidHom hlarge ha.1⟩)⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
