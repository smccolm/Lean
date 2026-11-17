import Dubon2026.SourceGammaOneResidualRankTwo
import Dubon2026.SourceOriginalResidualLocalInterface

/-! DUB-17/18 -> original residual association -> literal fixed local Hecke data.
The actual all-weight construction supplies the finite residue field,
integral and residual actions. The existing embedding comparison identifies
the fixed prime-local map, and the original Hecke character supplies the
exact polynomial. No residual action or Frobenius premise is supplied. -/
namespace Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
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

/-- The original all-weight residual action has finite image and the exact
Hecke characteristic polynomial under the fixed original local restriction. -/
theorem exists_gammaOne_original_fixedLocal_residual
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
      FiniteDimensional F L ∧ Finite 𝓀[L] ∧ DiscreteTopology 𝓀[L] ∧ CharP 𝓀[L] p ∧
      ∃ τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L,
      ∃ (ρint : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →*
          Matrix.GeneralLinearGroup (Fin 2) 𝒪[L])
        (ρres : rationalArithmeticGaloisGroup ((Q * p : ℕ) : 𝓞 ℚ) →*
          Matrix.GeneralLinearGroup (Fin 2) 𝓀[L]),
        Continuous ρint ∧ Continuous ρres ∧
        (∀ g i j, (ρres g).val i j = IsLocalRing.residue 𝒪[L] ((ρint g).val i j)) ∧
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
        ∀ e : Qbar →ₐ[ℚ] ℂ,
          let g := sourceAbsoluteArithmeticRestriction ((Q * p : ℕ) : 𝓞 ℚ)
            (sourceAbsoluteComplexConjugation e)
          (ρres g).val.det = -1 ∧ Matrix.trace (ρres g).val = 0 := by
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p (Fact.out : p.Prime)
  let F := rationalPrimeLocalField p (Fact.out : p.Prime)
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hs := exists_gammaOne_original_residual_rankTwo Q p f hk hlarge
  dsimp only at hs
  obtain ⟨u, v, hu, hv, hext, hfin, hfinite, hdiscrete, hchar,
    τ, ρint, ρres, hi, hr, hred, hFrob, hodd⟩ := hs
  letI : UniformSpace L := u
  letI : TopologicalSpace L := u.toTopologicalSpace
  letI : ValuativeRel L := v
  letI : IsNonarchimedeanLocalField L := hv
  letI : Finite 𝓀[L] := hfinite
  exact ⟨u, v, hu, hv, hext, hfin, hfinite, hdiscrete, hchar,
    τ, ρint, ρres, hi, hr, hred,
    sourcePrimitiveResidualHeckeCharacter_ker_isMaximal f hk τ,
    Set.toFinite _, originalResidualHecke_fixed_local_data Q p f hk τ ρres hFrob, hodd⟩

end
end Dubon2026.SourceFunctionField.GammaOne.CoefficientReduction
