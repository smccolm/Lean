import Dubon2026.SourcePrimitiveResidualOddness
import Dubon2026.SourceFiniteResidualArithmeticDescent
import Dubon2026.SourcePrimitiveResidualCharacteristic

/-! DUB-17/18 -> arithmetic automorphy -> actual finite residual coefficients.
The original primitive form in every weight at least two supplies a
continuous representation over a constructed finite field of the
prescribed characteristic. Abstract coefficient descent preserves the
same original Fourier reductions, cyclotomic determinant, actual real
determinant and good-prime inertia. Adic realization, local/image
properties and literal higher continuation remain separate obligations. -/
namespace Dubon2026
noncomputable section
open scoped NumberField ValuativeRel
open CongruenceSubgroup groupCohomology SourceCuspBoundary
attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric rationalPrimeOriginalClosureNorm
  rationalPrimeOriginalClosureNormedAlgebra rationalPrimeOriginalClosureNorm_ultrametric
  algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
variable {Q : ℕ} [NeZero Q] {k : ℤ}

theorem sourcePrimitive_exists_originalSupport_finiteResidualGalois_charP
    (f : PrimitiveCuspForm Q k) (hk : 2 ≤ k) (p : ℕ) (hp : p.Prime) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI := sourcePrimitiveCoefficientField_numberField f hk
    letI := rationalPrimeLocalField_charZero p hp
    let F := rationalPrimeLocalField p hp
    let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
    ∃ (u : UniformSpace L) (_ : ValuativeRel L),
      letI : TopologicalSpace L := u.toTopologicalSpace
      letI : TopologicalSpace (AlgebraicClosure 𝓀[L]) := ⊥
      letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
        @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
      IsUniformAddGroup L ∧ IsNonarchimedeanLocalField L ∧
      (ValuativeRel.valuation F).HasExtension (ValuativeRel.valuation L) ∧
      FiniteDimensional F L ∧ Finite 𝓀[L] ∧
      ∃ hchar : CharP (AlgebraicClosure 𝓀[L]) p,
      letI := hchar
      ∃ (τ : sourcePrimitiveCoefficientField f →ₐ[ℚ] L),
        ∃ (S : IntermediateField 𝓀[L] (AlgebraicClosure 𝓀[L])),
          letI : Algebra 𝓀[L] S := S.toSubalgebra.algebra
          Finite S ∧ ∃ hSchar : CharP S p,
          letI := hSchar
        let a : 𝓞 ℚ := (Q * p : ℕ)
           ∃ ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) (S),
             Continuous ρ ∧
             Matrix.GeneralLinearGroup.det.comp ρ =
               (sourceArithmeticCyclotomicUnitCharacter (F := S) p a
                 ⟨(Q : 𝓞 ℚ), by simp [a, mul_comm]⟩).toMonoidHom ^ (k - 1).toNat ∧
             (ρ (rationalRealArithmeticRestriction a Complex.conjAe)).val.det = -1 ∧
             (∀ (ell : sourceBinaryHeckePrime Q), ell.val ≠ p →
               ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
                 rationalPrimeLocalField ell.val ell.property.1),
                 (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
                   (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
                 Matrix.trace (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   algebraMap 𝓀[L] (S) (IsLocalRing.residue 𝒪[L]
                     ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
                       sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩) ∧
                 Matrix.det (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   (ell.val : S) ^ (k - 1).toNat) ∧
             ∀ (ell : ℕ) (hell : ell.Prime), ¬ell ∣ Q → ell ≠ p →
               ∀ g ∈ rationalPrimeNormInertia ell hell,
                 ρ (rationalPrimeArithmeticRestriction a ell hell g) = 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hr := sourcePrimitive_exists_originalSupport_oddResidualGalois_charP f hk p hp
  dsimp only at hr
  rcases hr with ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, ρ, hρ, hdet, hodd, hFrob, hI⟩
  letI : UniformSpace L := u
  letI : TopologicalSpace L := u.toTopologicalSpace
  letI : ValuativeRel L := v
  letI : TopologicalSpace (AlgebraicClosure 𝓀[L]) := ⊥
  letI : DiscreteTopology (AlgebraicClosure 𝓀[L]) := ⟨rfl⟩
  letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
    @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
  letI := hchar
  letI : CharP 𝓀[L] p :=
    (Algebra.charP_iff 𝓀[L] (AlgebraicClosure 𝓀[L]) p).mpr hchar
  letI : Finite 𝓀[L] := hfinite
  refine ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, ?_⟩
  exact sourceArithmetic_exists_finiteCoefficient_realization
    (F := 𝓀[L]) (K := AlgebraicClosure 𝓀[L]) Q p
    ((Q * p : ℕ) : 𝓞 ℚ) ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩
    (k - 1).toNat
    (fun ell => IsLocalRing.residue 𝒪[L]
      ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
        sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩)
    ρ ⟨hρ, hdet, hodd, hFrob, hI⟩

end
end Dubon2026
