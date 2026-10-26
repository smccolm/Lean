import Dubon2026.SourcePrimitiveResidualGlobalDeterminant
import Dubon2026.SourceResidualRealDeterminant
import Dubon2026.SourcePrimitiveResidualCharacteristic

/-! DUB-17/18 -> all-weight original residual association. At every
prescribed rational prime, construct the genuine finite local coefficient
field and its prescribed-characteristic residue closure, then consume
the assembled original-support theorem. No coefficient field, residual
class, geometric branch, weight twist, or support comparison is supplied
as a hypothesis. Arithmetic automorphy and all-weight continuation are
separate remaining acceptance obligations. -/
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

theorem sourcePrimitive_exists_originalSupport_oddResidualGalois_charP
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
        let a : 𝓞 ℚ := (Q * p : ℕ)
           ∃ ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) (AlgebraicClosure 𝓀[L]),
             Continuous ρ ∧
             Matrix.GeneralLinearGroup.det.comp ρ =
               (sourceArithmeticCyclotomicUnitCharacter (F := AlgebraicClosure 𝓀[L]) p a
                 ⟨(Q : 𝓞 ℚ), by simp [a, mul_comm]⟩).toMonoidHom ^ (k - 1).toNat ∧
             (ρ (rationalRealArithmeticRestriction a Complex.conjAe)).val.det = -1 ∧
             (∀ (ell : sourceBinaryHeckePrime Q), ell.val ≠ p →
               ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
                 rationalPrimeLocalField ell.val ell.property.1),
                 (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
                   (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
                 Matrix.trace (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   algebraMap 𝓀[L] (AlgebraicClosure 𝓀[L]) (IsLocalRing.residue 𝒪[L]
                     ⟨τ (sourcePrimitiveFieldCoefficient f ell.val),
                       sourcePrimitiveCoefficient_valuation_le_one f hk τ ell.val⟩) ∧
                 Matrix.det (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   (ell.val : AlgebraicClosure 𝓀[L]) ^ (k - 1).toNat) ∧
             ∀ (ell : ℕ) (hell : ell.Prime), ¬ell ∣ Q → ell ≠ p →
               ∀ g ∈ rationalPrimeNormInertia ell hell,
                 ρ (rationalPrimeArithmeticRestriction a ell hell g) = 1 := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI := sourcePrimitiveCoefficientField_numberField f hk
  letI := rationalPrimeLocalField_charZero p hp
  let F := rationalPrimeLocalField p hp
  let L := commonCoefficientField (sourcePrimitiveCoefficientField f) F
  have hr := sourcePrimitive_exists_originalSupport_cyclotomicResidualGalois_charP f hk p hp
  dsimp only at hr
  rcases hr with ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, ρ, hρ, hdet, hFrob, hI⟩
  letI : UniformSpace L := u
  letI : TopologicalSpace L := u.toTopologicalSpace
  letI : ValuativeRel L := v
  letI : TopologicalSpace (AlgebraicClosure 𝓀[L]) := ⊥
  letI : Algebra 𝓀[L] (AlgebraicClosure 𝓀[L]) :=
    @AlgebraicClosure.instAlgebra 𝓀[L] _ 𝓀[L] _ (Algebra.id 𝓀[L])
  letI := hchar
  refine ⟨u, v, hu, hlocal, hext, hdim, hfinite, hchar, τ, ρ, hρ, hdet, ?_, hFrob, hI⟩
  have hodd : Odd (k - 1).toNat := by
    obtain ⟨n, hn⟩ := sourcePrimitive_binaryDegree_even f hk
    exact ⟨n, by omega⟩
  exact sourceArithmetic_real_det_of_cyclotomic p ((Q * p : ℕ) : 𝓞 ℚ)
    ⟨(Q : 𝓞 ℚ), by simp [mul_comm]⟩ (k - 1).toNat hodd ρ hdet

end
end Dubon2026
