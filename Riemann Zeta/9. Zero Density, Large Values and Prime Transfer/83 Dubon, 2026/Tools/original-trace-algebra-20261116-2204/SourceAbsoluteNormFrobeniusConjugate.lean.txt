import Dubon2026.ChebotarevRationalPrime
import Dubon2026.RationalNormFrobeniusClass
import Dubon2026.SourceRationalLocalFrobenius
import Dubon2026.SourceRationalLocalClosureEmbedding

/-! DUB-17/18 -> original all-weight association -> central finite traces.
Reuse native Chebotarev and original norm Frobenius to realize any finite
continuous Galois image by an actual local Frobenius, up to conjugation
by an actual global Galois element. This preserves the original local
embedding and avoids assuming density for an unspecified Frobenius family. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois
private local instance (F : FiniteGaloisIntermediateField ℚ Qbar) : Algebra ℚ F := F.algebra'

/-- Native finite-factor Chebotarev produces a genuine norm-residue Frobenius
outside any finite set, with conjugator in the original absolute Galois group. -/
theorem absolute_continuous_exists_norm_frobenius_conjugate
    {T : Type} [Group T] [TopologicalSpace T] [DiscreteTopology T]
    (χ : Gal(Qbar/ℚ) →ₜ* T) (g : Gal(Qbar/ℚ)) (S : Finset ℕ) :
    ∃ (q : ℕ) (hq : q.Prime), q ∉ S ∧
      ∃ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
        (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) ∧
        ∃ τ : Gal(Qbar/ℚ),
          χ (τ * embeddedNormalGaloisRestriction e φ * τ⁻¹) = χ g := by
  obtain ⟨F, ψ, hψ, hF⟩ := continuous_rational_galois_exists_frobenius_prime χ
  letI : NumberField F := NumberField.of_module_finite ℚ F
  letI : IsGalois ℚ F := F.isGalois
  letI : @IsGalois ℚ _ F _ DivisionRing.toRatAlgebra := by
    have he : F.algebra' = (DivisionRing.toRatAlgebra : Algebra ℚ F) := Subsingleton.elim _ _
    exact Eq.mp (congrArg (fun α : Algebra ℚ F => @IsGalois ℚ _ F _ α) he) F.isGalois
  letI : @Normal ℚ F _ _ DivisionRing.toRatAlgebra := inferInstance
  obtain ⟨q, hq, hqS, hunr, hclass, _⟩ := hF g S
  obtain ⟨e⟩ := sourceRationalLocalClosure_nonempty_embedding q hq
  obtain ⟨φ, hφ⟩ := rationalPrimeOriginalNorm_exists_frobenius q hq
  let d := embeddedNormalGaloisRestriction e φ
  let ef : F →+* rationalPrimeLocalClosure q hq := e.toRingHom.comp (algebraMap F Qbar)
  have he (x : F) : ef ((AlgEquiv.restrictNormalHom F d) x) = φ (ef x) := by
    exact (congrArg e (d.restrictNormal_commutes F x)).trans
      (embeddedNormalGaloisRestriction_commutes e φ (algebraMap F Qbar x))
  have hc := algebraicLocal_frobenius_class_of_original_residue (F := F) ef q hq
    (rationalPrimeOriginalClosureNorm_prime_lt_one q hq) hunr
    (AlgEquiv.restrictNormalHom F d) φ he hφ
  have hi : IsConj (AlgEquiv.restrictNormalHom F d) (AlgEquiv.restrictNormalHom F g) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (hc.symm.trans hclass)
  obtain ⟨t, ht⟩ := isConj_iff.mp hi
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := F) Qbar t
  refine ⟨q, hq, hqS, e, φ, hφ, τ, ?_⟩
  rw [← hψ, ← hψ]
  apply congrArg ψ
  simp only [map_mul, map_inv]
  rw [hτ]
  exact ht

end
end Dubon2026
