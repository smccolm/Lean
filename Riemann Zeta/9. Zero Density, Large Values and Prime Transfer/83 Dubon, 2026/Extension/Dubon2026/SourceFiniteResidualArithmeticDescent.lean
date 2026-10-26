import Dubon2026.SourceFiniteResidualCoefficientField
import Dubon2026.SourceResidualCoefficientDeterminant
import Dubon2026.SourceResidualRealDeterminant
import Dubon2026.SourceBinaryH1HeckeAlgebra

/-! DUB-17/18 -> arithmetic automorphy -> finite residual coefficients.
Descend the same actual arithmetic representation and all its source local
and global equations before instantiating the primitive coefficient field. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric rationalPrimeOriginalClosureNorm
  rationalPrimeOriginalClosureNormedAlgebra rationalPrimeOriginalClosureNorm_ultrametric
  algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

theorem sourceArithmetic_exists_finiteCoefficient_realization
    {F K : Type} [Field F] [Finite F] [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] [TopologicalSpace K] [DiscreteTopology K]
    (Q p : ℕ) [NeZero p] [CharP F p] [CharP K p]
    (a : 𝓞 ℚ) (hpa : (p : 𝓞 ℚ) ∣ a) (j : ℕ)
    (theta : sourceBinaryHeckePrime Q → F)
    (ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) K)
    (hdata :
             Continuous ρ ∧
             Matrix.GeneralLinearGroup.det.comp ρ =
               (sourceArithmeticCyclotomicUnitCharacter (F := K) p a
                 hpa).toMonoidHom ^ j ∧
             (ρ (rationalRealArithmeticRestriction a Complex.conjAe)).val.det = -1 ∧
             (∀ (ell : sourceBinaryHeckePrime Q), ell.val ≠ p →
               ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
                 rationalPrimeLocalField ell.val ell.property.1),
                 (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
                   (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
                 Matrix.trace (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   algebraMap F K (theta ell) ∧
                 Matrix.det (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   (ell.val : K) ^ j) ∧
             ∀ (ell : ℕ) (hell : ell.Prime), ¬ell ∣ Q → ell ≠ p →
               ∀ g ∈ rationalPrimeNormInertia ell hell,
                 ρ (rationalPrimeArithmeticRestriction a ell hell g) = 1) :
    ∃ (S : IntermediateField F K), Finite S ∧
      ∃ hSchar : CharP S p, letI := hSchar
      ∃ η : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) S,
             Continuous η ∧
             Matrix.GeneralLinearGroup.det.comp η =
               (sourceArithmeticCyclotomicUnitCharacter (F := S) p a
                 hpa).toMonoidHom ^ j ∧
             (η (rationalRealArithmeticRestriction a Complex.conjAe)).val.det = -1 ∧
             (∀ (ell : sourceBinaryHeckePrime Q), ell.val ≠ p →
               ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
                 rationalPrimeLocalField ell.val ell.property.1),
                 (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
                   (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
                 Matrix.trace (η (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   algebraMap F S (theta ell) ∧
                 Matrix.det (η (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
                   (ell.val : S) ^ j) ∧
             ∀ (ell : ℕ) (hell : ell.Prime), ¬ell ∣ Q → ell ≠ p →
               ∀ g ∈ rationalPrimeNormInertia ell hell,
                 η (rationalPrimeArithmeticRestriction a ell hell g) = 1 := by
  rcases hdata with ⟨hρ, hdet, hodd, hFrob, hI⟩
  have hfin : (Set.range ρ).Finite := (isCompact_range hρ).finite_of_discrete
  obtain ⟨S, hS, η, hη, hmap⟩ :=
    sourceFiniteImage_exists_finiteCoefficientField (F := F) ρ hρ hfin
  letI : CharP S p := (Algebra.charP_iff F S p).mp inferInstance
  have hmat (g) : (RingHom.mapMatrix S.val.toRingHom) (η g).val = (ρ g).val :=
    congrArg Units.val (DFunLike.congr_fun hmap g)
  have htr (g) : S.val.toRingHom (Matrix.trace (η g).val) = Matrix.trace (ρ g).val := by
    rw [AddMonoidHom.map_trace]
    exact congrArg Matrix.trace (hmat g)
  have hdt (g) : S.val.toRingHom (η g).val.det = (ρ g).val.det := by
    change S.val.toRingHom (η g).val.det = _
    rw [RingHom.map_det]
    exact congrArg Matrix.det (hmat g)
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := Fin 2) S.val.toRingHom) := by
    intro x y hxy
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    apply Subtype.ext
    exact congrArg (fun z : Matrix.GeneralLinearGroup (Fin 2) (K) =>
      z.val i j) hxy
  refine ⟨S, hS, inferInstance, η, hη, ?_, ?_, ?_, ?_⟩
  · exact sourceArithmetic_cyclotomic_determinant_coefficient_descent p
      a hpa j S.val.toRingHom η ρ hmap hdet
  · apply S.val.injective
    rw [hdt, hodd, map_neg, map_one]
  · intro ell hellp g hg
    have hf := hFrob ell hellp g hg
    constructor
    · apply S.val.injective
      rw [htr]
      exact hf.1.trans (S.val.commutes (theta ell)).symm
    · apply S.val.injective
      rw [hdt, map_pow, map_natCast]
      exact hf.2
  · intro ell hell hellQ hellp g hg
    apply hinj
    change ((Matrix.GeneralLinearGroup.map S.val.toRingHom).comp η)
      (rationalPrimeArithmeticRestriction _ ell hell g) = _
    rw [hmap, hI ell hell hellQ hellp g hg, map_one]


end
end Dubon2026
