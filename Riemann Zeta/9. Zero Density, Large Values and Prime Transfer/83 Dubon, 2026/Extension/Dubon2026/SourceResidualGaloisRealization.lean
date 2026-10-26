import Dubon2026.SourceParabolicArithmeticResidual
import Dubon2026.SourceResidualGaloisAlternative

/-! DUB-17/18 -> all-weight residual association -> close the original
weight-two alternative. The parabolic branch now consumes its actual H1
lift through the primitive divisor and prescribed arithmetic realization.
The already proved Dirichlet branch is retained. Every actual nonzero
residual H1 eigensystem therefore gives a genuine arithmetic Galois
representation with its exact original local trace, determinant and
inertia conditions. No parabolic/Galois alternative remains. -/
namespace Dubon2026
noncomputable section
open scoped NumberField
open CongruenceSubgroup groupCohomology SourceCuspBoundary
attribute [local instance] rationalPrimeLocalField_charZero rationalPrimeOriginalNorm
  rationalPrimeOriginalNorm_ultrametric rationalPrimeOriginalClosureNorm
  rationalPrimeOriginalClosureNormedAlgebra rationalPrimeOriginalClosureNorm_ultrametric
  algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField

theorem sourceTrivialH1Eigen_exists_galoisRep
    (F : Type) [Field F] [IsAlgClosed F] [TopologicalSpace F] [DiscreteTopology F]
    (N p : ℕ) [NeZero N] (hp : p.Prime) [CharP F p]
    (values : sourceBinaryHeckePrime N → F)
    (x : H1 (Rep.trivial F (Gamma0 N) F)) (hx : x ≠ 0)
    (heig : ∀ ell, sourceTrivialCoefficientHeckeOperators F N ell x = values ell • x) :
    let a : 𝓞 ℚ := (N * p : ℕ)
     ∃ ρ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup (Fin 2) F,
       Continuous ρ ∧
       (∀ (ell : sourceBinaryHeckePrime N), ell.val ≠ p →
         ∀ g : Gal(rationalPrimeLocalClosure ell.val ell.property.1 /
           rationalPrimeLocalField ell.val ell.property.1),
           (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
             (rationalPrimeLocalClosure ell.val ell.property.1)), g • z = z ^ ell.val) →
           Matrix.trace (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
             values ell ∧
           Matrix.det (ρ (rationalPrimeArithmeticRestriction a ell.val ell.property.1 g)).val =
             (ell.val : F)) ∧
       ∀ (ell : ℕ) (hell : ell.Prime), ¬ell ∣ N → ell ≠ p →
         ∀ g ∈ rationalPrimeNormInertia ell hell,
           ρ (rationalPrimeArithmeticRestriction a ell hell g) = 1 := by
  have hsrc := sourceTrivialH1Eigen_parabolicLift_or_galoisRep F N p hp values x hx heig
  rcases hsrc with hlift | hrep
  · rcases hlift with ⟨θ, φ, v, hv, hpar, he, hres⟩
    have hgeo := sourceTrivialParabolicEigen_prescribed_galoisRep N p hp F θ φ v hv hpar he
    rcases hgeo with ⟨ρ, hc, _, hFrob, hI⟩
    refine ⟨ρ, hc, ?_, hI⟩
    intro ell hep g hg
    have hh := (hFrob ell hep g hg).2
    rwa [hres ell] at hh
  · exact hrep

end
end Dubon2026
