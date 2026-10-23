import Dubon2026.SourceCurveMappedSeparatingCoordinate

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal-divisor
degree zero -> Galois-closure descent. Finite separable extensions of the
actual rational field inherit a separating coordinate, finite order
divisors, and closed constant residues. The latter two are constructed
here without assuming principal-divisor degree zero. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField
attribute [local instance] rational_coordinate_finite rational_coordinate_separable

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
variable [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
variable [FiniteDimensional (RatFunc K) E] [Algebra.IsSeparable (RatFunc K) E]

theorem finite_rational_extension_divisor_support (f : E) :
    {v : Place K E | v.ord f ≠ 0}.Finite := by
  obtain ⟨hfinite, hsep⟩ := finite_separable_mapped_coordinate (K := K) (E := E)
    (RatFunc.X : RatFunc K)
  have ht : Transcendental K (algebraMap (RatFunc K) E RatFunc.X) :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc K) E).injective).mpr RatFunc.transcendental_X
  exact finite_function_support_of_separating_coordinate _ ht f

/-- The actual finite normalized-order divisor in a finite separable rational-field extension. -/
def rationalExtensionPrincipalDivisor (f : E) : Divisor K E :=
  Finsupp.ofSupportFinite (fun v => v.ord f) (finite_rational_extension_divisor_support K E f)

theorem rationalExtensionPrincipalDivisor_apply (f : E) (v : Place K E) :
    rationalExtensionPrincipalDivisor K E f v = v.ord f := rfl

theorem rational_extension_place_residue_bijective [IsAlgClosed K] (v : Place K E) :
    Function.Bijective (algebraMap K v.ResidueField) := by
  obtain ⟨hfinite, _⟩ := finite_separable_mapped_coordinate (K := K) (E := E)
    (RatFunc.X : RatFunc K)
  exact place_residue_bijective_of_finite_coordinate
    (algebraMap (RatFunc K) E RatFunc.X) v

end
end Dubon2026.SourceCurve
