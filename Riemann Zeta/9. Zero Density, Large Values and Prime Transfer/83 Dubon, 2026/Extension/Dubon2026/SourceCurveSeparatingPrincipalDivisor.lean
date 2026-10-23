import Dubon2026.SourceCurveSeparatingFunctionSupport
import Dubon2026.SourceCurveDivisors
import Dubon2026.SourceCurveTranscendence

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal divisors ->
degree-zero descent from a Galois closure. This is the literal finite
normalized-order divisor furnished by the separating-coordinate support
proof. Its multiplicative and inverse laws follow from actual place orders;
degree zero is proved separately, not built into this definition. -/
namespace Dubon2026.SourceCurve
noncomputable section
open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (t : F) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ F]
variable [Algebra.IsSeparable K⟮t⟯ F]

/-- The actual finite normalized-order divisor, using one finite separating coordinate. -/
def separatingPrincipalDivisor (f : F) : Divisor K F :=
  Finsupp.ofSupportFinite (fun v => v.ord f)
    (finite_function_support_of_separating_coordinate t ht f)

theorem separatingPrincipalDivisor_apply (f : F) (v : Place K F) :
    separatingPrincipalDivisor t ht f v = v.ord f := rfl

theorem separatingPrincipalDivisor_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :
    separatingPrincipalDivisor t ht (f * g) =
      separatingPrincipalDivisor t ht f + separatingPrincipalDivisor t ht g := by
  ext v
  exact v.ord_mul hf hg

theorem separatingPrincipalDivisor_inv (f : F) :
    separatingPrincipalDivisor t ht f⁻¹ = -separatingPrincipalDivisor t ht f := by
  ext v
  exact v.ord_inv f

theorem separatingPrincipalDivisor_algebraMap (c : K) :
    separatingPrincipalDivisor t ht (algebraMap K F c) = 0 := by
  ext v
  exact v.ord_eq_zero_of_isAlgebraic (isAlgebraic_algebraMap c)

end
end Dubon2026.SourceCurve
