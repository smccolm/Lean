import Dubon2026.SourceCurveTateCommutator
import Dubon2026.SourceCurveFiniteRankTraceAdd

/-! The multiplication defect of the local integral projection factors
through the already finite principal-part image. This supplies the finite
error terms in the residue Leibniz rule and avoids introducing a second
quotient factorization. Adapted from the local algebra in the verified FLT
`S_AlgebraicCurve_tateChainRule`, using the current actual projection. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Projected multiplication as an endomorphism of the integral image. -/
def piRestrict (p φ : V →ₗ[K] V) : LinearMap.range p →ₗ[K] LinearMap.range p :=
  (p ∘ₗ φ).restrict (fun x _ => mem_range_self p (φ x))

/-- Evaluation of projected multiplication. -/
theorem piRestrict_apply (p φ : V →ₗ[K] V) (a : LinearMap.range p) :
    (piRestrict p φ a : V) = p (φ (a : V)) := rfl

/-- The actual error in multiplying two projected multiplication operators. -/
def epsRestrict (p φ ψ : V →ₗ[K] V) : LinearMap.range p →ₗ[K] LinearMap.range p :=
  (p ∘ₗ φ ∘ₗ (LinearMap.id - p) ∘ₗ ψ).restrict (fun _ _ => mem_range_self p _)

/-- Evaluation of the multiplication defect through the principal part. -/
theorem epsRestrict_apply (p φ ψ : V →ₗ[K] V) (a : LinearMap.range p) :
    (epsRestrict p φ ψ a : V) = p (φ (ψ (a : V) - p (ψ (a : V)))) := rfl

/-- Projected multiplication of a product is the operator product plus its explicit defect. -/
theorem piRestrict_comp_eq (p φ ψ : V →ₗ[K] V) :
    piRestrict p (φ ∘ₗ ψ) = piRestrict p φ ∘ₗ piRestrict p ψ + epsRestrict p φ ψ := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change p (φ (ψ (a : V))) = p (φ (p (ψ (a : V)))) +
    p (φ (ψ (a : V) - p (ψ (a : V))))
  rw [map_sub, map_sub]
  abel

/-- The local Tate operator is precisely the commutator of projected multiplication. -/
theorem tateCommRestrict_eq_bracket (p f g : V →ₗ[K] V) :
    tateCommRestrict p f g = piRestrict p f ∘ₗ piRestrict p g -
      piRestrict p g ∘ₗ piRestrict p f := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  rfl

/-- Finite principal parts imply finite rank of the multiplication defect. -/
theorem finite_range_epsRestrict (p φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range
      ((LinearMap.id - p) ∘ₗ ψ ∘ₗ (LinearMap.range p).subtype))] :
    FiniteDimensional K (LinearMap.range (epsRestrict p φ ψ)) := by
  let g : V →ₗ[K] LinearMap.range p :=
    (p ∘ₗ φ).codRestrict (LinearMap.range p) (fun x => mem_range_self p _)
  have h : epsRestrict p φ ψ =
      g ∘ₗ ((LinearMap.id - p) ∘ₗ ψ ∘ₗ (LinearMap.range p).subtype) := by
    ext a
    rfl
  rw [h, LinearMap.range_comp]
  exact Module.Finite.map _ _

end Dubon2026.SourceCurve.ResidueTrace
