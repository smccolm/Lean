import Dubon2026.SourceCurveFiniteRankTraceLinear

/-! The finite-rank trace identities required to kill the error commutators
in the local residue Leibniz rule. Every required finite image is derived
from sums, compositions and the original finite-rank factor. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The range of a sum lies in the sum of the ranges. -/
theorem range_add_le (φ ψ : V →ₗ[K] V) :
    LinearMap.range (φ + ψ) ≤ LinearMap.range φ ⊔ LinearMap.range ψ := by
  rintro x ⟨y, rfl⟩
  exact add_mem (Submodule.mem_sup_left (mem_range_self φ y))
    (Submodule.mem_sup_right (mem_range_self ψ y))

/-- Sums of finite-rank operators have finite rank. -/
theorem finite_range_add (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ + ψ)) := by
  haveI := Submodule.finiteDimensional_sup (LinearMap.range φ) (LinearMap.range ψ)
  exact Submodule.finiteDimensional_of_le (range_add_le φ ψ)

/-- Finite-rank trace is additive on an arbitrary ambient vector space. -/
theorem finrankTrace_add (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace (φ + ψ) = finrankTrace φ + finrankTrace ψ := by
  haveI := finite_range_add φ ψ
  let W : Submodule K V := LinearMap.range φ ⊔ LinearMap.range ψ
  haveI : FiniteDimensional K W := Submodule.finiteDimensional_sup _ _
  have hφ : ∀ x ∈ W, φ x ∈ W := fun x _ => Submodule.mem_sup_left (mem_range_self φ x)
  have hψ : ∀ x ∈ W, ψ x ∈ W := fun x _ => Submodule.mem_sup_right (mem_range_self ψ x)
  have hsum : ∀ x ∈ W, (φ + ψ) x ∈ W := fun x hx => add_mem (hφ x hx) (hψ x hx)
  rw [finrankTrace_eq_trace_on_superspace (φ + ψ) W (range_add_le φ ψ) hsum,
    finrankTrace_eq_trace_on_superspace φ W le_sup_left hφ,
    finrankTrace_eq_trace_on_superspace ψ W le_sup_right hψ, ← map_add]
  congr 1

/-- Postcomposing a finite-rank operator preserves finite rank. -/
theorem finite_range_comp_right (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ ∘ₗ ψ)) := by
  rw [LinearMap.range_comp]
  exact Module.Finite.map _ _

/-- Precomposing a finite-rank operator preserves finite rank. -/
theorem finite_range_comp_left (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (ψ ∘ₗ φ)) :=
  Submodule.finiteDimensional_of_le (LinearMap.range_comp_le_range _ _)

/-- A commutator with a finite-rank right factor has zero finite-rank trace. -/
theorem finrankTrace_commutator_eq_zero (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range ψ)] :
    finrankTrace (φ ∘ₗ ψ - ψ ∘ₗ φ) = 0 := by
  haveI := finite_range_comp_right φ ψ
  haveI := finite_range_comp_left φ ψ
  rw [finrankTrace_sub, finrankTrace_comp_comm ψ φ, sub_self]

/-- The same vanishing holds when the left factor has finite rank. -/
theorem finrankTrace_commutator_eq_zero_left (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)] :
    finrankTrace (φ ∘ₗ ψ - ψ ∘ₗ φ) = 0 := by
  haveI := finite_range_comp_right ψ φ
  haveI := finite_range_comp_left ψ φ
  rw [finrankTrace_sub, finrankTrace_comp_comm ψ φ, sub_self]

end Dubon2026.SourceCurve.ResidueTrace
