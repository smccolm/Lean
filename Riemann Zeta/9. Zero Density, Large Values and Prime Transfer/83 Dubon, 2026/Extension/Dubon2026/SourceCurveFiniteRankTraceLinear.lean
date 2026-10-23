import Dubon2026.SourceCurveFiniteRankTrace

/-! The linearity required for the residue/trace comparison in the canonical
degree step of DUB-17/18. Every trace is computed on a proved finite image;
comparison on the sum of two images reduces additivity to native trace. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The range of a difference lies in the sum of the two ranges. -/
theorem range_sub_le (φ ψ : V →ₗ[K] V) :
    LinearMap.range (φ - ψ) ≤ LinearMap.range φ ⊔ LinearMap.range ψ := by
  rintro x ⟨y, rfl⟩
  exact sub_mem (Submodule.mem_sup_left (mem_range_self φ y))
    (Submodule.mem_sup_right (mem_range_self ψ y))

/-- Differences of finite-rank endomorphisms have finite rank. -/
theorem finite_range_sub (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    FiniteDimensional K (LinearMap.range (φ - ψ)) := by
  haveI := Submodule.finiteDimensional_sup (LinearMap.range φ) (LinearMap.range ψ)
  exact Submodule.finiteDimensional_of_le (range_sub_le φ ψ)

/-- Subtraction of traces holds on an infinite ambient vector space. -/
theorem finrankTrace_sub (φ ψ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)]
    [FiniteDimensional K (LinearMap.range ψ)] :
    haveI := finite_range_sub φ ψ
    finrankTrace (φ - ψ) = finrankTrace φ - finrankTrace ψ := by
  haveI := finite_range_sub φ ψ
  let W : Submodule K V := LinearMap.range φ ⊔ LinearMap.range ψ
  haveI : FiniteDimensional K W := Submodule.finiteDimensional_sup _ _
  have hφ : ∀ x ∈ W, φ x ∈ W := fun x _ =>
    Submodule.mem_sup_left (mem_range_self φ x)
  have hψ : ∀ x ∈ W, ψ x ∈ W := fun x _ =>
    Submodule.mem_sup_right (mem_range_self ψ x)
  have hsub : ∀ x ∈ W, (φ - ψ) x ∈ W := fun x hx => sub_mem (hφ x hx) (hψ x hx)
  rw [finrankTrace_eq_trace_on_superspace (φ - ψ) W (range_sub_le φ ψ) hsub,
    finrankTrace_eq_trace_on_superspace φ W le_sup_left hφ,
    finrankTrace_eq_trace_on_superspace ψ W le_sup_right hψ, ← map_sub]
  congr 1

/-- The zero endomorphism has finite-dimensional image. -/
theorem finite_range_zero : FiniteDimensional K (LinearMap.range (0 : V →ₗ[K] V)) := by
  rw [LinearMap.range_zero]
  infer_instance

/-- The finite-rank trace of zero is zero. -/
theorem finrankTrace_zero :
    haveI := finite_range_zero (K := K) (V := V)
    finrankTrace (0 : V →ₗ[K] V) = 0 := by
  unfold finrankTrace
  have h : (0 : V →ₗ[K] V).restrict (p := LinearMap.range (0 : V →ₗ[K] V))
      (fun x _ => mem_range_self _ x) = 0 := by
    ext
    rfl
  rw [h, map_zero]

/-- The image of a scalar multiple remains in the original image. -/
theorem range_smul_le (c : K) (φ : V →ₗ[K] V) :
    LinearMap.range (c • φ) ≤ LinearMap.range φ := by
  rintro x ⟨y, rfl⟩
  exact Submodule.smul_mem _ c (mem_range_self φ y)

/-- Scalar multiplication preserves finite rank. -/
theorem finite_range_smul (c : K) (φ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)] :
    FiniteDimensional K (LinearMap.range (c • φ)) :=
  Submodule.finiteDimensional_of_le (range_smul_le c φ)

/-- The finite-rank trace respects scalar multiplication in any characteristic. -/
theorem finrankTrace_smul (c : K) (φ : V →ₗ[K] V)
    [FiniteDimensional K (LinearMap.range φ)] :
    haveI := finite_range_smul c φ
    finrankTrace (c • φ) = c • finrankTrace φ := by
  haveI := finite_range_smul c φ
  have h : ∀ x ∈ LinearMap.range φ, (c • φ) x ∈ LinearMap.range φ :=
    fun x _ => Submodule.smul_mem _ c (mem_range_self φ x)
  rw [finrankTrace_eq_trace_on_superspace (c • φ) (LinearMap.range φ)
    (range_smul_le c φ) h]
  unfold finrankTrace
  rw [← map_smul]
  congr 1

end Dubon2026.SourceCurve.ResidueTrace
