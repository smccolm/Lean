import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! DUB-17/18 -> higher symmetric-power continuation -> original Frobenius/inertia
-> modular-curve good reduction -> reverse genus bound -> canonical degree
-> global residues -> residue/trace compatibility. The finite-rank trace is
computed on its actual image. Cyclicity and independence of a larger finite
space are the linear algebra needed by the local residue comparison.
Adapted from the verified FLT archive, `S_AlgebraicCurve_tateAgreement`;
native finite-dimensional trace supplies the entire trace calculation. -/

noncomputable section

namespace Dubon2026.SourceCurve.ResidueTrace

open LinearMap Submodule

variable {K V M N : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- The trace of a finite-rank endomorphism on its actual image. -/
def finrankTrace (φ : V →ₗ[K] V) : K :=
  LinearMap.trace K (LinearMap.range φ)
    (φ.restrict (fun x _ => LinearMap.mem_range_self φ x))

/-- The first map carries the range of one composite into that of the other. -/
theorem range_comp_map_left (f : M →ₗ[K] N) (g : N →ₗ[K] M) :
    ∀ x ∈ LinearMap.range (g ∘ₗ f), f x ∈ LinearMap.range (f ∘ₗ g) := by
  rintro x ⟨y, rfl⟩
  exact ⟨f y, rfl⟩

/-- Cyclicity uses only the finite images, even when both ambient spaces are infinite. -/
theorem finrankTrace_comp_comm (f : M →ₗ[K] N) (g : N →ₗ[K] M)
    [FiniteDimensional K (LinearMap.range (g ∘ₗ f))]
    [FiniteDimensional K (LinearMap.range (f ∘ₗ g))] :
    finrankTrace (g ∘ₗ f) = finrankTrace (f ∘ₗ g) := by
  let fR : LinearMap.range (g ∘ₗ f) →ₗ[K] LinearMap.range (f ∘ₗ g) :=
    f.restrict (range_comp_map_left f g)
  let gR : LinearMap.range (f ∘ₗ g) →ₗ[K] LinearMap.range (g ∘ₗ f) :=
    g.restrict (range_comp_map_left g f)
  have hgf : (g ∘ₗ f).restrict (fun x _ => mem_range_self _ x) = gR ∘ₗ fR := by
    ext x
    rfl
  have hfg : (f ∘ₗ g).restrict (fun x _ => mem_range_self _ x) = fR ∘ₗ gR := by
    ext x
    rfl
  unfold finrankTrace
  rw [hgf, hfg, LinearMap.trace_comp_comm']

/-- Any finite-dimensional space containing the image computes the same trace. -/
theorem finrankTrace_eq_trace_on_superspace
    (φ : V →ₗ[K] V) [FiniteDimensional K (LinearMap.range φ)]
    (W : Submodule K V) [FiniteDimensional K W]
    (hrange : LinearMap.range φ ≤ W) (hW : ∀ x ∈ W, φ x ∈ W) :
    finrankTrace φ = LinearMap.trace K W (φ.restrict hW) := by
  let i : LinearMap.range φ →ₗ[K] W := Submodule.inclusion hrange
  let π : W →ₗ[K] LinearMap.range φ :=
    { toFun := fun w => ⟨φ (w : V), mem_range_self φ (w : V)⟩
      map_add' := fun _ _ => by simp
      map_smul' := fun _ _ => by simp }
  have hip : i ∘ₗ π = φ.restrict hW := by ext; rfl
  have hpi : π ∘ₗ i = φ.restrict (fun x _ => mem_range_self φ x) := by ext; rfl
  unfold finrankTrace
  rw [← hpi, ← hip, LinearMap.trace_comp_comm']

/-- Conjugation sends the actual image to its image under the equivalence. -/
theorem range_conj_eq_map (e : M ≃ₗ[K] N) (φ : M →ₗ[K] M) :
    LinearMap.range (e.conj φ) = (LinearMap.range φ).map (e : M →ₗ[K] N) := by
  rw [LinearEquiv.conj_apply, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearMap.range_comp]

/-- The finite-rank trace is unchanged by changing linear coordinates. -/
theorem finrankTrace_conj (e : M ≃ₗ[K] N) (φ : M →ₗ[K] M)
    [FiniteDimensional K (LinearMap.range φ)] :
    haveI : FiniteDimensional K (LinearMap.range (e.conj φ)) := by
      rw [range_conj_eq_map]
      exact (Submodule.equivMapOfInjective _ e.injective _).finiteDimensional
    finrankTrace (e.conj φ) = finrankTrace φ := by
  haveI : FiniteDimensional K (LinearMap.range (e.conj φ)) := by
    rw [range_conj_eq_map]
    exact (Submodule.equivMapOfInjective _ e.injective _).finiteDimensional
  have hgf : ((e : M →ₗ[K] N) ∘ₗ φ) ∘ₗ (e.symm : N →ₗ[K] M) = e.conj φ := by
    ext x
    rfl
  have hfg : (e.symm : N →ₗ[K] M) ∘ₗ ((e : M →ₗ[K] N) ∘ₗ φ) = φ := by
    ext x
    exact e.symm_apply_apply _
  haveI : FiniteDimensional K
      (LinearMap.range (((e : M →ₗ[K] N) ∘ₗ φ) ∘ₗ (e.symm : N →ₗ[K] M))) := by
    rw [hgf]
    infer_instance
  haveI : FiniteDimensional K
      (LinearMap.range ((e.symm : N →ₗ[K] M) ∘ₗ ((e : M →ₗ[K] N) ∘ₗ φ))) := by
    rw [hfg]
    infer_instance
  simpa only [hfg, hgf] using
    (finrankTrace_comp_comm ((e : M →ₗ[K] N) ∘ₗ φ) (e.symm : N →ₗ[K] M)).symm

end Dubon2026.SourceCurve.ResidueTrace
