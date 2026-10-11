import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Original denominator bounds between a full basis lattice and a finite module -/

namespace Dubon2026
noncomputable section

open scoped nonZeroDivisors

variable {R K V ι : Type} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [AddCommGroup V]
  [Module K V] [Module R V] [IsScalarTower R K V] [Finite ι]

/-- Clear the finitely many original coordinates of a finite generating
family. One nonzero original base denominator sends the whole finite module
into the original lattice spanned by the displayed field basis. -/
theorem fullBasis_span_absorbs_finite_submodule
    (b : Module.Basis ι K V) (N : Submodule R V) (hN : N.FG) :
    ∃ r : R, r ≠ 0 ∧ ∀ x ∈ N, r • x ∈ Submodule.span R (Set.range b) := by
  classical
  obtain ⟨s, hs⟩ := hN
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite R⁰
    (fun z : ι × s => b.repr (z.2 : V) z.1)
  have hgen (x : V) (hx : x ∈ s) :
      (r : R) • x ∈ Submodule.span R (Set.range b) := by
    apply (b.mem_span_iff_repr_mem R _).mpr
    intro i
    have hc : b.repr ((r : R) • x) i = (r : R) • b.repr x i :=
      ((b.coord i).restrictScalars R).map_smul (r : R) x
    rw [hc]
    exact hr (i, ⟨x, hx⟩)
  refine ⟨r, nonZeroDivisors.ne_zero r.property, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx => exact hgen x hx
  | zero => simpa only [smul_zero] using (Submodule.span R (Set.range b)).zero_mem
  | add x y _ _ hx hy => simpa only [smul_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_comm]
    exact Submodule.smul_mem _ a hx

/-- In the original DVR, the denominator bound is an actual power of any
displayed original uniformizer. The unit factor is removed inside the same
original base-ring lattice. -/
theorem fullBasis_span_absorbs_uniformizer_power
    [IsDiscreteValuationRing R] (b : Module.Basis ι K V)
    (N : Submodule R V) (hN : N.FG) (π : R) (hπ : Irreducible π) :
    ∃ n : ℕ, ∀ x ∈ N, π ^ n • x ∈ Submodule.span R (Set.range b) := by
  obtain ⟨r, hr0, hr⟩ := fullBasis_span_absorbs_finite_submodule b N hN
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hπ
  refine ⟨n, fun x hx => ?_⟩
  have h := (Submodule.span R (Set.range b)).smul_mem (↑(u⁻¹) : R) (hr x hx)
  have he : (↑(u⁻¹) : R) * r = π ^ n := by simp [hu, ← mul_assoc]
  simpa only [smul_smul, he] using h

end
end Dubon2026
