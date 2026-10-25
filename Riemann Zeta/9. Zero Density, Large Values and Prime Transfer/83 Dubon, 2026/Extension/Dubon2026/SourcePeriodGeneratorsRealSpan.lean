import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic

/-! DUB-17/18 -> cover Abel converse -> integer matrix unimodularity.
This finite-dimensional step uses exactly the existing integer period
coordinates and real-annihilator result. Separating the linear algebra keeps
the actual field expressions out of its proof, without changing proof limits. -/
namespace Dubon2026.SourceFunctionField.PeriodRealDual
noncomputable section
open Set

theorem integer_coordinates_of_finset_generators {ι κ : Type*}
    (s : Finset ι) (z : ι → κ → ℂ) {S : Set (κ → ℂ)}
    (hgen : ∀ u ∈ S, ∃ a : ι → ℤ, ∀ i, u i = ∑ l ∈ s, (a l : ℂ) * z l i) :
    ∀ u ∈ Submodule.span ℤ S, ∃ a : {l // l ∈ s} → ℤ, u = ∑ l, a l • z l.1 := by
  have hspan : Submodule.span ℤ S ≤
      Submodule.span ℤ (range (fun l : {l // l ∈ s} => z l.1)) := by
    apply Submodule.span_le.mpr
    intro u hu
    obtain ⟨a, ha⟩ := hgen u hu
    have he : u = ∑ l : {l // l ∈ s}, a l.1 • z l.1 := by
      funext i
      have hi := ha i
      rw [← Finset.sum_coe_sort s (fun l => (a l : ℂ) * z l i)] at hi
      simpa only [Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul, Pi.mul_apply,
        Pi.intCast_apply] using hi
    rw [he]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
  intro u hu
  have hm := hspan hu
  rw [Submodule.mem_span_range_iff_exists_fun] at hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨a, ha.symm⟩

theorem span_top_of_integer_coordinates {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) (z : ι → V)
    (hcoords : ∀ u ∈ Λ, ∃ a : ι → ℤ, u = ∑ l, a l • z l)
    (hann : ∀ ℓ : V →ₗ[ℝ] ℝ, (∀ u ∈ Λ, ℓ u = 0) → ℓ = 0) :
    ⊤ ≤ Submodule.span ℝ (range z) := by
  by_contra htop
  have hne : Submodule.span ℝ (range z) ≠ ⊤ := fun he => htop (by rw [he])
  obtain ⟨ℓ, hℓ0, hℓbot⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (lt_top_iff_ne_top.mpr hne) inferInstance
  have hz : ∀ l, ℓ (z l) = 0 := by
    intro l
    have hzmem : z l ∈ Submodule.span ℝ (range z) := Submodule.subset_span ⟨l, rfl⟩
    have hm := Submodule.mem_map_of_mem (f := ℓ) hzmem
    rw [hℓbot, Submodule.mem_bot] at hm
    exact hm
  apply hℓ0
  apply hann ℓ
  intro u hu
  obtain ⟨a, rfl⟩ := hcoords u hu
  rw [map_sum]
  simp only [map_zsmul, hz, smul_zero, Finset.sum_const_zero]

end
end Dubon2026.SourceFunctionField.PeriodRealDual
