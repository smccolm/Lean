import Dubon2026.SourceOriginalPeriodsFullRealSpan

/-! DUB-17/18 -> original torsion cardinality -> discrete original periods.
The loop-generation clause of the raw reciprocity theorem gives exact integer
coordinates for every actual period-lattice element. No symplectic change of
basis is required. The geometric loop-generation clause remains upstream.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Set KaehlerDifferential
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_period_coordinates {n : ℕ} {ι : Type*} [Fintype ι]
    (b : Fin n → Ω[F⁄ℂ]) (Pz : ι → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
    (hgen : ∀ (P : Place ℂ F) (γ : Path P P), ∃ κ : ι → ℤ,
      ∀ i, pathIntegral N (b i) γ = ∑ k, (κ k : ℂ) * pathIntegral N (b i) (Z k))
    {u : Fin n → ℂ} (hu : u ∈ pathPeriodLattice N b) :
    ∃ κ : ι → ℤ, u = fun i => ∑ k, (κ k : ℂ) * pathIntegral N (b i) (Z k) := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨P, γ, rfl⟩ := hu
    obtain ⟨κ, hκ⟩ := hgen P γ
    exact ⟨κ, funext hκ⟩
  | zero => exact ⟨0, by ext i; simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨κ, rfl⟩ := hu
    obtain ⟨μ, rfl⟩ := hv
    exact ⟨κ + μ, by ext i; simp [add_mul, Finset.sum_add_distrib]⟩
  | smul a u _ hu =>
    obtain ⟨κ, rfl⟩ := hu
    refine ⟨a • κ, ?_⟩
    ext i
    simp [zsmul_eq_mul, Finset.mul_sum, mul_assoc]

theorem original_period_lattice_eq_span_loops {n : ℕ} {ι : Type*} [Fintype ι]
    (b : Fin n → Ω[F⁄ℂ]) (Pz : ι → Place ℂ F) (Z : ∀ k, Path (Pz k) (Pz k))
    (hgen : ∀ (P : Place ℂ F) (γ : Path P P), ∃ κ : ι → ℤ,
      ∀ i, pathIntegral N (b i) γ = ∑ k, (κ k : ℂ) * pathIntegral N (b i) (Z k)) :
    pathPeriodLattice N b =
      Submodule.span ℤ (Set.range (fun k i => pathIntegral N (b i) (Z k))) := by
  classical
  apply le_antisymm
  · intro u hu
    obtain ⟨κ, rfl⟩ := exists_original_period_coordinates N b Pz Z hgen hu
    have hsum : (fun i => ∑ k, (κ k : ℂ) * pathIntegral N (b i) (Z k)) =
        ∑ k, κ k • (fun i => pathIntegral N (b i) (Z k)) := by
      ext i
      simp [zsmul_eq_mul]
    rw [hsum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact mem_pathPeriodLattice_of_loop N b (Z k)

end
end Dubon2026.SourceFunctionField.OriginalChart
