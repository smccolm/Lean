import Dubon2026.FinitePlaceLevel
import Mathlib.Order.Filter.Finite

/-! # Actual finite adelic matrices satisfy their original local level conditions at almost every place -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Filter

/-- Every actual finite adelic matrix lies in the genuine local level order at all but finitely many places. -/
theorem finiteAdeleLevelMatrix_eventually_places (N : ℕ)
    (a : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ∀ᶠ v in cofinite, finitePlaceLevelMatrix N v (a.map (finiteAdelePlace v)) := by
  have he : ∀ᶠ v in cofinite, ∀ i j, (a i j) v ∈ v.adicCompletionIntegers ℚ := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    exact (a i j).property
  have hl := (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) * a 1 0).property
  filter_upwards [he, hl] with v he hl
  refine ⟨he, ?_⟩
  change finiteAdelePlace v (algebraMap ℚ (FiniteAdeleRing ℤ ℚ) ((N : ℚ)⁻¹) * a 1 0) ∈ _ at hl
  simpa only [map_mul, finiteAdelePlace_rational] using hl

/-- Every genuine finite adelic GL2 matrix belongs to the actual local K0(N) at all but finitely many places. -/
theorem finiteAdeleGL2Gamma0_eventually_places (N : ℕ)
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ∀ᶠ v in cofinite, GeneralLinearGroup.map (finiteAdelePlace v) g ∈ finitePlaceGL2Gamma0 N v := by
  filter_upwards [finiteAdeleLevelMatrix_eventually_places N g.val,
    finiteAdeleLevelMatrix_eventually_places N (g⁻¹).val] with v hg hi
  exact ⟨hg, hi⟩

/-- The actual finite adelic matrix has a genuine finite set containing every exceptional local level coordinate. -/
theorem finiteAdeleGL2Gamma0_exists_exceptional_finset (N : ℕ)
    (g : GeneralLinearGroup (Fin 2) (FiniteAdeleRing ℤ ℚ)) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      GeneralLinearGroup.map (finiteAdelePlace v) g ∈ finitePlaceGL2Gamma0 N v := by
  classical
  have h := Filter.eventually_cofinite.mp (finiteAdeleGL2Gamma0_eventually_places N g)
  refine ⟨h.toFinset, ?_⟩
  intro v hv
  by_contra he
  exact hv (h.mem_toFinset.mpr he)

end
end Dubon2026
