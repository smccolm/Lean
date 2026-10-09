import Dubon2026.AdelicFiniteTupleCoefficients

/-! # Reordering genuine finite adelic coordinates preserves their original product and complement -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {n : ℕ} (v : Fin n → HeightOneSpectrum ℤ) (e : Equiv.Perm (Fin n))

/-- Permuting the selected genuine places leaves the original full complementary subgroup unchanged. -/
theorem adelicFiniteFamilyAwayGroup_reindex :
    adelicFiniteFamilyAwayGroup (fun i => v (e i)) = adelicFiniteFamilyAwayGroup v := by
  ext a
  change (fun i => adelicPlaceGL2Hom (v (e i)) a) = 1 ↔
    (fun i => adelicPlaceGL2Hom (v i) a) = 1
  constructor
  · intro h
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    exact congrFun h j
  · intro h
    funext i
    exact congrFun h (e i)

/-- Reordered complementary coordinates are the very same original adelic matrices. -/
def adelicFiniteFamilyAwayReindex :
    adelicFiniteFamilyAwayGroup (fun i => v (e i)) ≃* adelicFiniteFamilyAwayGroup v :=
  MulEquiv.subgroupCongr (adelicFiniteFamilyAwayGroup_reindex v e)

/-- The true finite adelic product is independent of the order of its distinct original local factors. -/
theorem adelicFinitePlaceProduct_reindex (hv : Function.Injective v)
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) :
    adelicFinitePlaceProduct (fun i => v (e i)) (hv.comp e.injective) (fun i => g (e i)) =
      adelicFinitePlaceProduct v hv g := by
  classical
  let l := (Finset.univ : Finset (Fin n)).toList
  have hl : l.Nodup := Finset.nodup_toList _
  have hu : l.toFinset = Finset.univ := Finset.toList_toFinset _
  have heu : (l.map e).toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨e.symm i, ?_, e.apply_symm_apply i⟩
    exact Finset.mem_toList.mpr (Finset.mem_univ _)
  have h₁ := adelicFinitePlaceProduct_eq_list (fun i => v (e i)) (hv.comp e.injective)
    (fun i => g (e i)) l hl hu
  have h₂ := adelicFinitePlaceProduct_eq_list v hv g (l.map e) (hl.map e.injective) heu
  exact h₁.trans (by simpa only [List.map_map, Function.comp_def] using h₂.symm)

/-- Reordering the actual finite local coordinates and their literal complement preserves the original full adelic matrix. -/
theorem adelicFiniteFamilyEquiv_reindex (hv : Function.Injective v)
    (g : ∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ))
    (a : adelicFiniteFamilyAwayGroup (fun i => v (e i))) :
    adelicFiniteFamilyEquiv (fun i => v (e i)) (hv.comp e.injective) ((fun i => g (e i)), a) =
      adelicFiniteFamilyEquiv v hv (g, adelicFiniteFamilyAwayReindex v e a) := by
  change adelicFinitePlaceProduct (fun i => v (e i)) (hv.comp e.injective) (fun i => g (e i)) * a.val =
    adelicFinitePlaceProduct v hv g * a.val
  rw [adelicFinitePlaceProduct_reindex]

end
end Dubon2026
