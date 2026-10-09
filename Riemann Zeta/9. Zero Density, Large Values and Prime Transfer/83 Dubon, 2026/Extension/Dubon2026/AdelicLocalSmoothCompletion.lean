import Dubon2026.AdelicLocalSubgroupProjection

/-! # The genuine full smooth local completion equals the original algebraic orbit core -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- At every genuine compact open local subgroup, all original fixed cyclic Hilbert vectors already lie in the actual algebraic local core. -/
theorem adelicLocalCyclic_compact_open_fixed_eq_core (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))
    (hJo : IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))))
    (hJc : IsCompact (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)))) :
    adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v J =
      adelicLocalCyclicCore f v ⊓ adelicLocalSubgroupFixedSpace f v J := by
  letI := adelicLocalCyclic_open_fixed_finiteDimensional f hf hk v J hJo
  have hle : adelicLocalCyclicCore f v ⊓ adelicLocalSubgroupFixedSpace f v J ≤
      adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v J :=
    inf_le_inf (Submodule.le_topologicalClosure _) le_rfl
  letI := Submodule.finiteDimensional_of_le hle
  have he := @projection_stable_core_closure (AdelicCyclicHilbert f) inferInstance inferInstance
    (adelicLocalCyclicCore f v) (adelicLocalSubgroupFixedSpace f v J) inferInstance
    (adelicLocalSubgroupFixedSpace_isClosed f v J) (adelicLocalSubgroupProjection_core f v J hJc)
  rw [adelicLocalCyclicCore_closure] at he
  rw [← he]
  exact (Submodule.closed_of_finiteDimensional _).submodule_topologicalClosure_eq

/-- An original local cyclic Hilbert vector is genuinely smooth exactly when it belongs to the literal algebraic span of the original cusp orbit. -/
theorem adelicLocalCyclic_smooth_iff_core (hf : f ≠ 0) (hk : 0 < k)
    (v : HeightOneSpectrum ℤ) (x : AdelicCyclicHilbert f) (hx : x ∈ adelicLocalCyclicClosedSpan f v) :
    (∃ J : Subgroup (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ)),
      IsOpen (J : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) ∧
        ∀ g ∈ J, adelicCyclicLocalRepresentation f v g x = x) ↔ x ∈ adelicLocalCyclicCore f v := by
  constructor
  · rintro ⟨J, hJo, hJx⟩
    let K := J ⊓ finitePlaceGL2Gamma0 N v
    have hKo : IsOpen (K : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :=
      hJo.inter (finitePlaceGL2Gamma0_isOpen N v)
    have hKc : IsCompact (K : Set (GeneralLinearGroup (Fin 2) (v.adicCompletion ℚ))) :=
      (finitePlaceGL2Gamma0_isCompact N v).inter_left (J.isClosed_of_isOpen hJo)
    have hxK : x ∈ adelicLocalCyclicClosedSpan f v ⊓ adelicLocalSubgroupFixedSpace f v K := by
      refine ⟨hx, ?_⟩
      intro g
      exact hJx g.val g.property.1
    rw [adelicLocalCyclic_compact_open_fixed_eq_core f hf hk v K hKo hKc] at hxK
    exact hxK.1
  · exact adelicLocalCyclicCore_smooth f v x

end
end Dubon2026
