import Dubon2026.SourceCurveSeparatingCoordinateDegree

/-! The existing separating-coordinate degree formula forces a place
over every prescribed finite value. This supplies the actual place in
the DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 finite Galois specialization,
exceptional-fiber census, reverse genus and good reduction chain.
Reusing the positive degree sum avoids a separate maximal-ideal valuation
extension construction from the external source. -/
namespace Dubon2026.SourceCurve
open IntermediateField
noncomputable section

theorem exists_place_over_finite_value
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (t : F) (ht : Transcendental K t) [FiniteDimensional K⟮t⟯ F]
    [Algebra.IsSeparable K⟮t⟯ F] (a : K) :
    ∃ v : Place K F, 0 < v.ord (t - algebraMap K F a) := by
  have hfield : K⟮t - algebraMap K F a⟯ = K⟮t⟯ := by
    apply le_antisymm
    · apply adjoin_simple_le_iff.mpr
      exact sub_mem (mem_adjoin_simple_self K t) (IntermediateField.algebraMap_mem _ a)
    · apply adjoin_simple_le_iff.mpr
      have h := add_mem (mem_adjoin_simple_self K (t - algebraMap K F a))
        (IntermediateField.algebraMap_mem K⟮t - algebraMap K F a⟯ a)
      simpa only [sub_add_cancel] using h
  have hx : Transcendental K (t - algebraMap K F a) := by
    intro h
    apply ht
    simpa only [sub_add_cancel] using h.add (isAlgebraic_algebraMap a)
  haveI : FiniteDimensional K⟮t - algebraMap K F a⟯ F := hfield ▸ inferInstance
  haveI : Algebra.IsSeparable K⟮t - algebraMap K F a⟯ F := hfield ▸ inferInstance
  have hsum := sum_positive_orders_eq_finrank_separating (t - algebraMap K F a) hx
  by_contra h
  haveI : IsEmpty {v : Place K F // 0 < v.ord (t - algebraMap K F a)} :=
    ⟨fun v => h ⟨v.val, v.property⟩⟩
  rw [finsum_of_isEmpty] at hsum
  have hpos : 0 < Module.finrank K⟮t - algebraMap K F a⟯ F := Module.finrank_pos
  omega

end
end Dubon2026.SourceCurve
