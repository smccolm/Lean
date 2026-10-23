import Dubon2026.SourceCurvePlaceCompletion
import Dubon2026.SourceCurveRestrictionOrders

/-! The actual extension embedding is uniformly continuous for the two
normalized place valuations. This constructs, rather than assumes, the
completion embedding needed for finite integral bases in the residue/trace
comparison. The order scaling is reused from the existing curve code.
Adapted from the verified FLT Def_AlgebraicCurve_PlaceCompletion source. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open WithZero Topology MonoidWithZeroHom

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The ramification index is the positive order of the mapped base uniformizer. -/
def ramificationIndex : ℕ := (w.ord (algebraMap F E (w.restrict F).uniformizer)).toNat

/-- The actual ramification index is positive. -/
theorem ramificationIndex_pos : 0 < w.ramificationIndex (F := F) := by
  have h := w.ord_restricted_uniformizer_pos (F := F)
  unfold ramificationIndex
  omega

/-- The ramification index recovers the original positive integral order. -/
theorem ramificationIndex_cast : (w.ramificationIndex (F := F) : ℤ) =
    w.ord (algebraMap F E (w.restrict F).uniformizer) :=
  Int.toNat_of_nonneg w.ord_restricted_uniformizer_pos.le

/-- The original field embedding scales normalized multiplicative valuations by ramification. -/
theorem adicValuation_algebraMap (x : F) :
    w.adicValuation (algebraMap F E x) =
      (w.restrict F).adicValuation x ^ w.ramificationIndex (F := F) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_pow (w.ramificationIndex_pos (F := F)).ne']
  · have hord := w.ord_algebraMap_restrict x
    have hax : algebraMap F E x ≠ 0 := (map_ne_zero_iff _ (algebraMap F E).injective).mpr hx
    have hv0 := (w.restrict F).adicValuation_ne_zero hx
    have hw0 := w.adicValuation_ne_zero hax
    unfold ord at hord
    have he : log (w.adicValuation (algebraMap F E x)) =
        log ((w.restrict F).adicValuation x ^ w.ramificationIndex (F := F)) := by
      rw [← zpow_natCast, log_zpow, zsmul_eq_mul, w.ramificationIndex_cast]
      simp only [Int.cast_id, ord]
      nlinarith [hord]
    rw [← exp_log hw0, he, exp_log (pow_ne_zero _ hv0)]

/-- The same valuation formula holds on the native valued-field type synonyms. -/
theorem valued_withValMapAlgebraMap (x : WithVal ((w.restrict F).heightOneSpectrum.valuation F)) :
    Valued.v (WithVal.map ((w.restrict F).heightOneSpectrum.valuation F)
      (w.heightOneSpectrum.valuation E) (algebraMap F E) x) =
        Valued.v x ^ w.ramificationIndex (F := F) := by
  rw [WithVal.map_apply, WithVal.valued_toVal]
  exact w.adicValuation_algebraMap x.ofVal

/-- The actual finite-extension embedding is uniformly continuous for its place valuations. -/
theorem uniformContinuous_withValMapAlgebraMap :
    UniformContinuous (WithVal.map ((w.restrict F).heightOneSpectrum.valuation F)
      (w.heightOneSpectrum.valuation E) (algebraMap F E)) := by
  refine uniformContinuous_of_continuousAt_zero _ ?_
  simp_rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  have hγ0 : (ValueGroup₀.embedding γ.val : ℤᵐ⁰) ≠ 0 :=
    (γ.isUnit.map ValueGroup₀.embedding).ne_zero
  have hc0 : min (ValueGroup₀.embedding γ.val) (1 : ℤᵐ⁰) ≠ 0 :=
    (lt_min (zero_lt_iff.mpr hγ0) zero_lt_one).ne'
  obtain ⟨x₀, hx₀⟩ := (w.restrict F).heightOneSpectrum.valuation_surjective F
    (min (ValueGroup₀.embedding γ.val) 1)
  have hx₀v : Valued.v (WithVal.toVal ((w.restrict F).heightOneSpectrum.valuation F) x₀) =
      min (ValueGroup₀.embedding γ.val) 1 := by rw [WithVal.valued_toVal, hx₀]
  have hδ0 : Valued.v.restrict
      (WithVal.toVal ((w.restrict F).heightOneSpectrum.valuation F) x₀) ≠ 0 := by
    rw [ne_eq, Valuation.restrict_eq_zero_iff, hx₀v]
    exact hc0
  refine ⟨Units.mk0 _ hδ0, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0] at hx ⊢
  rw [Valuation.restrict_lt_iff, hx₀v] at hx
  rw [Valuation.restrict_lt_iff_lt_embedding, w.valued_withValMapAlgebraMap]
  calc Valued.v x ^ w.ramificationIndex (F := F)
      ≤ Valued.v x ^ 1 := pow_le_pow_right_of_le_one' (hx.trans_le (min_le_right _ _)).le
        (w.ramificationIndex_pos (F := F))
    _ = Valued.v x := pow_one _
    _ < ValueGroup₀.embedding γ.val := hx.trans_le (min_le_left _ _)

end Dubon2026.SourceCurve.Place
