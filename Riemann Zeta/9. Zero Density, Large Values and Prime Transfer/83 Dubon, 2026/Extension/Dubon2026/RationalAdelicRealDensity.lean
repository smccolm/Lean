import Dubon2026.RationalAdelicAdditiveQuotient

/-! # Density of the actual real additive line in the rational adele quotient -/

namespace Dubon2026

noncomputable section
open NumberField IsDedekindDomain Set

/-- The original real additive line inside the canonical full rational adele ring. -/
def rationalAdeleRealEmbedding : ℝ →+ AdeleRing ℤ ℚ where
  toFun t := rationalAdeleRealFiniteRingEquiv.symm (t, 0)
  map_zero' := by change rationalAdeleRealFiniteRingEquiv.symm 0 = 0; exact map_zero _
  map_add' a b := by
    change rationalAdeleRealFiniteRingEquiv.symm (a + b, 0) = _
    simpa only [Prod.mk_add_mk, zero_add] using
      map_add rationalAdeleRealFiniteRingEquiv.symm (a, 0) (b, 0)

/-- The genuine real line maps into the actual additive adele quotient. -/
def rationalAdelicRealQuotientMap : ℝ →+ RationalAdelicAdditiveQuotient :=
  (QuotientAddGroup.mk' (AdeleRing.principalSubgroup ℤ ℚ)).comp rationalAdeleRealEmbedding

/-- The literal real embedding is continuous for the actual canonical adele topology. -/
theorem rationalAdeleRealEmbedding_continuous : Continuous rationalAdeleRealEmbedding :=
  rationalAdeleRealFiniteRingEquiv_symm_continuous.comp (continuous_id.prodMk continuous_const)

/-- The original real orbit is continuous in the genuine quotient topology. -/
theorem rationalAdelicRealQuotientMap_continuous : Continuous rationalAdelicRealQuotientMap :=
  QuotientAddGroup.continuous_mk.comp rationalAdeleRealEmbedding_continuous

/-- Actual rational finite approximation proves density of the original real additive line in the full rational adele quotient. -/
theorem rationalAdelicRealQuotientMap_dense : DenseRange rationalAdelicRealQuotientMap := by
  intro z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  let r := (rationalAdeleRealFiniteRingEquiv x).1
  have hd (y : FiniteAdeleRing ℤ ℚ) :
      (QuotientAddGroup.mk (rationalAdeleRealFiniteRingEquiv.symm (r, y)) :
        RationalAdelicAdditiveQuotient) ∈ closure (Set.range rationalAdelicRealQuotientMap) := by
    refine rational_dense_finiteAdeles.induction_on y
      (isClosed_closure.preimage (QuotientAddGroup.continuous_mk.comp
        (rationalAdeleRealFiniteRingEquiv_symm_continuous.comp
          (continuous_const.prodMk continuous_id)))) ?_
    intro q
    apply subset_closure
    refine ⟨r - (q : ℝ), ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    refine ⟨-q, ?_⟩
    apply rationalAdeleRealFiniteRingEquiv.injective
    rw [rationalAdeleRealFiniteRingEquiv_algebraMap, map_sub]
    change (((-q : ℚ) : ℝ),
      algebraMap ℚ (FiniteAdeleRing ℤ ℚ) (-q)) =
      rationalAdeleRealFiniteRingEquiv (rationalAdeleRealFiniteRingEquiv.symm (r - q, 0)) -
      rationalAdeleRealFiniteRingEquiv
        (rationalAdeleRealFiniteRingEquiv.symm (r, algebraMap ℚ (FiniteAdeleRing ℤ ℚ) q))
    simp only [RingEquiv.apply_symm_apply, Rat.cast_neg, map_neg, Prod.mk_sub_mk, zero_sub]
    congr 1
    ring
  simpa only [r, Prod.mk.eta, RingEquiv.symm_apply_apply] using
    hd (rationalAdeleRealFiniteRingEquiv x).2

end
end Dubon2026
