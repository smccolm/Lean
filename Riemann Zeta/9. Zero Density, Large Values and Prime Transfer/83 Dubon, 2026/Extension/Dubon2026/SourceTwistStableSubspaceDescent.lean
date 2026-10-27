import Dubon2026.SourceTwistDescentFiniteSupport

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational cusp-form spanning
-> descent of the proved coefficient-twist-stable cusp image. Finite scalar
support and original-field fixed coefficients yield descent of the actual
stable subspace. Adapted from anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0,
S_WLight_span_inter_rational_of_twist_stable. Only its necessary abstract
descent argument is retained; the already proved actual coefficient twist
replaces the separate external flatness/twist construction. -/
namespace Dubon2026.SourceFunctionField.TwistDescent
noncomputable section

theorem descent_generic {k K E : Type*} [Field k] [Field K] [Algebra k K] [AddCommGroup E]
    [Module K E] [Module k E] [IsScalarTower k K E] (M : Submodule k E) (V : Submodule K E)
    (hVle : V ≤ Submodule.span K (M : Set E))
    (T : (K ≃ₐ[k] K) → E → E)
    (hT : ∀ (σ : K ≃ₐ[k] K) (ι : Type) [Fintype ι] (c : ι → K) (e : ι → E), (∀ i, e i ∈ M) →
      T σ (∑ i, c i • e i) = ∑ i, σ (c i) • e i)
    (hTV : ∀ σ, ∀ v ∈ V, T σ v ∈ V)
    (G1 : ∀ c : K, (∀ σ : K ≃ₐ[k] K, σ c = c) → ∃ a : k, algebraMap k K a = c)
    {v : E} (hv : v ∈ V) : v ∈ Submodule.span K {y : E | y ∈ V ∧ y ∈ M} := by
  classical
  obtain ⟨T₀, hTM, hvT⟩ := Submodule.mem_span_finite_of_mem_span (hVle hv)
  set X : Submodule k E := Submodule.span k (T₀ : Set E)
  have hXM : X ≤ M := Submodule.span_le.mpr fun t ht ↦ hTM ht
  haveI : FiniteDimensional k ↥X := FiniteDimensional.span_of_finite _ T₀.finite_toSet
  let U : Submodule k ↥X := (V.restrictScalars k).comap X.subtype
  obtain ⟨W, hUW⟩ := U.exists_isCompl
  let bU := Module.finBasis k ↥U
  let bW := Module.finBasis k ↥W
  let ι := Fin (Module.finrank k ↥U) ⊕ Fin (Module.finrank k ↥W)
  let eX : ι → ↥X := Sum.elim (fun i ↦ (bU i : ↥X)) (fun j ↦ (bW j : ↥X))
  let e : ι → E := fun i ↦ (eX i : E)
  let P : ι → Prop := fun i ↦ Sum.isLeft i
  have heM : ∀ i, e i ∈ M := fun i ↦ hXM (eX i).2
  have hP : ∀ i, P i → e i ∈ V := by
    rintro (i | j) h
    · exact (bU i).2
    · simp [P] at h
  have key : ∀ a : ι → k, (∑ i, algebraMap k K (a i) • e i) ∈ V → ∀ i, ¬ P i → a i = 0 := by
    intro a ha
    have hsum : (∑ i, algebraMap k K (a i) • e i) = ((∑ i, a i • eX i : ↥X) : E) := by
      rw [Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Submodule.coe_smul, algebraMap_smul]
    have hxU : (∑ i, a i • eX i : ↥X) ∈ U := by
      change ((∑ i, a i • eX i : ↥X) : E) ∈ V
      rw [← hsum]; exact ha
    rw [Fintype.sum_sum_type] at hxU
    have hu : (∑ i, a (Sum.inl i) • eX (Sum.inl i) : ↥X) ∈ U :=
      U.sum_mem fun i _ ↦ U.smul_mem _ (bU i).2
    have hw : (∑ j, a (Sum.inr j) • eX (Sum.inr j) : ↥X) ∈ W :=
      W.sum_mem fun j _ ↦ W.smul_mem _ (bW j).2
    have hwU : (∑ j, a (Sum.inr j) • eX (Sum.inr j) : ↥X) ∈ U := by
      have := U.sub_mem hxU hu
      rwa [add_sub_cancel_left] at this
    have hw0 : (∑ j, a (Sum.inr j) • eX (Sum.inr j) : ↥X) = 0 :=
      Submodule.disjoint_def.mp hUW.disjoint _ hwU hw
    have hw0' : (∑ j, a (Sum.inr j) • (bW j : ↥W)) = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero, ← hw0]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Submodule.coe_smul]; rfl
    have hlin := Fintype.linearIndependent_iff.mp bW.linearIndependent (fun j ↦ a (Sum.inr j))
      hw0'
    rintro (i | j) h
    · simp [P] at h
    · exact hlin j
  have hT' : ∀ (σ : K ≃ₐ[k] K) (c : ι → K), T σ (∑ i, c i • e i) = ∑ i, σ (c i) • e i :=
    fun σ c ↦ hT σ ι c e heM
  have hTe : ∀ t ∈ T₀, t ∈ Submodule.span K (Set.range e) := by
    intro t ht
    have htX : t ∈ X := Submodule.subset_span ht
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp
      (hUW.sup_eq_top ▸ Submodule.mem_top (x := (⟨t, htX⟩ : ↥X)))
    have ht' : t = ((u : ↥X) : E) + ((w : ↥X) : E) := by
      rw [← Submodule.coe_add, huw]
    rw [ht']
    refine Submodule.add_mem _ ?_ ?_
    · have hrepr := bU.sum_repr ⟨u, hu⟩
      have : (u : E) = ∑ i, algebraMap k K (bU.repr ⟨u, hu⟩ i) • e (Sum.inl i) := by
        have := congrArg (fun z : ↥U ↦ ((z : ↥X) : E)) hrepr
        simp only at this
        rw [← this, Submodule.coe_sum, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [Submodule.coe_smul, Submodule.coe_smul, algebraMap_smul]
        rfl
      rw [this]
      exact Submodule.sum_mem _ fun i _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
    · have hrepr := bW.sum_repr ⟨w, hw⟩
      have : (w : E) = ∑ j, algebraMap k K (bW.repr ⟨w, hw⟩ j) • e (Sum.inr j) := by
        have := congrArg (fun z : ↥W ↦ ((z : ↥X) : E)) hrepr
        simp only at this
        rw [← this, Submodule.coe_sum, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Submodule.coe_smul, Submodule.coe_smul, algebraMap_smul]
        rfl
      rw [this]
      exact Submodule.sum_mem _ fun j _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  have hve : v ∈ Submodule.span K (Set.range e) := (Submodule.span_le.mpr hTe) hvT
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hve
  have hzero := descent_core e V P hP key T hT' hTV G1 c hv
  refine Submodule.sum_mem _ fun i _ ↦ ?_
  rcases i with i | j
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨hP _ rfl, heM _⟩)
  · rw [hzero (Sum.inr j) (by simp [P]), zero_smul]; exact Submodule.zero_mem _

end
end Dubon2026.SourceFunctionField.TwistDescent
