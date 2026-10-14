import Dubon2026.LocalFieldValuativeExtensionUniqueness
import Mathlib.RingTheory.Valuation.Discrete.RankOne

/-! # Detecting local-field uniformizers in an ambient DVR

An integral embedding of the base integer ring into an ambient DVR puts every
integer of a finite local extension in the pulled-back ambient valuation ring.
The chosen local valuation ring has Krull dimension one, so a nontrivial
pulled-back overring must equal it.  An ambient uniformizer can then be pulled
back by divisibility.  This is the narrow valuation comparison needed for the
actual changed cyclotomic compositum in DUB-17.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

theorem localField_integer_valuationSubring_eq_comap_of_integral_embedding
    (E M B Ω : Type) [Field E] [Field M] [Algebra E M]
    [ValuativeRel E] [ValuativeRel M]
    [TopologicalSpace E] [TopologicalSpace M]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field Ω] [Algebra B Ω] [IsFractionRing B Ω]
    (j : 𝒪[E] →+* B) (ι : M →+* Ω)
    (hcomp : (algebraMap B Ω).comp j = ι.comp (algebraMap 𝒪[E] M))
    (π : M)
    (hπ : ((IsDiscreteValuationRing.maximalIdeal B).valuation Ω).IsUniformizer (ι π)) :
    (ValuativeRel.valuation M).valuationSubring =
      (((IsDiscreteValuationRing.maximalIdeal B).valuation Ω).comap ι).valuationSubring := by
  let vΩ := (IsDiscreteValuationRing.maximalIdeal B).valuation Ω
  apply ValuationSubring.eq_of_le_of_ne_top
  · intro x hx
    change ValuativeRel.valuation M (x : M) ≤ 1 at hx
    have hxint : IsIntegral 𝒪[E] (x : M) :=
      (localField_vle_one_iff_integral E M x).mp
        ((Valuation.vle_one_iff (ValuativeRel.valuation M)).mpr hx)
    have himg : IsIntegral B (ι (x : M)) :=
      hxint.map_of_comp_eq j ι hcomp
    obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp himg
    change vΩ (ι (x : M)) ≤ 1
    rw [← hb]
    exact ((IsDiscreteValuationRing.equivValuationSubring (A := B) (K := Ω)) b).property
  · intro htop
    have htriv := (Valuation.valuationSubring_eq_top_iff (vΩ.comap ι)).mp htop
    apply htriv
    exact ⟨⟨π, by simpa only [vΩ, Valuation.comap_apply] using hπ.val_ne_zero,
      by simpa only [vΩ, Valuation.comap_apply] using ne_of_lt hπ.val_lt_one⟩⟩

theorem localField_isUniformizer_of_integral_ambient_embedding
    (E M B Ω : Type) [Field E] [Field M] [Algebra E M]
    [ValuativeRel E] [ValuativeRel M]
    [TopologicalSpace E] [TopologicalSpace M]
    [IsNonarchimedeanLocalField E] [IsNonarchimedeanLocalField M]
    [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Field Ω] [Algebra B Ω] [IsFractionRing B Ω]
    (j : 𝒪[E] →+* B) (ι : M →+* Ω)
    (hcomp : (algebraMap B Ω).comp j = ι.comp (algebraMap 𝒪[E] M))
    {π : M}
    (hπ : ((IsDiscreteValuationRing.maximalIdeal B).valuation Ω).IsUniformizer (ι π)) :
    (ValuativeRel.valuation M).IsUniformizer π := by
  let vM := ValuativeRel.valuation M
  let vΩ := (IsDiscreteValuationRing.maximalIdeal B).valuation Ω
  have hsub : vM.valuationSubring = (vΩ.comap ι).valuationSubring :=
    localField_integer_valuationSubring_eq_comap_of_integral_embedding
      E M B Ω j ι hcomp π hπ
  have hEquiv : vM.IsEquiv (vΩ.comap ι) :=
    (Valuation.isEquiv_iff_valuationSubring vM (vΩ.comap ι)).mpr hsub
  have hπ_target_lt : vM π < 1 := by
    have hπ_comap_lt : (vΩ.comap ι) π < (vΩ.comap ι) 1 := by
      simpa only [vΩ, Valuation.comap_apply, map_one] using hπ.val_lt_one
    simpa only [map_one] using
      (hEquiv.lt_iff_lt (x := π) (y := (1 : M))).2 hπ_comap_lt
  let πtarget : vM.valuationSubring := ⟨π, hπ_target_lt.le⟩
  have hmaximal : IsLocalRing.maximalIdeal vM.valuationSubring =
      Ideal.span ({πtarget} : Set vM.valuationSubring) := by
    apply le_antisymm
    · intro a ha
      have ha_target_lt : vM (a : M) < 1 :=
        (Valuation.mem_maximalIdeal_iff (v := vM)).1 ha
      have ha_ambient_lt : vΩ (ι (a : M)) < 1 := by
        have ha_comap_lt : (vΩ.comap ι) (a : M) < (vΩ.comap ι) 1 :=
          (hEquiv.lt_iff_lt (x := (a : M)) (y := (1 : M))).1
            (by simpa only [map_one] using ha_target_lt)
        simpa only [vΩ, Valuation.comap_apply, map_one] using ha_comap_lt
      let aambient : vΩ.valuationSubring := ⟨ι (a : M), ha_ambient_lt.le⟩
      let πambient : vΩ.valuationSubring := ⟨ι π, hπ.val_lt_one.le⟩
      have ha_ambient_maximal : aambient ∈ IsLocalRing.maximalIdeal vΩ.valuationSubring :=
        (Valuation.mem_maximalIdeal_iff (v := vΩ)).2 ha_ambient_lt
      have hπambient : vΩ.IsUniformizer (πambient : Ω) := by
        simpa only [πambient] using hπ
      rw [hπambient.is_generator,
        Ideal.mem_span_singleton] at ha_ambient_maximal
      obtain ⟨c, hc⟩ := ha_ambient_maximal
      have hc_field : ι (a : M) = ι π * (c : Ω) := by
        simpa only [aambient, πambient] using
          congrArg (fun t : vΩ.valuationSubring => (t : Ω)) hc
      have hπ_ne : π ≠ 0 := by
        intro hzero
        apply hπ.ne_zero
        simp only [hzero, map_zero]
      have hc_eq : (c : Ω) = ι (π⁻¹ * (a : M)) := by
        apply mul_left_cancel₀ hπ.ne_zero
        calc
          ι π * (c : Ω) = ι (a : M) := hc_field.symm
          _ = ι (π * (π⁻¹ * (a : M))) := by
            congr 1
            rw [← mul_assoc, mul_inv_cancel₀ hπ_ne, one_mul]
          _ = ι π * ι (π⁻¹ * (a : M)) := by rw [map_mul]
      have hquotient_comap : (vΩ.comap ι) (π⁻¹ * (a : M)) ≤ (vΩ.comap ι) 1 := by
        have hquotient_ambient : vΩ (ι (π⁻¹ * (a : M))) ≤ 1 := by
          rw [← hc_eq]
          exact c.property
        simpa only [vΩ, Valuation.comap_apply, map_one] using hquotient_ambient
      have hquotient_target : vM (π⁻¹ * (a : M)) ≤ 1 := by
        have hle := (hEquiv.le_iff_le
          (x := π⁻¹ * (a : M)) (y := (1 : M))).2 hquotient_comap
        simpa only [map_one] using hle
      let quotient : vM.valuationSubring :=
        ⟨π⁻¹ * (a : M), hquotient_target⟩
      rw [Ideal.mem_span_singleton]
      refine ⟨quotient, ?_⟩
      apply Subtype.ext
      change (a : M) = π * (π⁻¹ * (a : M))
      rw [← mul_assoc, mul_inv_cancel₀ hπ_ne, one_mul]
    · rw [Ideal.span_le]
      intro a ha
      have ha_eq : a = πtarget := by simpa using ha
      subst a
      exact (Valuation.mem_maximalIdeal_iff (v := vM)).2
        (by simpa only [πtarget] using hπ_target_lt)
  exact vM.isUniformizer_of_maximalIdeal_eq_span hmaximal

end
end Dubon2026
