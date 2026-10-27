import Dubon2026.SourceCyclotomicFrickeIndex

/-! DUB-17/18 -> actual Gamma1 differential realization -> rational Fourier
structure -> conjugation of the original cyclotomic Fricke field. The
existing torsion-product coefficient formula and integral discriminant
series identify conjugation with the actual torsion-index permutation. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass SourceFunctionField
open scoped MatrixGroups Manifold ModularForm

theorem coeffMap_discriminantLaurentK_ringHom (N : ℕ) [NeZero N] (φ : kN N →+* ℂ) :
    coeffMap φ (discriminantLaurentK N) =
      (qExpansion N (⇑CuspForm.discriminant : ℍ → ℂ) : LaurentSeries ℂ) := by
  rw [discriminantLaurentK, coeffMap_qExpand, coeffMap_ofPowerSeries]
  have he : ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom (kN N))).map φ =
      (PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom ℂ) := by
    ext n
    simp only [PowerSeries.coeff_map, Int.coe_castRingHom, map_intCast]
  rw [he, ← qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit]
  simpa only [CuspForm.coe_discriminant] using
    (qExpansion_laurent_width (⇑CuspForm.discriminant : ℍ → ℂ) N
      (periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL)
      CuspForm.discriminant.holo' (ModularFormClass.bdd_at_infty CuspForm.discriminant)).symm

theorem coeffMap_frickeLaurentK_cyclotomic (N : ℕ) [NeZero N]
    (s : ℕ) (hs : s.Coprime N) (φ : kN N →+* ℂ)
    (hφ : φ (zetaK N) = zetaN N ^ s) (i : FrickeIdx N) :
    coeffMap φ (frickeLaurentK N i) =
      coeffMap (algebraMap (kN N) ℂ) (frickeLaurentK N (cyclotomicFrickeIndex s hs i)) := by
  obtain ⟨h₁, h₂, h₀⟩ := frickeIdx_hyps i.1 i.2
  obtain ⟨h₁', h₂', h₀'⟩ := frickeIdx_hyps (cyclotomicFrickeIndex s hs i).1
    (cyclotomicFrickeIndex s hs i).2
  simp only [frickeLaurentK, map_div₀, map_mul, map_neg, map_one, map_ofNat,
    coeffMap_ofPowerSeries]
  rw [frickeHQSeriesK_map_cyclotomic h₁ h₂ h₀ hs φ hφ,
    frickeHQSeriesK_map_inclusion h₁' h₂' h₀', coeffMap_discriminantLaurentK_ringHom,
    coeffMap_discriminantLaurentK, cyclotomicFrickeIndex_val_zero, cyclotomicFrickeIndex_val_one]

theorem coeffMap_frickeLaurentK_aut (N : ℕ) [NeZero N]
    (σ : kN N ≃ₐ[ℚ] kN N) (s : ℕ) (hs : s.Coprime N)
    (hσ : σ (zetaK N) = zetaK N ^ s) (i : FrickeIdx N) :
    coeffMap σ.toRingEquiv.toRingHom (frickeLaurentK N i) =
      frickeLaurentK N (cyclotomicFrickeIndex s hs i) := by
  apply (coeffMap (algebraMap (kN N) ℂ)).injective
  have hφ : ((algebraMap (kN N) ℂ).comp σ.toRingEquiv.toRingHom) (zetaK N) =
      zetaN N ^ s := by
    change (σ (zetaK N) : ℂ) = _
    rw [hσ]
    rfl
  convert coeffMap_frickeLaurentK_cyclotomic N s hs
    ((algebraMap (kN N) ℂ).comp σ.toRingEquiv.toRingHom) hφ i using 1

theorem coeffMap_jqNModC_aut (N : ℕ) [NeZero N] (σ : kN N ≃ₐ[ℚ] kN N) :
    coeffMap σ.toRingEquiv.toRingHom (jqNModC (kN N) N) = jqNModC (kN N) N := by
  rw [jqNModC, coeffMap_qExpand]
  congr 1
  exact map_jqModC σ.toRingEquiv.toRingHom

end
end Dubon2026.SourceFricke
