import Dubon2026.SourceQExpansionLaurentWidth
import Dubon2026.SourcePoleBoundedCuspLaurent
import Dubon2026.SourceFrickeProductCyclotomic
import Dubon2026.SourceHasseCoefficientTransport
import Dubon2026.SourceLaurentCoefficientReindex

/-! DUB-17/18 -> actual Gamma1 differential/cusp comparison -> rational
Fourier structure -> cyclotomic coefficient descent. Construct the Laurent
series of the actual Fricke generators over their original cyclotomic field.
The ordinary numerator series and integral discriminant series are already
proved; their quotient is identified as a meromorphic cusp germ. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane ModularForm SlashInvariantFormClass ModularFormClass SourceFunctionField
open scoped Manifold ModularForm MatrixGroups

/-- The actual discriminant Laurent series at width N over the cyclotomic field. -/
def discriminantLaurentK (N : ℕ) [NeZero N] : LaurentSeries (kN N) :=
  qExpand (kN N) N
    (((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom (kN N))) : LaurentSeries (kN N))

theorem coeffMap_discriminantLaurentK (N : ℕ) [NeZero N] :
    coeffMap (algebraMap (kN N) ℂ) (discriminantLaurentK N) =
      (qExpansion N (⇑CuspForm.discriminant : ℍ → ℂ) : LaurentSeries ℂ) := by
  rw [discriminantLaurentK, coeffMap_qExpand, coeffMap_ofPowerSeries]
  have he : ((PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom (kN N))).map
      (algebraMap (kN N) ℂ) =
      (PowerSeries.X * dedekindEtaUnit).map (Int.castRingHom ℂ) := by
    ext n
    simp only [PowerSeries.coeff_map, Int.coe_castRingHom, map_intCast]
  rw [he, ← qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit]
  simpa only [CuspForm.coe_discriminant] using
    (qExpansion_laurent_width (⇑CuspForm.discriminant : ℍ → ℂ) N
      (periodic_comp_ofComplex CuspForm.discriminant one_mem_strictPeriods_SL)
      CuspForm.discriminant.holo' (ModularFormClass.bdd_at_infty CuspForm.discriminant)).symm

theorem coeffMap_jqNModC_kN (N : ℕ) [NeZero N] :
    coeffMap (algebraMap (kN N) ℂ) (jqNModC (kN N) N) = jqNModC ℂ N := by
  rw [jqNModC, coeffMap_qExpand, jqNModC]
  congr 1
  exact map_jqModC (algebraMap (kN N) ℂ)

/-- The cyclotomic Laurent series of the original Fricke function. -/
def frickeLaurentK (N : ℕ) [NeZero N] (i : FrickeIdx N) : LaurentSeries (kN N) :=
  (-1 / 2592 : LaurentSeries (kN N)) *
    (frickeHQSeriesK (frickeIdx_hyps i.1 i.2).1 (i.1 1).val : LaurentSeries (kN N)) /
      discriminantLaurentK N

theorem frickeF_eq_frickeH_div {N : ℕ} (a : Fin 2 → ZMod N) :
    frickeF N a = (fun _ : ℍ => (-1 / 2592 : ℂ)) *
      frickeH N (a 0).val (a 1).val / (⇑CuspForm.discriminant : ℍ → ℂ) := by
  funext τ
  apply (eq_div_iff (by simpa only [CuspForm.coe_discriminant] using discriminant_ne_zero τ)).mpr
  exact frickeF_mul_discriminant a τ

theorem represents_frickeLaurentK (N : ℕ) [NeZero N] (i : FrickeIdx N) :
    CuspTaylor.Represents (coeffMap (algebraMap (kN N) ℂ) (frickeLaurentK N i))
      (cuspFunction N (frickeF N i.1)) := by
  obtain ⟨h₁, h₂, h₀⟩ := frickeIdx_hyps i.1 i.2
  rw [frickeLaurentK, map_div₀, map_mul, map_div₀, map_neg, map_one, map_ofNat,
    coeffMap_ofPowerSeries, frickeHQSeriesK_map_inclusion h₁ h₂ h₀,
    coeffMap_discriminantLaurentK]
  have hc : CuspTaylor.Represents (-1 / 2592 : LaurentSeries ℂ)
      (cuspFunction N (fun _ : ℍ => (-1 / 2592 : ℂ))) := by
    simpa only [map_div₀, map_neg, map_one, map_ofNat] using CuspTaylor.represents_cusp_const N (-1 / 2592)
  have hH := CuspTaylor.represents_qExpansion (by exact_mod_cast NeZero.pos N)
    (periodic_frickeH h₁ h₂ h₀) (mdifferentiable_frickeH h₁ h₂ h₀)
    (isBoundedAtImInfty_frickeH h₁ h₂ h₀)
  rw [frickeF_eq_frickeH_div]
  exact (hc.cusp_mul hH).cusp_div (represents_discriminant_width N)

theorem periodic_frickeF {N : ℕ} [NeZero N] (i : FrickeIdx N) :
    Function.Periodic (frickeF N i.1 ∘ ofComplex) N := by
  obtain ⟨h₁, h₂, h₀⟩ := frickeIdx_hyps i.1 i.2
  have hH := periodic_frickeH h₁ h₂ h₀
  have hd := periodic_discriminant_width N
  rw [frickeF_eq_frickeH_div]
  intro z
  have hHz := hH z
  have hdz := hd z
  simp only [Function.comp_apply] at hHz hdz
  simp only [Function.comp_apply, Pi.mul_apply, Pi.div_apply, hHz, hdz]

end
end Dubon2026.SourceFricke