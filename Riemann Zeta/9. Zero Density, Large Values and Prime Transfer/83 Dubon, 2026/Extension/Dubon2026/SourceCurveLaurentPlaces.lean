import Dubon2026.SourceLaurentOrderValuation
import Dubon2026.SourceCurveLocalDifferentials
import Dubon2026.SourceLaurentEuler

/-! DUB-17/18 -> numerical modular genus -> cusp classification -> genuine
places attached to actual Laurent embeddings. The native Laurent valuation
is pulled back to the function field. Its cyclic value group makes the
nontrivial valuation ring principal. Unit/uniformizer decomposition then
derives the exact positive integer scaling of normalized place orders.
This replaces the external rational-exponent/Puiseux route with existing
integer-valued valuation and original place APIs.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open SourceFunctionField WithZero
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_place_of_laurent_embedding (ι : F →ₐ[K] LaurentSeries K)
    (hnt : ∃ f : F, (ι f).order ≠ 0) :
    ∃ (w : Place K F) (γ : ℕ), 0 < γ ∧ ∀ f : F, w.ord f * (γ : ℤ) = (ι f).order := by
  let v : Valuation F ℤᵐ⁰ := (Valued.v : Valuation (LaurentSeries K) ℤᵐ⁰).comap ι.toRingHom
  have hmem : ∀ f : F, f ∈ v.valuationSubring ↔ 0 ≤ (ι f).order :=
    fun f => laurent_valuation_mem_iff (ι f)
  have htop : v.valuationSubring ≠ ⊤ := by
    intro he
    obtain ⟨f, hf⟩ := hnt
    have h1 := (hmem f).mp (he ▸ ValuationSubring.mem_top f)
    have h2 := (hmem f⁻¹).mp (he ▸ ValuationSubring.mem_top f⁻¹)
    rw [map_inv₀, laurent_order_inv] at h2
    omega
  haveI : v.IsNontrivial := by
    by_contra hn
    exact htop ((Valuation.valuationSubring_eq_top_iff (v := v)).mpr hn)
  haveI : IsCyclic (MonoidWithZeroHom.valueGroup v) := inferInstance
  let w : Place K F :=
    { toValuationSubring := v.valuationSubring
      algebraMap_mem' := fun c => by
        rw [hmem, ι.commutes, SourceDifferential.algebraMap_laurentSeries_apply_alt]
        rcases eq_or_ne c 0 with rfl | hc
        · simp
        · rw [HahnSeries.order_single hc]
      ne_top' := htop
      isPrincipalIdealRing' := Valuation.valuationSubring_isPrincipalIdealRing v }
  have hwm : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order := hmem
  have hπmem : w.uniformizer ∈ w.toValuationSubring :=
    (IsDiscreteValuationRing.exists_irreducible w.toValuationSubring).choose.2
  have hπpos : 0 < (ι w.uniformizer).order := by
    have hnonneg := (hwm _).mp hπmem
    by_contra hn
    have hz : (ι w.uniformizer).order = 0 := by omega
    have hi : w.uniformizer⁻¹ ∈ w.toValuationSubring := by
      rw [hwm, map_inv₀, laurent_order_inv, hz, neg_zero]
    have hb := w.ord_nonneg_of_mem hi
    rw [w.ord_inv, w.ord_uniformizer] at hb
    omega
  have hu0 : ∀ u : w.toValuationSubringˣ, (ι ((u : w.toValuationSubring) : F)).order = 0 := by
    intro u
    let ui : w.toValuationSubringˣ := u⁻¹
    have h1 := (hwm _).mp (u : w.toValuationSubring).2
    have h2 := (hwm _).mp (ui : w.toValuationSubring).2
    have huF : ((u : w.toValuationSubring) : F) ≠ 0 := by exact_mod_cast u.ne_zero
    have hvF : ((ui : w.toValuationSubring) : F) ≠ 0 := by exact_mod_cast ui.ne_zero
    have hU : ι ((u : w.toValuationSubring) : F) ≠ 0 := by
      simpa only [map_zero] using ι.injective.ne huF
    have hV : ι ((ui : w.toValuationSubring) : F) ≠ 0 := by
      simpa only [map_zero] using ι.injective.ne hvF
    have he : ι ((u : w.toValuationSubring) : F) * ι ((ui : w.toValuationSubring) : F) = 1 := by
      rw [← map_mul]
      change ι (algebraMap w.toValuationSubring F
        ((u : w.toValuationSubring) * ((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring))) = 1
      simp only [Units.mul_inv, map_one]
    have ho := HahnSeries.order_mul hU hV
    rw [he, HahnSeries.order_one] at ho
    omega
  refine ⟨w, (ι w.uniformizer).order.toNat, by omega, ?_⟩
  intro f
  rw [Int.toNat_of_nonneg hπpos.le]
  rcases eq_or_ne f 0 with rfl | hf
  · rw [w.ord_zero, zero_mul, map_zero, HahnSeries.order_zero]
  obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf
    (IsDiscreteValuationRing.exists_irreducible w.toValuationSubring).choose_spec
  change f = ((u : w.toValuationSubring) : F) * w.uniformizer ^ w.ord f at hu
  have huF : ((u : w.toValuationSubring) : F) ≠ 0 := by exact_mod_cast u.ne_zero
  have hU : ι ((u : w.toValuationSubring) : F) ≠ 0 := by
    simpa only [map_zero] using ι.injective.ne huF
  have hπ : ι w.uniformizer ≠ 0 := by
    simpa only [map_zero] using ι.injective.ne w.uniformizer_ne_zero
  conv_rhs => rw [hu, map_mul, map_zpow₀]
  rw [HahnSeries.order_mul hU (zpow_ne_zero _ hπ), hu0, zero_add, laurent_order_zpow]

end
end Dubon2026.SourceCurve.Place
