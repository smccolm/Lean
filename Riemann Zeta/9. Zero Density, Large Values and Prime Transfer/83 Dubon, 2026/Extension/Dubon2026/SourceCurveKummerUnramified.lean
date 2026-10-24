import Dubon2026.SourceCurveKummerNorm
import Dubon2026.SourceCurveKummerLocalOrders
import Dubon2026.SourceCurveCompletionEmbeddingValuation

/-! DUB-17/18 -> original Frobenius/inertia -> Picard torsion injectivity ->
power lifting -> genus of an unramified Kummer cover. The actual normalized
ramification index is one when all base orders of the defining function are
divisible by the prime degree. Existing norm fibers, local units and place
restriction replace the external evaluation-map infrastructure. Adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_AlgebraicCurve_Place_ramificationIndex_eq_one_of_forall_dvd_ord. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
open IsLocalRing IntermediateField

private theorem ord_root_eq_zero
    {K F E : Type*} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [Algebra.IsIntegral F E] (w : Place K E) {q : ℕ} (hq : q ≠ 0)
    {f : F} {β : E} (hβ : β ^ q = algebraMap F E f)
    (hf : (w.restrict F).ord f = 0) : w.ord β = 0 := by
  have h := w.ord_algebraMap_restrict f
  rw [hf, zero_mul, ← hβ, ← zpow_natCast, w.ord_zpow] at h
  exact (mul_eq_zero.mp h).resolve_left (Int.natCast_ne_zero.mpr hq)

theorem ramificationIndex_eq_one_of_kummer_orders
    {K F E : Type*} [Field K] [CharZero K] [Field F] [Field E]
    [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    {q : ℕ} [hq : Fact q.Prime] {f : F} {α : E}
    (hf : ∀ g : F, g ^ q ≠ f) (hα : α ^ q = algebraMap F E f)
    (htop : F⟮α⟯ = ⊤) (hord : ∀ v : Place K F, (q : ℤ) ∣ v.ord f)
    (hbase : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (htopres : ∀ v : Place K E, Function.Bijective (algebraMap K v.ResidueField))
    (w : Place K E) : w.ramificationIndex (F := F) = 1 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  let v := w.restrict F
  have hf0 : f ≠ 0 := by rintro rfl; exact hf 0 (zero_pow hq.out.ne_zero)
  obtain ⟨m, hm⟩ := hord v
  let h : F := v.uniformizer ^ (-m)
  have hh0 : h ≠ 0 := zpow_ne_zero _ v.uniformizer_ne_zero
  let f₁ := f * h ^ q
  have hf₁ : ∀ g : F, g ^ q ≠ f₁ := by
    intro g hg
    apply hf (g / h)
    rw [div_pow, hg, mul_div_cancel_right₀ _ (pow_ne_zero _ hh0)]
  have hf₁0 : f₁ ≠ 0 := mul_ne_zero hf0 (pow_ne_zero _ hh0)
  have hfv : v.ord f₁ = 0 := by
    rw [show f₁ = f * h ^ q from rfl, v.ord_mul hf0 (pow_ne_zero _ hh0),
      ← zpow_natCast, v.ord_zpow]
    change v.ord f + (q : ℤ) * v.ord (v.uniformizer ^ (-m)) = 0
    rw [v.ord_zpow, v.ord_uniformizer, hm]
    ring
  let β : E := α * algebraMap F E h
  have hβ : β ^ q = algebraMap F E f₁ := by
    rw [show β = α * algebraMap F E h from rfl, mul_pow, hα, ← map_pow, ← map_mul]
  have hβtop : F⟮β⟯ = ⊤ := by
    rw [eq_top_iff, ← htop, adjoin_simple_le_iff]
    have h1 := mem_adjoin_simple_self F β
    have h2 := IntermediateField.algebraMap_mem F⟮β⟯ h⁻¹
    have h3 := mul_mem h1 h2
    dsimp only [β] at h3
    rwa [mul_assoc, ← map_mul, mul_inv_cancel₀ hh0, map_one, mul_one] at h3
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_pow hq.out.ne_zero] at hβ
    exact hf₁0 ((algebraMap F E).injective (hβ.symm.trans (map_zero _).symm))
  have hβord : w.ord β = 0 := ord_root_eq_zero w hq.out.ne_zero hβ hfv
  have hβmem : β ∈ w.toValuationSubring := w.mem_of_ord_nonneg hβord.ge
  obtain ⟨c, hc⟩ := (htopres w).2 (residue w.toValuationSubring ⟨β, hβmem⟩)
  have hc0 : c ≠ 0 := by
    intro h0
    have hu : IsUnit (⟨β, hβmem⟩ : w.toValuationSubring) :=
      ConstantField.isUnit_of_ord_eq_zero w (fun h => hβ0 (congrArg Subtype.val h)) hβord
    apply (residue_ne_zero_iff_isUnit _).mpr hu
    rw [← hc, h0, map_zero]
  let cF := algebraMap K F c
  let cE := algebraMap K E c
  have hcE : cE = algebraMap F E cF := IsScalarTower.algebraMap_apply K F E c
  have hne : β - cE ≠ 0 := by
    intro hzero
    have heq : β = algebraMap F E cF := (sub_eq_zero.mp hzero).trans hcE
    rw [heq, ← map_pow] at hβ
    exact hf₁ cF ((algebraMap F E).injective hβ)
  have hmpos : 0 < w.ord (β - cE) := by
    let Z : w.toValuationSubring := ⟨β, hβmem⟩ - algebraMap K w.toValuationSubring c
    have hZ0 : (Z : E) ≠ 0 := hne
    apply (w.mem_maximalIdeal_iff_ord_pos hZ0 Z.2).mp
    rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
    rw [← hc]
    exact (IsScalarTower.algebraMap_apply K w.toValuationSubring w.ResidueField c)
  let f₂ := f₁ - cF ^ q
  have hpow : w.ord (algebraMap F E f₂) = w.ord (β - cE) := by
    have heq : algebraMap F E f₂ = β ^ q - cE ^ q := by
      rw [show f₂ = f₁ - cF ^ q from rfl, map_sub, map_pow, ← hβ, ← hcE]
    rw [heq]
    exact w.ord_pow_sub_constant_of_same_residue hβmem hc0 hc.symm hne hq.out.ne_zero
  have hnorm : v.ord (Algebra.norm F (β - cE)) = v.ord f₂ := by
    rw [hcE, KummerCover.ord_norm_root_sub_algebraMap v hf₁ hβ hβtop cF]
  have hle : w.ord (β - cE) ≤ v.ord f₂ := by
    rw [← hnorm]
    apply ord_le_ord_norm_of_nonnegative_fiber w (hbase v) htopres hne
    intro w' hw'
    have hβord' : w'.ord β = 0 :=
      ord_root_eq_zero w' hq.out.ne_zero hβ (by rw [hw']; exact hfv)
    exact w'.ord_nonneg_of_mem (sub_mem (w'.mem_of_ord_nonneg hβord'.ge)
      (w'.algebraMap_mem' c))
  have heq := w.ord_algebraMap_restrict f₂
  rw [hpow, ← w.ramificationIndex_cast] at heq
  have hep := w.ramificationIndex_pos (F := F)
  have hvpos : 0 < v.ord f₂ := hmpos.trans_le hle
  have heone : (w.ramificationIndex (F := F) : ℤ) ≤ 1 := by
    change w.ord (β - cE) = v.ord f₂ * _ at heq
    nlinarith
  omega

end
end Dubon2026.SourceCurve.Place
