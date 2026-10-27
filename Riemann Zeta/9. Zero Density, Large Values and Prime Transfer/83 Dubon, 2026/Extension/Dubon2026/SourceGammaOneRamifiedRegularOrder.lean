import Dubon2026.SourceGammaOneRamifiedRegularParameter

/-! DUB-17/18 -> actual Gamma1 period comparison -> actual complex place
charts. Power pullback multiplies analytic order by the exact ramification.
The existing original order formula supplies the same factor on the
original realization. Cancelling its proved positive integer value gives
the exact normalized order on the descended original place family.
-/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter EllipticCoordinate CongruenceSubgroup
open scoped Topology

theorem ramifiedPlace_regular_order (N : ℕ) [NeZero N] (hT : ModularGroup.T ∈ Gamma1 N) (τ : ℍ)
    (f : functionFieldOver (Gamma1 N) ℂ) (hf0 : f ≠ 0)
    (hf : f ∈ (analyticPlace hT τ).toValuationSubring) :
    meromorphicOrderAt (fun z => placeEval hT (ramifiedPlace N hT τ z) f) 0 =
      ((analyticPlace hT τ).ord f : WithTop ℤ) := by
  let e := analyticRamification hT τ
  have he : e ≠ 0 := (analyticRamification_pos hT τ).ne'
  let H : ℂ → ℂ := fun z => placeEval hT (ramifiedPlace N hT τ z) f
  let F : ℂ → ℂ := fun z => placeEval hT (analyticPlace hT (ofComplex z)) f
  obtain ⟨hH, hcomp⟩ := ramifiedPlace_regular_analytic N hT τ f hf
  have hpow : AnalyticAt ℂ (fun z : ℂ => z ^ e) 0 := analyticAt_id.pow e
  have hpowOrder : analyticOrderAt (fun z : ℂ => z ^ e - (0 : ℂ) ^ e) 0 = (e : ℕ∞) := by
    simpa only [zero_pow he, sub_zero, analyticOrderAt_id, nsmul_one] using
      analyticOrderAt_pow (f := id) (z₀ := (0 : ℂ)) analyticAt_id e
  have hnc : ¬EventuallyConst (fun z : ℂ => z ^ e) (𝓝 0) := by
    rw [eventuallyConst_iff_analyticOrderAt_sub_eq_top, hpowOrder]
    exact ENat.coe_ne_top e
  have hHz : MeromorphicAt H ((0 : ℂ) ^ e) := by
    simpa only [zero_pow he] using hH.meromorphicAt
  have hc := hHz.meromorphicOrderAt_comp hpow hnc
  change meromorphicOrderAt (H ∘ (fun z : ℂ => z ^ e)) 0 =
    meromorphicOrderAt H ((0 : ℂ) ^ e) *
      (analyticOrderAt (fun z : ℂ => z ^ e - (0 : ℂ) ^ e) 0).map Nat.cast at hc
  rw [hpowOrder] at hc
  simp only [zero_pow he, ENat.map_coe] at hc
  have horder : meromorphicOrderAt (H ∘ (fun z : ℂ => z ^ e)) 0 =
      (((e : ℤ) * (analyticPlace hT τ).ord f : ℤ) : WithTop ℤ) := by
    have heq : H ∘ (fun z : ℂ => z ^ e) =ᶠ[𝓝[≠] (0 : ℂ)] F ∘ param τ :=
      hcomp.filter_mono nhdsWithin_le_nhds
    rw [meromorphicOrderAt_congr heq]
    change meromorphicOrderAt (F ∘ param τ) 0 = _
    rw [meromorphicOrderAt_comp_of_deriv_ne_zero (analyticAt_param τ) (deriv_param_ne_zero τ),
      param_zero, placeEval_meromorphicOrderAt hT f hf0 τ]
  have hm : meromorphicOrderAt H 0 * ((e : ℤ) : WithTop ℤ) =
      (((e : ℤ) * (analyticPlace hT τ).ord f : ℤ) : WithTop ℤ) := hc.symm.trans horder
  have hez : ((e : ℤ) : WithTop ℤ) ≠ 0 := by exact_mod_cast he
  have hfin : meromorphicOrderAt H 0 ≠ ⊤ := by
    intro ht
    rw [ht, WithTop.top_mul hez] at hm
    exact WithTop.top_ne_coe hm
  obtain ⟨m, hm0⟩ := WithTop.ne_top_iff_exists.mp hfin
  rw [← hm0, ← WithTop.coe_mul] at hm
  have hi : m * (e : ℤ) = (e : ℤ) * (analyticPlace hT τ).ord f := WithTop.coe_injective hm
  have hm' : m = (analyticPlace hT τ).ord f := by
    apply mul_right_cancel₀ (show (e : ℤ) ≠ 0 by exact_mod_cast he)
    simpa only [mul_comm] using hi
  change meromorphicOrderAt H 0 = _
  rw [← hm0, hm']

end
end Dubon2026.SourceFunctionField.GammaOne
