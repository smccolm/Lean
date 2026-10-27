import Dubon2026.SourcePoleBoundedCuspLaurent

/-! DUB-17/18 -> actual Gamma1 cusp realization -> rational Fourier spanning
-> pole-cleared cyclotomic Fourier coefficients. Reuse the existing
meromorphic cusp germs and native order/limit theorems. The discriminant
has positive cusp order, so a power clears every meromorphic cusp pole.
This avoids repeating the external coefficient-recursion and growth engine. -/
namespace Dubon2026.SourceFricke
noncomputable section
open UpperHalfPlane SourceFunctionField Filter
open scoped Topology Manifold ModularForm

theorem exists_nonnegative_add_nat_mul {a b : WithTop ℤ} (hb : 0 < b) :
    ∃ m : ℕ, 0 ≤ a + m * b := by
  cases a with
  | top => exact ⟨0, by simp⟩
  | coe a =>
    cases b with
    | top => exact ⟨1, by simp⟩
    | coe b =>
      have hb' : 0 < b := by exact_mod_cast hb
      refine ⟨a.natAbs, ?_⟩
      have hneg : -(a.natAbs : ℤ) ≤ a := by
        simpa only [Int.natCast_natAbs] using neg_abs_le a
      have hm := mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ b by omega)
        (Int.natCast_nonneg a.natAbs)
      have hz : 0 ≤ a + (a.natAbs : ℤ) * b := by linarith
      simpa only [WithTop.coe_add, WithTop.coe_mul, WithTop.coe_natCast, WithTop.coe_zero] using
        (show ((0 : ℤ) : WithTop ℤ) ≤ (a + (a.natAbs : ℤ) * b : ℤ) from WithTop.coe_le_coe.mpr hz)

theorem meromorphicOrderAt_discriminant_cusp_pos (N : ℕ) [NeZero N] :
    0 < meromorphicOrderAt (cuspFunction N (⇑CuspForm.discriminant : ℍ → ℂ)) 0 := by
  have hh : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have ha := analyticAt_cuspFunction_zero hh (periodic_discriminant_width N)
    CuspForm.discriminant.holo' (ModularFormClass.bdd_at_infty CuspForm.discriminant)
  apply (tendsto_zero_iff_meromorphicOrderAt_pos ha.meromorphicAt).mp
  have ht := (ha.continuousAt.continuousWithinAt (s := ({0}ᶜ : Set ℂ))).tendsto
  have hz := (CuspFormClass.zero_at_infty CuspForm.discriminant).cuspFunction_apply_zero hh
  rw [hz] at ht
  exact ht

theorem periodic_mul_discriminant {N : ℕ} {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ ofComplex) N) (m : ℕ) :
    Function.Periodic ((F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) ∘ ofComplex) N := by
  intro z
  exact congrArg₂ (fun a b : ℂ => a * b ^ m) (hper z) (periodic_discriminant_width N z)

theorem exists_bounded_mul_discriminant_of_meromorphic {N : ℕ} [NeZero N] {F : ℍ → ℂ}
    (hper : Function.Periodic (F ∘ ofComplex) N)
    (hmer : MeromorphicAt (cuspFunction N F) 0) :
    ∃ m : ℕ, IsBoundedAtImInfty (F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) := by
  have hd := (represents_discriminant_width N).meromorphicAt
  obtain ⟨m, hm⟩ := exists_nonnegative_add_nat_mul
    (a := meromorphicOrderAt (cuspFunction N F) 0) (meromorphicOrderAt_discriminant_cusp_pos N)
  let G : ℂ → ℂ := cuspFunction N F * (cuspFunction N (⇑CuspForm.discriminant : ℍ → ℂ)) ^ m
  have hG : MeromorphicAt G 0 := hmer.mul (hd.pow m)
  have hGo : 0 ≤ meromorphicOrderAt G 0 := by
    rw [meromorphicOrderAt_mul hmer (hd.pow m), meromorphicOrderAt_pow hd]
    exact hm
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hG hGo
  have he : G =ᶠ[𝓝[≠] (0 : ℂ)]
      cuspFunction N (F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    simp only [G, cuspFunction, Function.Periodic.cuspFunction_eq_of_nonzero _ _ hq,
      Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
  have hh : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have ht := (hc.congr' he).comp
    ((Function.Periodic.qParam_tendsto hh).comp tendsto_coe_atImInfty)
  have ht' : Tendsto (F * ⇑CuspForm.discriminant ^ m : ℍ → ℂ) atImInfty (𝓝 c) := by
    convert ht using 1
    funext τ
    exact (eq_cuspFunction τ hh.ne' (periodic_mul_discriminant hper m)).symm
  exact ⟨m, ht'.isBigO_one ℝ⟩

end
end Dubon2026.SourceFricke