import Dubon2026.SourceOriginalAnalyticChart

/-! DUB-17/18 -> finite analytic-place exhaustion. Existing actual
Dedekind-center localization identifies two original places from their
centers. A denominator outside the center is a unit in the valuation
ring, so a cleared-denominator relation proves membership. These are
the local steps of the missing-place contradiction, using the original
integral-closure chart without introducing another local model.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_ComplexPlaceDictionary_exists_pt_eq_of_mem.
-/
namespace Dubon2026.SourceFunctionField.AnalyticChart
noncomputable section
open SourceCurve
open scoped IntermediateField.algebraAdjoinAdjoin
variable (N : ℕ) [NeZero N]

theorem eq_of_center_eq {Q Q' : Place ℂ (F N)}
    (hQ : ∀ b : B N, algebraMap (B N) (F N) b ∈ Q.toValuationSubring)
    (hQ' : ∀ b : B N, algebraMap (B N) (F N) b ∈ Q'.toValuationSubring)
    (h : Place.center (B N) Q hQ = Place.center (B N) Q' hQ') : Q = Q' := by
  apply Place.ext
  rw [Place.toValuationSubring_eq_of_forall_mem Q hQ, Place.toValuationSubring_eq_of_forall_mem Q' hQ']
  have hc : Place.centerHeightOneSpectrum (B N) Q hQ = Place.centerHeightOneSpectrum (B N) Q' hQ' :=
    IsDedekindDomain.HeightOneSpectrum.ext h
  rw [hc]

omit [NeZero N] in
theorem mem_of_mul_eq {Q : Place ℂ (F N)}
    (hQ : ∀ b : B N, algebraMap (B N) (F N) b ∈ Q.toValuationSubring)
    {x : F N} {b s : B N} (hs : s ∉ Place.center (B N) Q hQ)
    (hx : x * algebraMap (B N) (F N) s = algebraMap (B N) (F N) b) :
    x ∈ Q.toValuationSubring := by
  set O := Q.toValuationSubring
  have hsunit : IsUnit (⟨algebraMap (B N) (F N) s, hQ s⟩ : O) :=
    IsLocalRing.notMem_maximalIdeal.mp (fun hm => hs ((Place.mem_center_iff Q hQ).mpr hm))
  have hv1 : O.valuation (algebraMap (B N) (F N) s) = 1 :=
    (O.valuation_eq_one_iff _).mp hsunit
  have hs0 : algebraMap (B N) (F N) s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv1
    exact zero_ne_one hv1
  have hxeq : x = algebraMap (B N) (F N) b * (algebraMap (B N) (F N) s)⁻¹ := by
    rw [← hx, mul_inv_cancel_right₀ hs0]
  rw [← O.valuation_le_one_iff, hxeq, map_mul, map_inv₀, hv1, inv_one, mul_one]
  exact O.valuation_le_one ⟨_, hQ b⟩

end
end Dubon2026.SourceFunctionField.AnalyticChart
