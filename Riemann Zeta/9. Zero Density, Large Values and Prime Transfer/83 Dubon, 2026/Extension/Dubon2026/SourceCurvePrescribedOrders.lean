import Dubon2026.SourceCurveFinitePlaceIndicators

/-! DUB-17/18 -> full original Picard-period Hecke compatibility ->
moving every divisor class away from the cusps -> finite prescribed orders.
Adapted from S_AlgebraicCurve_Place_exists_forall_ord_eq,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Existing actual place separation, uniformizers and valuation/order identities
supply the foundations. No global approximation hypothesis is introduced.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_forall_ord_eq_of_sep (T : Finset (Place K F)) (n : Place K F → ℤ)
    (hsep : ∀ v ∈ T, ∃ z : F, v.ord z < 0 ∧ ∀ w ∈ T, w ≠ v → 0 < w.ord z) :
    ∃ f : F, f ≠ 0 ∧ ∀ v ∈ T, v.ord f = n v := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hT
  · exact ⟨1, one_ne_zero, by simp⟩

  have hunif : ∀ v : Place K F, ∃ π : F, π ≠ 0 ∧ v.ord π = 1 := fun v => by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
    refine ⟨ϖ, ?_, v.ord_coe_irreducible hϖ⟩
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hϖ.ne_zero
  choose π hπ0 hπ1 using hunif

  set t : Place K F → F := fun v => π v ^ n v with ht
  have ht0 : ∀ v, t v ≠ 0 := fun v => zpow_ne_zero _ (hπ0 v)
  have htord : ∀ v w : Place K F, w.ord (t v) = n v * w.ord (π v) := fun v w => by
    rw [ht, ord_zpow]
  have htv : ∀ v, v.ord (t v) = n v := fun v => by rw [htord, hπ1, mul_one]

  set B : ℤ := 1 + ∑ v ∈ T, ∑ w ∈ T, (|n v| + |v.ord (t w)|) with hBdef
  have hB : ∀ v ∈ T, ∀ w ∈ T, n v - v.ord (t w) + 1 ≤ B := by
    intro v hv w hw
    have h1 : |n v| + |v.ord (t w)| ≤ ∑ w' ∈ T, (|n v| + |v.ord (t w')|) :=
      Finset.single_le_sum (f := fun w' => |n v| + |v.ord (t w')|)
        (fun _ _ => by positivity) hw
    have h2 : ∑ w' ∈ T, (|n v| + |v.ord (t w')|)
        ≤ ∑ v' ∈ T, ∑ w' ∈ T, (|n v'| + |v'.ord (t w')|) :=
      Finset.single_le_sum (f := fun v' => ∑ w' ∈ T, (|n v'| + |v'.ord (t w')|))
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) hv
    have h3 : n v ≤ |n v| := le_abs_self _
    have h4 : -v.ord (t w) ≤ |v.ord (t w)| := neg_le_abs _
    omega

  have hind : ∀ v : Place K F, ∃ e : F, v ∈ T →
      (v.adicValuation (e - 1) ≤ WithZero.exp (-B) ∧
        ∀ w ∈ T, w ≠ v → w.adicValuation e ≤ WithZero.exp (-B)) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨z, hz, hzT⟩ := hsep v hv
      obtain ⟨e, he⟩ := exists_indicator T hz hzT B
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose e he using hind

  have main : ∀ v ∈ T, v.adicValuation (∑ w ∈ T, t w * e w) = WithZero.exp (-(n v)) := by
    intro v hv
    have hsplit : ∑ w ∈ T, t w * e w = t v + (t v * (e v - 1) + ∑ w ∈ T.erase v, t w * e w) := by
      rw [← Finset.add_sum_erase T (fun w => t w * e w) hv]
      ring
    have hvt : v.adicValuation (t v) = WithZero.exp (-(n v)) := by
      rw [v.adicValuation_eq_exp_neg_ord (ht0 v), htv]
    have hsmall : v.adicValuation (t v * (e v - 1) + ∑ w ∈ T.erase v, t w * e w)
        ≤ WithZero.exp (-(n v + 1)) := by
      apply Valuation.map_add_le
      · rw [map_mul, hvt]
        calc WithZero.exp (-(n v)) * v.adicValuation (e v - 1)
            ≤ WithZero.exp (-(n v)) * WithZero.exp (-B) := mul_le_mul_right (he v hv).1 _
          _ = WithZero.exp (-(n v) + -B) := (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp (-(n v + 1)) := WithZero.exp_le_exp.mpr (by
              have h := hB v hv v hv
              rw [htv] at h
              omega)
      · apply Valuation.map_sum_le
        intro w hw
        obtain ⟨hwv, hwT⟩ := Finset.mem_erase.mp hw
        rw [map_mul, v.adicValuation_eq_exp_neg_ord (ht0 w)]
        calc WithZero.exp (-(v.ord (t w))) * v.adicValuation (e w)
            ≤ WithZero.exp (-(v.ord (t w))) * WithZero.exp (-B) :=
              mul_le_mul_right ((he w hwT).2 v hv hwv.symm) _
          _ = WithZero.exp (-(v.ord (t w)) + -B) := (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp (-(n v + 1)) := WithZero.exp_le_exp.mpr (by
              have h := hB v hv w hwT
              omega)
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ (lt_of_le_of_lt hsmall ?_), hvt]
    rw [hvt, WithZero.exp_lt_exp]
    omega
  obtain ⟨v₀, hv₀⟩ := hT
  have hf0 : (∑ w ∈ T, t w * e w) ≠ 0 := by
    intro h0
    have h := main v₀ hv₀
    rw [h0, map_zero] at h
    exact WithZero.exp_ne_zero h.symm
  refine ⟨∑ w ∈ T, t w * e w, hf0, fun v hv => ?_⟩
  have h := main v hv
  rw [v.adicValuation_eq_exp_neg_ord hf0, WithZero.exp_inj] at h
  omega

end
end Dubon2026.SourceCurve.Place
