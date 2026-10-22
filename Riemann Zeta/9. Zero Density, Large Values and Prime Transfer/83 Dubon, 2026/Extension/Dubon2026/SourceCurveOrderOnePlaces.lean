import Dubon2026.SourceCurveOrderMapPlaces

/-! DUB-17/18 -> original torsion cardinality -> actual normalized cusp chart.
The existing integer-order place construction has normalization factor
one whenever an actual function has order one. The cusp uniformizer
differences supply this input, so no ramification factor remains locally.
-/
namespace Dubon2026.SourceCurve.Place
noncomputable section

theorem exists_place_of_orderMap_of_order_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    (μ : F → WithTop ℤ) (h_top : ∀ x, μ x = ⊤ ↔ x = 0)
    (h_mul : ∀ x y, μ (x * y) = μ x + μ y) (h_add : ∀ x y, min (μ x) (μ y) ≤ μ (x + y))
    (h_const : ∀ c : K, c ≠ 0 → μ (algebraMap K F c) = 0)
    (t : F) (ht : μ t = (1 : ℤ)) :
    ∃ P : Place K F, (∀ x, x ∈ P.toValuationSubring ↔ 0 ≤ μ x) ∧
      ∀ x, x ≠ 0 → μ x = (P.ord x : WithTop ℤ) := by
  have ht_top : μ t ≠ ⊤ := by rw [ht]; exact WithTop.coe_ne_top
  have ht_ne : t ≠ 0 := fun h => ht_top ((h_top t).mpr h)
  obtain ⟨P, e, he, hmem, hord⟩ := exists_place_of_orderMap μ h_top h_mul h_add h_const
    ⟨t, by rw [ht]; norm_num, ht_top⟩
  have hprod : (e : ℤ) * P.ord t = 1 := WithTop.coe_injective ((hord t ht_ne).symm.trans ht)
  have hez : 0 < (e : ℤ) := by exact_mod_cast he
  have htz : 0 < P.ord t := (mul_pos_iff_of_pos_left hez).mp (by rw [hprod]; norm_num)
  have he1 : (e : ℤ) = 1 := by nlinarith
  refine ⟨P, hmem, fun x hx => ?_⟩
  simpa only [he1, one_mul] using hord x hx

end
end Dubon2026.SourceCurve.Place
