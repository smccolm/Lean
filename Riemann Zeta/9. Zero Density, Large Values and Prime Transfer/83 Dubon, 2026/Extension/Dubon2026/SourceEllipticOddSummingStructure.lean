import Dubon2026.SourceEllipticOddSummingSet

/-! Derive the actual odd Velu summing-set conditions and cardinality from
the order of its generator. Native injectivity below addOrderOf and the
already proved two-torsion criterion replace duplicate source arguments.
These discharge the summing-set inputs to the odd-degree quotient discriminant
and map needed for the DUB-17 / DUB-18 cyclic-subgroup inertia census.
Adapted from the Structure section of
S_WeierstrassCurve_veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow,
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. -/
namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F]
  {W : WeierstrassCurve F} {Q : W.toAffine.Point} {n : ℕ}

private theorem odd_multiple_ne_zero (hQ : addOrderOf Q = 2 * n + 1)
    {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ 2 * n) : k • Q ≠ 0 := by
  intro h
  have hdvd : 2 * n + 1 ∣ k := hQ ▸ addOrderOf_dvd_iff_nsmul_eq_zero.mpr h
  have := Nat.le_of_dvd (by omega) hdvd
  omega

private theorem odd_multiple_some (hQ : addOrderOf Q = 2 * n + 1)
    {k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ n) :
    ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      k • Q = WeierstrassCurve.Affine.Point.some x y h ∧
      coordsOrZero (k • Q) = (x, y) ∧ veluGy W x y ≠ 0 := by
  have hne := odd_multiple_ne_zero hQ hk₁ (show k ≤ 2 * n by omega)
  have htwo : 2 • (k • Q) ≠ 0 := by
    rw [← mul_nsmul]
    exact odd_multiple_ne_zero hQ (by omega) (by omega)
  cases heq : k • Q with
  | zero => exact (hne heq).elim
  | some x y h =>
    refine ⟨x, y, h, rfl, rfl, ?_⟩
    intro hgy
    exact htwo (heq ▸ two_nsmul_some_eq_zero_of_veluGy_eq_zero hgy h)

private theorem odd_multiple_eq_of_x_eq (hQ : addOrderOf Q = 2 * n + 1)
    {k l : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ n) (hl₁ : 1 ≤ l) (hl₂ : l ≤ n)
    {x y x' y' : F} {h : W.toAffine.Nonsingular x y} {h' : W.toAffine.Nonsingular x' y'}
    (hk : k • Q = WeierstrassCurve.Affine.Point.some x y h)
    (hl : l • Q = WeierstrassCurve.Affine.Point.some x' y' h') (hx : x = x') :
    k • Q = l • Q := by
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := h) (h₂ := h')).mp hx with he | he
  · exact hk.trans (he.trans hl.symm)
  · exfalso
    apply odd_multiple_ne_zero hQ (k := k + l) (by omega) (by omega)
    rw [add_nsmul, hk, hl, he, neg_add_cancel]

theorem isOddVeluSet_oddOrderSummingSet (hQ : addOrderOf Q = 2 * n + 1) :
    IsOddVeluSet W (oddOrderSummingSet W Q n) where
  equation P hP := by
    obtain ⟨k, hk₁, hk₂, rfl⟩ := mem_oddOrderSummingSet.mp hP
    obtain ⟨x, y, h, _, hc, _⟩ := odd_multiple_some hQ hk₁ hk₂
    rw [hc]
    exact h.left
  gy_ne_zero P hP := by
    obtain ⟨k, hk₁, hk₂, rfl⟩ := mem_oddOrderSummingSet.mp hP
    obtain ⟨x, y, _, _, hc, hgy⟩ := odd_multiple_some hQ hk₁ hk₂
    rw [hc]
    exact hgy
  x_injOn P hP P' hP' hx := by
    obtain ⟨k, hk₁, hk₂, rfl⟩ := mem_oddOrderSummingSet.mp hP
    obtain ⟨l, hl₁, hl₂, rfl⟩ := mem_oddOrderSummingSet.mp hP'
    obtain ⟨x, y, _, he, hc, _⟩ := odd_multiple_some hQ hk₁ hk₂
    obtain ⟨x', y', _, he', hc', _⟩ := odd_multiple_some hQ hl₁ hl₂
    rw [hc, hc'] at hx
    exact congrArg coordsOrZero (odd_multiple_eq_of_x_eq hQ hk₁ hk₂ hl₁ hl₂ he he' hx)

theorem coordsOrZero_odd_nsmul_injOn (hQ : addOrderOf Q = 2 * n + 1) :
    Set.InjOn (fun k : ℕ => coordsOrZero (k • Q)) (Finset.Icc 1 n : Finset ℕ) := by
  intro k hk l hl heq
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk hl
  obtain ⟨x, y, _, he, hc, _⟩ := odd_multiple_some hQ hk.1 hk.2
  obtain ⟨x', y', _, he', hc', _⟩ := odd_multiple_some hQ hl.1 hl.2
  have hx : x = x' := congrArg Prod.fst (hc.symm.trans (heq.trans hc'))
  apply nsmul_injOn_Iio_addOrderOf (x := Q) (by rw [Set.mem_Iio, hQ]; omega)
    (by rw [Set.mem_Iio, hQ]; omega)
  exact odd_multiple_eq_of_x_eq hQ hk.1 hk.2 hl.1 hl.2 he he' hx

theorem card_oddOrderSummingSet (hQ : addOrderOf Q = 2 * n + 1) :
    (oddOrderSummingSet W Q n).card = n := by
  rw [oddOrderSummingSet, Finset.card_image_of_injOn (coordsOrZero_odd_nsmul_injOn hQ),
    Nat.card_Icc, Nat.add_sub_cancel]

end
end Dubon2026.SourceEllipticVelu
