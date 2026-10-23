import Dubon2026.SourcePrimeTwoSymmetricIdentities

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> continuation -> original
Frobenius/inertia -> good reduction -> reverse genus -> elliptic inertia orbits
-> cyclic-quotient interpretation of integral modular-polynomial roots.
This step factors the explicit classical prime-two polynomial into the j-values
of the three actual degree-two Velu curves. Identification of this explicit
polynomial with the existing integral minimal polynomial is a separate required
bridge. The quotient group homomorphism and its kernel remain required too.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the VeluQuotient2 cFour/j solutions,
Def_ModularCurve_ClassicalModularPolynomials, Def_ModularCurve_FibrePoly and
S_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j. -/
namespace Dubon2026.SourcePrimeTwoPolynomial
open Polynomial WeierstrassCurve
open Dubon2026.SourceEllipticVelu
noncomputable section
theorem fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, veluGy W (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (veluQuotient2 W (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly phiTwo W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (veluQuotient2 W (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  classical

  have hy : ∀ i, (P i).2 = -(W.a₁ * (P i).1 + W.a₃) / 2 := by
    intro i
    have hg := hPgy i
    simp only [veluGy, neg_eq_zero] at hg
    rw [eq_div_iff h2]
    linear_combination hg
  have hroot : ∀ i, W.Ψ₂Sq.eval (P i).1 = 0 := by
    intro i
    rw [← veluU_eq_Ψ₂Sq_eval W (hPeq i)]
    simp [veluU, hPgy i]
  have hinjx : ∀ {i i' : ι}, (P i).1 = (P i').1 → i = i' := by
    intro i i' hx
    apply hP
    exact Prod.ext hx (by rw [hy i, hy i', hx])

  obtain ⟨e⟩ : Nonempty (ι ≃ Fin 3) := ⟨Fintype.equivFinOfCardEq hι⟩
  have hre : ∀ f : ι → K[X], ∏ i, f i = ∏ k : Fin 3, f (e.symm k) := fun f =>
    (Fintype.prod_equiv e.symm (fun k => f (e.symm k)) f (fun _ => rfl)).symm
  rw [hre, Fin.prod_univ_three]
  set x0 := (P (e.symm 0)).1 with hx0
  set y0 := (P (e.symm 0)).2 with hy0
  set x1 := (P (e.symm 1)).1 with hx1
  set y1 := (P (e.symm 1)).2 with hy1
  set x2 := (P (e.symm 2)).1 with hx2
  set y2 := (P (e.symm 2)).2 with hy2
  have h01 : x0 ≠ x1 := fun h => by have := e.symm.injective (hinjx h); exact absurd this (by decide)
  have h02 : x0 ≠ x2 := fun h => by have := e.symm.injective (hinjx h); exact absurd this (by decide)
  have h12 : x1 ≠ x2 := fun h => by have := e.symm.injective (hinjx h); exact absurd this (by decide)

  have hq : W.Ψ₂Sq - C 4 * ((X - C x0) * (X - C x1) * (X - C x2))
      = C (W.b₂ + 4 * (x0 + x1 + x2)) * X ^ 2 + C (2 * W.b₄ - 4 * (x0 * x1 + x0 * x2 + x1 * x2)) * X
        + C (W.b₆ + 4 * (x0 * x1 * x2)) := by
    rw [WeierstrassCurve.Ψ₂Sq]
    simp only [map_add, map_sub, map_mul, map_ofNat]
    ring
  have hq0 : C (W.b₂ + 4 * (x0 + x1 + x2)) * X ^ 2 + C (2 * W.b₄ - 4 * (x0 * x1 + x0 * x2 + x1 * x2)) * X
        + C (W.b₆ + 4 * (x0 * x1 * x2)) = 0 := by
    rw [← hq]
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ {x0, x1, x2}
    · intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · rw [hx0]; simp [hroot (e.symm 0)]
      · rw [hx1]; simp [hroot (e.symm 1)]
      · rw [hx2]; simp [hroot (e.symm 2)]
    · rw [hq]
      refine lt_of_le_of_lt natDegree_quadratic_le ?_
      rw [Finset.card_insert_of_notMem (by simp [h01, h02]), Finset.card_insert_of_notMem (by simp [h12]),
        Finset.card_singleton]
      norm_num
  have hA : W.b₂ + 4 * (x0 + x1 + x2) = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff 2) hq0
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h
    simpa using h
  have hB : 2 * W.b₄ - 4 * (x0 * x1 + x0 * x2 + x1 * x2) = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff 1) hq0
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h
    simpa using h
  have hD : W.b₆ + 4 * (x0 * x1 * x2) = 0 := by
    have h := congrArg (fun q : K[X] => q.coeff 0) hq0
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_zero] at h
    simpa using h
  have hb2 : W.b₂ = -4 * (x0 + x1 + x2) := by linear_combination hA
  have hb4 : W.b₄ = 2 * (x0 * x1 + x0 * x2 + x1 * x2) := by
    apply mul_left_cancel₀ h2; linear_combination hB
  have hb6 : W.b₆ = -4 * (x0 * x1 * x2) := by linear_combination hD
  have h4 : (4 : K) ≠ 0 := by rw [show (4 : K) = 2 ^ 2 by norm_num]; exact pow_ne_zero _ h2
  have hb8 : W.b₈ = 4 * (x0 + x1 + x2) * (x0 * x1 * x2) - (x0 * x1 + x0 * x2 + x1 * x2) ^ 2 := by
    apply mul_left_cancel₀ h4
    rw [b_relation, hb2, hb4, hb6]; ring

  have hc4 : W.c₄ = 16 * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2 - x0 * x1 - x0 * x2 - x1 * x2) := by
    rw [c₄, hb2, hb4]; ring
  have hΔ' : W.Δ = 16 * (x0 - x1) ^ 2 * (x0 - x2) ^ 2 * (x1 - x2) ^ 2 := by
    rw [WeierstrassCurve.Δ, hb2, hb4, hb6, hb8]; ring
  have hgx : ∀ i, veluGx W (P i).1 (P i).2
      = (6 * (P i).1 ^ 2 + W.b₂ * (P i).1 + W.b₄) / 2 := by
    intro i
    have hT := veluT_eq W (P i).1 (P i).2
    rw [veluT, hPgy i, mul_zero, sub_zero] at hT
    rw [eq_div_iff h2, mul_comm, hT]
  have hg0 : veluGx W x0 y0 = (x0 - x1) * (x0 - x2) := by
    rw [hx0, hy0, hgx, ← hx0, hb2, hb4, div_eq_iff h2]; ring
  have hg1 : veluGx W x1 y1 = (x1 - x0) * (x1 - x2) := by
    rw [hx1, hy1, hgx, ← hx1, hb2, hb4, div_eq_iff h2]; ring
  have hg2 : veluGx W x2 y2 = (x2 - x0) * (x2 - x1) := by
    rw [hx2, hy2, hgx, ← hx2, hb2, hb4, div_eq_iff h2]; ring
  have hd0 : velu2QuadDisc W x0 = 16 * (x1 - x2) ^ 2 := by rw [velu2QuadDisc_def, hb2, hb4]; ring
  have hd1 : velu2QuadDisc W x1 = 16 * (x0 - x2) ^ 2 := by rw [velu2QuadDisc_def, hb2, hb4]; ring
  have hd2 : velu2QuadDisc W x2 = 16 * (x0 - x1) ^ 2 := by rw [velu2QuadDisc_def, hb2, hb4]; ring
  have hj : W.j = W.c₄ ^ 3 / W.Δ := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ', inv_mul_eq_div]

  have hJ0 : @WeierstrassCurve.j K _ (veluQuotient2 W x0 y0) ⟨isUnit_iff_ne_zero.mpr (hΔ (e.symm 0))⟩
      = (W.c₄ + 240 * veluGx W x0 y0) ^ 3 / (veluGx W x0 y0 * velu2QuadDisc W x0 ^ 2) :=
    veluQuotient2_j (hPeq (e.symm 0)) (hPgy (e.symm 0))
  have hJ1 : @WeierstrassCurve.j K _ (veluQuotient2 W x1 y1) ⟨isUnit_iff_ne_zero.mpr (hΔ (e.symm 1))⟩
      = (W.c₄ + 240 * veluGx W x1 y1) ^ 3 / (veluGx W x1 y1 * velu2QuadDisc W x1 ^ 2) :=
    veluQuotient2_j (hPeq (e.symm 1)) (hPgy (e.symm 1))
  have hJ2 : @WeierstrassCurve.j K _ (veluQuotient2 W x2 y2) ⟨isUnit_iff_ne_zero.mpr (hΔ (e.symm 2))⟩
      = (W.c₄ + 240 * veluGx W x2 y2) ^ 3 / (veluGx W x2 y2 * velu2QuadDisc W x2 ^ 2) :=
    veluQuotient2_j (hPeq (e.symm 2)) (hPgy (e.symm 2))
  rw [hJ0, hJ1, hJ2, fibrePoly_phiTwo_eq, hj, cubic_expand,
    coeff_two_identity h01 h02 h12 h2 hc4 hΔ' hg0 hg1 hg2 hd0 hd1 hd2,
    coeff_one_identity h01 h02 h12 h2 hc4 hΔ' hg0 hg1 hg2 hd0 hd1 hd2,
    coeff_zero_identity h01 h02 h12 h2 hc4 hΔ' hg0 hg1 hg2 hd0 hd1 hd2]


end
end Dubon2026.SourcePrimeTwoPolynomial
