import Dubon2026.SourceEllipticCharTwoStabilizerCoordinates

/-! DUB-17/18 -> characteristic-two modular genus comparison -> actual
exceptional stabilizer. Adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_isGalois_ord_jqModC_dvd_twelve_of_char_two.
The existing Mathlib.ofJ0 is the literal source curve. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve Polynomial
noncomputable section
variable {K : Type*} [Field K] [CharP K 2] [IsAlgClosed K]

omit [CharP K 2] in
lemma natCard_eq_natDegree {p : K[X]} (hsep : p.Separable) (S : Set K)
    (hS : ∀ x, x ∈ S ↔ Polynomial.aeval x p = 0) : Nat.card S = p.natDegree := by
  have hp : p ≠ 0 := hsep.ne_zero
  have hS' : S = p.rootSet K := by
    ext x
    rw [hS, Polynomial.mem_rootSet]
    exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
  rw [hS', Nat.card_eq_fintype_card]
  exact Polynomial.card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _)

lemma natCard_cube_eq_one : Nat.card {x : K // x ^ 3 = 1} = 3 := by
  have h3 : ((3 : ℕ) : K) ≠ 0 := by
    rw [Nat.cast_ofNat, three_eq_one K]; exact one_ne_zero
  have hsep : (Polynomial.X ^ 3 - Polynomial.C (1 : K)).Separable := Polynomial.separable_X_pow_sub_C 1 h3 one_ne_zero
  have := natCard_eq_natDegree hsep {x : K | x ^ 3 = 1} (fun x => by
    simp only [Set.mem_setOf_eq, map_sub, map_pow, Polynomial.aeval_X,
      map_one]
    exact sub_eq_zero.symm)
  rw [Polynomial.natDegree_X_pow_sub_C] at this
  exact this

lemma natCard_units_cube_eq_one : Nat.card {u : Kˣ // (u : K) ^ 3 = 1} = 3 := by
  have e : {u : Kˣ // (u : K) ^ 3 = 1} ≃ {x : K // x ^ 3 = 1} :=
    { toFun := fun u => ⟨u.1, u.2⟩
      invFun := fun x => ⟨Units.mk0 x.1 (by
          intro h; have := x.2; rw [h] at this; norm_num at this), x.2⟩
      left_inv := fun u => Subtype.ext (Units.ext rfl)
      right_inv := fun x => rfl }
  rw [Nat.card_congr e, natCard_cube_eq_one]

lemma natCard_pow_four_eq_self : Nat.card {s : K // s ^ 4 = s} = 4 := by
  have h2 := two_eq_zero K
  have hsep : (Polynomial.X ^ 4 - Polynomial.X : K[X]).Separable := by
    rw [Polynomial.separable_def']
    refine ⟨0, -1, ?_⟩
    have hd : Polynomial.derivative (Polynomial.X ^ 4 - Polynomial.X : K[X]) = -1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X]
      have : (Polynomial.C ((4 : ℕ) : K) : K[X]) = 0 := by
        rw [show ((4 : ℕ) : K) = 2 * 2 by norm_num, h2, mul_zero, map_zero]
      rw [this, zero_mul, zero_sub]
    rw [hd]; ring
  have := natCard_eq_natDegree hsep {s : K | s ^ 4 = s} (fun x => by
    simp only [Set.mem_setOf_eq, map_sub, map_pow, Polynomial.aeval_X]
    exact sub_eq_zero.symm)
  rw [show (Polynomial.X ^ 4 - Polynomial.X : K[X]).natDegree = 4 by compute_degree!] at this
  exact this

lemma natCard_artinSchreier (c : K) : Nat.card {t : K // t ^ 2 + t = c} = 2 := by
  have h2 := two_eq_zero K
  have hsep : (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : K[X]).Separable := by
    rw [Polynomial.separable_def']
    refine ⟨0, 1, ?_⟩
    have hd : Polynomial.derivative (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : K[X]) = 1 := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_add, Polynomial.derivative_X_pow,
        Polynomial.derivative_X, Polynomial.derivative_C]
      have : (Polynomial.C ((2 : ℕ) : K) : K[X]) = 0 := by
        rw [Nat.cast_ofNat, h2, map_zero]
      rw [this, zero_mul, zero_add, sub_zero]
    rw [hd]; ring
  have := natCard_eq_natDegree hsep {t : K | t ^ 2 + t = c} (fun x => by
    simp only [Set.mem_setOf_eq, map_sub, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_eq_zero.symm)
  rw [show (Polynomial.X ^ 2 + Polynomial.X - Polynomial.C c : K[X]).natDegree = 2 by compute_degree!] at this
  exact this

end
end Dubon2026.SourceEllipticCharTwo
