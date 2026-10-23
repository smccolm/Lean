/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.FieldDivision

set_option linter.style.header false

/-!
# Vélu's `x`-coordinate map and a product formula for translated sums

Let `W` be a Weierstrass curve over a field `F` of characteristic `≠ 2` and `H ⊆ W(F)` a finite
subgroup of odd order. For a point `P` write `x(P)` for its `x`-coordinate (`0` at infinity,
`Heights.Velu.xOf`). Vélu's isogeny `W → W/H` is given on `x`-coordinates by
`P ↦ ∑_{Q ∈ H} x(P + Q) − ∑_{Q ∈ H ∖ 0} x(Q)`, and this function of `P` depends on `x(P)`
only, through the **pair identity** (`Heights.Velu.xOf_add_add_xOf_sub`)

`x(P + Q) + x(P − Q) = 2x(Q) + t_Q/(x(P) − x(Q)) + u_Q/(x(P) − x(Q))²`,

`t_Q = 6x(Q)² + b₂x(Q) + b₄`, `u_Q = 4x(Q)³ + b₂x(Q)² + 2b₄x(Q) + b₆`, valid whenever
`x(P) ≠ x(Q)`. Clearing the denominators `∏_{Q ∈ H∖0} (X − x(Q))` gives a monic polynomial of
degree `|H|` whose roots are the `x(R + Q)`, `Q ∈ H`, for any `R ∉ H` with `2R ∉ H`; these are
`|H|` distinct roots. Evaluating at `x(P)` yields the **product formula**
(`Heights.Velu.prod_mul_sum_sub_sum`)

`∏_{Q ∈ H∖0} (x(P) − x(Q)) · (∑_{Q ∈ H} x(P + Q) − ∑_{Q ∈ H} x(R + Q))
    = ∏_{Q ∈ H} (x(P) − x(R + Q))`

for `P, R ∉ H` with `2R ∉ H`. This is the algebraic input of the isogeny estimate for a cyclic
subgroup: the left side is additive in torsion coordinates (so it is bounded crudely), the right
side is multiplicative (so its valuations can be computed factor by factor).

No isogeny, quotient curve or invariant differential is constructed here: the statements are
identities between coordinates of points of `W`.
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Heights.Velu

variable {F : Type*} [Field F] {W : Affine F}

/-- The `x`-coordinate of a point of an affine Weierstrass curve, `0` at the point at
infinity. -/
def xOf : W.Point → F
  | .zero => 0
  | .some x _ _ => x

@[simp] lemma xOf_zero : xOf (0 : W.Point) = 0 := rfl

@[simp] lemma xOf_some {x y : F} (h : W.Nonsingular x y) : xOf (.some x y h) = x := rfl

@[simp] lemma xOf_neg (P : W.Point) : xOf (-P) = xOf P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [Point.neg_some]; rfl

/-- Vélu's quantity `t = 6x² + b₂x + b₄`. -/
def veluT (W : Affine F) (x : F) : F := 6 * x ^ 2 + W.b₂ * x + W.b₄

/-- Vélu's quantity `u = 4x³ + b₂x² + 2b₄x + b₆ = (2y + a₁x + a₃)²`. -/
def veluU (W : Affine F) (x : F) : F := 4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆

variable [DecidableEq F]

/-- **The pair identity**: for affine points `P = (x₁, y₁)`, `Q = (x₂, y₂)` with `x₁ ≠ x₂`,
`x(P + Q) + x(P − Q) = 2x₂ + t/(x₁ − x₂) + u/(x₁ − x₂)²`. -/
theorem xOf_add_add_xOf_sub {x₁ y₁ x₂ y₂ : F} (h₁ : W.Nonsingular x₁ y₁)
    (h₂ : W.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    xOf (Point.some x₁ y₁ h₁ + Point.some x₂ y₂ h₂) +
        xOf (Point.some x₁ y₁ h₁ - Point.some x₂ y₂ h₂) =
      2 * x₂ + veluT W x₂ / (x₁ - x₂) + veluU W x₂ / (x₁ - x₂) ^ 2 := by
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have e₁ := (equation_iff x₁ y₁).mp h₁.1
  have e₂ := (equation_iff x₂ y₂).mp h₂.1
  rw [sub_eq_add_neg, Point.neg_some, Point.add_of_X_ne hx, Point.add_of_X_ne hx]
  simp only [xOf_some, addX, slope_of_X_ne hx, negY, veluT, veluU, b₂, b₄, b₆]
  field_simp
  linear_combination 2 * e₁ + 2 * e₂


/-! ### Sums over a finite subgroup -/

section Subgroup

variable (H : AddSubgroup W.Point) [Fintype H]

/-- The nonzero elements of `H`. -/
noncomputable def nonzero : Finset H := Finset.univ.filter (fun Q => Q ≠ 0)

lemma mem_nonzero {Q : H} : Q ∈ nonzero H ↔ Q ≠ 0 := by
  simp [nonzero]

omit [Fintype H] in
/-- A point outside `H` has `x`-coordinate different from those of the nonzero points of `H`. -/
lemma xOf_ne_of_notMem {P : W.Point} (hP : P ∉ H) {Q : W.Point} (hQ : Q ∈ H) (hQ0 : Q ≠ 0) :
    xOf P ≠ xOf Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · exact absurd H.zero_mem hP
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · exact absurd rfl hQ0
  intro hx
  rcases (Point.X_eq_iff (h₁ := h₁) (h₂ := h₂)).mp hx with h | h
  · exact hP (h ▸ hQ)
  · exact hP (h ▸ H.neg_mem hQ)

/-- Reindexing a sum over `H` by a translation in `H`. -/
lemma sum_add_left (f : W.Point → F) (Q₀ : H) :
    ∑ Q : H, f ((Q₀ : W.Point) + Q) = ∑ Q : H, f Q := by
  refine Fintype.sum_equiv (Equiv.addLeft Q₀) _ _ fun Q => ?_
  simp

/-- `∑_{Q ∈ H} f(P + Q) = f(P) + ∑_{Q ∈ H ∖ 0} f(P + Q)`. -/
lemma sum_eq_add_sum_nonzero (f : W.Point → F) :
    ∑ Q : H, f Q = f 0 + ∑ Q ∈ nonzero H, f Q := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : H))]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext Q
  simp [nonzero, Finset.mem_erase, and_comm]

/-- Negation permutes the nonzero elements of `H`. -/
lemma sum_nonzero_neg (f : W.Point → F) :
    ∑ Q ∈ nonzero H, f (-(Q : W.Point)) = ∑ Q ∈ nonzero H, f Q := by
  refine Finset.sum_nbij' (fun Q => -Q) (fun Q => -Q) ?_ ?_ ?_ ?_ ?_
  · intro Q hQ; rw [mem_nonzero] at hQ ⊢; exact neg_ne_zero.mpr hQ
  · intro Q hQ; rw [mem_nonzero] at hQ ⊢; exact neg_ne_zero.mpr hQ
  · intro Q _; simp
  · intro Q _; simp
  · intro Q _; simp

/-- **Vélu's `x`-map as a function of `x(P)`**: for `P ∉ H`,
`x(P) + ½ ∑_{Q ∈ H∖0} (t_Q/(x(P) − x(Q)) + u_Q/(x(P) − x(Q))²)
  = ∑_{Q ∈ H} x(P + Q) − ∑_{Q ∈ H∖0} x(Q)`. -/
theorem xOf_add_half_sum (h2 : (2 : F) ≠ 0) {P : W.Point} (hP : P ∉ H) :
    xOf P + (1 / 2) * ∑ Q ∈ nonzero H,
        (veluT W (xOf (Q : W.Point)) / (xOf P - xOf (Q : W.Point)) +
          veluU W (xOf (Q : W.Point)) / (xOf P - xOf (Q : W.Point)) ^ 2) =
      ∑ Q : H, xOf (P + (Q : W.Point)) - ∑ Q ∈ nonzero H, xOf (Q : W.Point) := by
  have hpair : ∀ Q ∈ nonzero H,
      veluT W (xOf (Q : W.Point)) / (xOf P - xOf (Q : W.Point)) +
          veluU W (xOf (Q : W.Point)) / (xOf P - xOf (Q : W.Point)) ^ 2 =
        xOf (P + (Q : W.Point)) + xOf (P + -(Q : W.Point)) - 2 * xOf (Q : W.Point) := by
    intro Q hQ
    rw [mem_nonzero] at hQ
    have hQ0 : (Q : W.Point) ≠ 0 := fun h => hQ (Subtype.ext h)
    have hne := xOf_ne_of_notMem H hP Q.2 hQ0
    obtain ⟨Q, hQH⟩ := Q
    rcases P with _ | ⟨x₁, y₁, h₁⟩
    · exact absurd H.zero_mem hP
    rcases Q with _ | ⟨x₂, y₂, h₂⟩
    · exact absurd rfl hQ0
    have := xOf_add_add_xOf_sub h₁ h₂ hne
    rw [sub_eq_add_neg] at this
    simp only [xOf_some] at this ⊢
    linear_combination -this
  rw [Finset.sum_congr rfl hpair, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_nonzero_neg H (fun Q => xOf (P + Q)), sum_eq_add_sum_nonzero H (fun Q => xOf (P + Q)),
    ← Finset.mul_sum, add_zero]
  field_simp
  ring

/-! ### The polynomial of Vélu's `x`-map -/

/-- `∏_{Q ∈ H∖0} (X − x(Q))`. -/
noncomputable def denom : F[X] := ∏ Q ∈ nonzero H, (X - C (xOf (Q : W.Point)))

/-- `∏_{Q' ∈ H∖0, Q' ≠ ±Q} (X − x(Q'))`. -/
noncomputable def denomExcept (Q : H) : F[X] :=
  ∏ Q' ∈ (nonzero H).filter (fun Q' => ¬ (Q' = Q ∨ Q' = -Q)), (X - C (xOf (Q' : W.Point)))

/-- **The numerator of Vélu's `x`-map** shifted by `c`:
`(X − c)·∏_{H∖0}(X − x(Q)) + ½ ∑_{Q ∈ H∖0} (t_Q (X − x(Q)) + u_Q) ∏_{Q' ≠ ±Q} (X − x(Q'))`. -/
noncomputable def numer (c : F) : F[X] :=
  (X - C c) * denom H + C (1 / 2) * ∑ Q ∈ nonzero H,
    (C (veluT W (xOf (Q : W.Point))) * (X - C (xOf (Q : W.Point))) +
      C (veluU W (xOf (Q : W.Point)))) * denomExcept H Q

lemma monic_denom : (denom H).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

lemma monic_denomExcept (Q : H) : (denomExcept H Q).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- `∏_{H∖0} (X − x(Q')) = (X − x(Q))² ∏_{Q' ≠ ±Q} (X − x(Q'))` for `Q ∈ H∖0` with `−Q ≠ Q`. -/
lemma denom_eq {Q : H} (hQ : Q ∈ nonzero H) (hQQ : -Q ≠ Q) :
    denom H = (X - C (xOf (Q : W.Point))) ^ 2 * denomExcept H Q := by
  classical
  unfold denom denomExcept
  rw [← Finset.prod_filter_not_mul_prod_filter (nonzero H) (fun Q' => ¬ (Q' = Q ∨ Q' = -Q))]
  have hpair : (nonzero H).filter (fun Q' => ¬¬ (Q' = Q ∨ Q' = -Q)) = {Q, -Q} := by
    ext Q'
    simp only [Finset.mem_filter, not_not, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · rintro (rfl | rfl)
      · exact ⟨hQ, Or.inl rfl⟩
      · refine ⟨?_, Or.inr rfl⟩
        rw [mem_nonzero] at hQ ⊢
        exact neg_ne_zero.mpr hQ
  rw [hpair, Finset.prod_pair (Ne.symm hQQ), AddSubgroup.coe_neg, xOf_neg, sq, mul_comm]

lemma natDegree_denom : (denom H).natDegree = (nonzero H).card := by
  unfold denom
  rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
  simp

/-- Evaluation of the numerator away from the `x(Q)`, `Q ∈ H∖0`. -/
lemma eval_numer (c z : F) (hH : ∀ Q : H, Q ≠ 0 → -Q ≠ Q)
    (hz : ∀ Q ∈ nonzero H, z ≠ xOf (Q : W.Point)) :
    (numer H c).eval z = (denom H).eval z * (z - c + (1 / 2) * ∑ Q ∈ nonzero H,
      (veluT W (xOf (Q : W.Point)) / (z - xOf (Q : W.Point)) +
        veluU W (xOf (Q : W.Point)) / (z - xOf (Q : W.Point)) ^ 2)) := by
  have hE : ∀ Q ∈ nonzero H, (denomExcept H Q).eval z =
      (denom H).eval z / (z - xOf (Q : W.Point)) ^ 2 := by
    intro Q hQ
    have hQ0 : Q ≠ 0 := (mem_nonzero H).mp hQ
    have hne : z - xOf (Q : W.Point) ≠ 0 := sub_ne_zero.mpr (hz Q hQ)
    rw [denom_eq H hQ (hH Q hQ0), eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    field_simp
  unfold numer
  rw [eval_add, eval_mul, eval_mul, eval_finsetSum, eval_sub, eval_X, eval_C, eval_C,
    mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun Q hQ => ?_
    have hne : z - xOf (Q : W.Point) ≠ 0 := sub_ne_zero.mpr (hz Q hQ)
    rw [eval_mul, hE Q hQ, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_C, eval_C]
    field_simp

lemma natDegree_denomExcept {Q : H} (hQ : Q ∈ nonzero H) (hQQ : -Q ≠ Q) :
    (denomExcept H Q).natDegree + 2 = (nonzero H).card := by
  have h := congrArg natDegree (denom_eq H hQ hQQ)
  rw [natDegree_denom, (monic_X_sub_C _).pow 2 |>.natDegree_mul (monic_denomExcept H Q),
    natDegree_pow, natDegree_X_sub_C] at h
  omega

/-- The numerator is monic of degree `|H|`. -/
lemma monic_numer (c : F) (hH : ∀ Q : H, Q ≠ 0 → -Q ≠ Q) :
    (numer H c).Monic ∧ (numer H c).natDegree = Fintype.card H := by
  classical
  have hcard : (nonzero H).card + 1 = Fintype.card H := by
    have h : nonzero H = Finset.univ.erase 0 := by
      ext Q; simp [nonzero]
    rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 0 < Fintype.card H := Fintype.card_pos
    omega
  have hmain : ((X - C c) * denom H).Monic := (monic_X_sub_C c).mul (monic_denom H)
  have hdeg : ((X - C c) * denom H).natDegree = (nonzero H).card + 1 := by
    rw [(monic_X_sub_C c).natDegree_mul (monic_denom H), natDegree_X_sub_C, natDegree_denom,
      add_comm]
  have hsmall : (C (1 / 2 : F) * ∑ Q ∈ nonzero H,
      (C (veluT W (xOf (Q : W.Point))) * (X - C (xOf (Q : W.Point))) +
        C (veluU W (xOf (Q : W.Point)))) * denomExcept H Q).natDegree <
      (nonzero H).card + 1 := by
    refine lt_of_le_of_lt (natDegree_C_mul_le _ _) (Nat.lt_succ_of_le ?_)
    refine natDegree_sum_le_of_forall_le _ _ fun Q hQ => ?_
    have h2 := natDegree_denomExcept H hQ (hH Q ((mem_nonzero H).mp hQ))
    refine (natDegree_mul_le).trans ?_
    have hlin : (C (veluT W (xOf (Q : W.Point))) * (X - C (xOf (Q : W.Point))) +
        C (veluU W (xOf (Q : W.Point)))).natDegree ≤ 1 := by
      refine (natDegree_add_le _ _).trans (max_le ?_ (by simp))
      refine (natDegree_C_mul_le _ _).trans ?_
      simp
    omega
  refine ⟨hmain.add_of_left ?_, ?_⟩
  · refine degree_lt_degree ?_
    rw [hdeg]; exact hsmall
  · unfold numer
    rw [natDegree_add_eq_left_of_natDegree_lt (by rw [hdeg]; exact hsmall), hdeg, hcard]

omit [Fintype H] [DecidableEq F] in
/-- Nonzero points with equal `x`-coordinates are equal up to sign. -/
lemma eq_or_eq_neg_of_xOf_eq {P₁ P₂ : W.Point} (h₁ : P₁ ≠ 0) (h₂ : P₂ ≠ 0)
    (hx : xOf P₁ = xOf P₂) : P₁ = P₂ ∨ P₁ = -P₂ := by
  rcases P₁ with _ | ⟨x₁, y₁, h₁'⟩
  · exact absurd rfl h₁
  rcases P₂ with _ | ⟨x₂, y₂, h₂'⟩
  · exact absurd rfl h₂
  exact (Point.X_eq_iff (h₁ := h₁') (h₂ := h₂')).mp hx

/-- **The product formula for Vélu's `x`-map.** Let `H` be a finite subgroup without points of
order `2`, and `P, R ∉ H` with `2R ∉ H`. Then
`∏_{Q ∈ H∖0} (x(P) − x(Q)) · (∑_{Q ∈ H} x(P + Q) − ∑_{Q ∈ H} x(R + Q))
    = ∏_{Q ∈ H} (x(P) − x(R + Q))`. -/
theorem prod_mul_sum_sub_sum (h2 : (2 : F) ≠ 0) (hH : ∀ Q : H, Q ≠ 0 → -Q ≠ Q)
    {P R : W.Point} (hP : P ∉ H) (hR : R ∉ H) (hRR : R + R ∉ H) :
    (∏ Q ∈ nonzero H, (xOf P - xOf (Q : W.Point))) *
        (∑ Q : H, xOf (P + (Q : W.Point)) - ∑ Q : H, xOf (R + (Q : W.Point))) =
      ∏ Q : H, (xOf P - xOf (R + (Q : W.Point))) := by
  classical
  set c : F := ∑ Q : H, xOf (R + (Q : W.Point)) - ∑ Q ∈ nonzero H, xOf (Q : W.Point) with hc
  have key : ∀ P' : W.Point, P' ∉ H → (numer H c).eval (xOf P') =
      (∏ Q ∈ nonzero H, (xOf P' - xOf (Q : W.Point))) *
        (∑ Q : H, xOf (P' + (Q : W.Point)) - ∑ Q : H, xOf (R + (Q : W.Point))) := by
    intro P' hP'
    rw [eval_numer H c _ hH fun Q hQ => xOf_ne_of_notMem H hP' Q.2
      fun h => (mem_nonzero H).mp hQ (Subtype.ext h)]
    have h := xOf_add_half_sum H h2 hP'
    unfold denom
    rw [eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    congr 1
    rw [hc]
    linear_combination h
  have hroot : ∀ Q₀ : H, (numer H c).IsRoot (xOf (R + (Q₀ : W.Point))) := by
    intro Q₀
    have hRQ : R + (Q₀ : W.Point) ∉ H := fun h =>
      hR (by simpa using H.sub_mem h Q₀.2)
    rw [IsRoot, key _ hRQ]
    have : ∑ Q : H, xOf (R + (Q₀ : W.Point) + (Q : W.Point)) =
        ∑ Q : H, xOf (R + (Q : W.Point)) := by
      simp_rw [add_assoc]
      exact sum_add_left H (fun S => xOf (R + S)) Q₀
    rw [this, sub_self, mul_zero]
  have hne0 : ∀ Q₀ : H, R + (Q₀ : W.Point) ≠ 0 := fun Q₀ h =>
    hR (by simp [eq_neg_iff_add_eq_zero.mpr h, Q₀.2])
  have hinj : Function.Injective (fun Q₀ : H => xOf (R + (Q₀ : W.Point))) := by
    intro Q₀ Q₁ hx
    rcases eq_or_eq_neg_of_xOf_eq (hne0 Q₀) (hne0 Q₁) hx with h | h
    · exact Subtype.ext (add_left_cancel h)
    · exfalso
      apply hRR
      have : R + R = -((Q₁ : W.Point) + Q₀) := by
        rw [neg_add] at h ⊢
        rw [show R + R = (R + (Q₀ : W.Point)) + (R - (Q₀ : W.Point)) by abel, h]
        abel
      rw [this]
      exact H.neg_mem (H.add_mem Q₁.2 Q₀.2)
  have hdvd : ∏ Q₀ : H, (X - C (xOf (R + (Q₀ : W.Point)))) ∣ numer H c :=
    Fintype.prod_dvd_of_coprime (pairwise_coprime_X_sub_C hinj)
      fun Q₀ => dvd_iff_isRoot.mpr (hroot Q₀)
  have hmon : (∏ Q₀ : H, (X - C (xOf (R + (Q₀ : W.Point))))).Monic :=
    monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hdeg : (∏ Q₀ : H, (X - C (xOf (R + (Q₀ : W.Point))))).natDegree = Fintype.card H := by
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp
  have heq := eq_of_monic_of_dvd_of_natDegree_le hmon (monic_numer H c hH).1 hdvd
    (by rw [hdeg, (monic_numer H c hH).2])
  rw [← key P hP, heq, eval_prod]
  simp

end Subgroup

end Heights.Velu
