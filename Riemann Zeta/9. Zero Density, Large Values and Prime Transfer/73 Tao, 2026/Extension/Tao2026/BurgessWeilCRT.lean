import Tao2026.BurgessMoment

/-!
# Chinese-remainder factorization for Burgess complete correlations

This file isolates the exact multiplicative step in the remaining composite
Weil estimate.  A character modulo a coprime product is restricted canonically
to both CRT coordinates, the tuple polynomials commute with those coordinates,
and the complete correlation factors as the product of its two local sums.
-/

namespace Tao2026


open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

noncomputable def burgessCRTLeftCharacter
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n)) : DirichletCharacter ℂ m where
  toFun x := χ ((ZMod.chineseRemainder h).symm (x, 1))
  map_one' := by
    rw [← χ.map_one]
    congr 1
    apply (ZMod.chineseRemainder h).injective
    simp
  map_mul' x y := by
    rw [show (ZMod.chineseRemainder h).symm (x * y, 1) =
        (ZMod.chineseRemainder h).symm (x, 1) *
          (ZMod.chineseRemainder h).symm (y, 1) by
      apply (ZMod.chineseRemainder h).injective
      simp]
    exact χ.map_mul _ _
  map_nonunit' x hx := by
    apply χ.map_nonunit
    intro hu
    have hpair := hu.map (ZMod.chineseRemainder h).toMonoidHom
    have hxy : IsUnit (x, (1 : ZMod n)) := by simpa using hpair
    have hxUnit : IsUnit x := (Prod.isUnit_iff.mp hxy).1
    exact hx hxUnit

noncomputable def burgessCRTRightCharacter
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n)) : DirichletCharacter ℂ n where
  toFun y := χ ((ZMod.chineseRemainder h).symm (1, y))
  map_one' := by
    rw [← χ.map_one]
    congr 1
    apply (ZMod.chineseRemainder h).injective
    simp
  map_mul' x y := by
    rw [show (ZMod.chineseRemainder h).symm (1, x * y) =
        (ZMod.chineseRemainder h).symm (1, x) *
          (ZMod.chineseRemainder h).symm (1, y) by
      apply (ZMod.chineseRemainder h).injective
      simp]
    exact χ.map_mul _ _
  map_nonunit' y hy := by
    apply χ.map_nonunit
    intro hu
    have hpair := hu.map (ZMod.chineseRemainder h).toMonoidHom
    have hxy : IsUnit ((1 : ZMod m), y) := by simpa using hpair
    have hyUnit : IsUnit y := (Prod.isUnit_iff.mp hxy).2
    exact hy hyUnit

theorem burgessCRT_character_factorization
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n)) (z : ZMod (m * n)) :
    χ z =
      burgessCRTLeftCharacter m n h χ (ZMod.chineseRemainder h z).1 *
        burgessCRTRightCharacter m n h χ (ZMod.chineseRemainder h z).2 := by
  change χ z =
    χ ((ZMod.chineseRemainder h).symm
      ((ZMod.chineseRemainder h z).1, 1)) *
    χ ((ZMod.chineseRemainder h).symm
      (1, (ZMod.chineseRemainder h z).2))
  have hz : z =
      (ZMod.chineseRemainder h).symm
          ((ZMod.chineseRemainder h z).1, 1) *
        (ZMod.chineseRemainder h).symm
          (1, (ZMod.chineseRemainder h z).2) := by
    apply (ZMod.chineseRemainder h).injective
    simp
  calc
    χ z = χ
        ((ZMod.chineseRemainder h).symm
            ((ZMod.chineseRemainder h z).1, 1) *
          (ZMod.chineseRemainder h).symm
            (1, (ZMod.chineseRemainder h z).2)) := congrArg χ hz
    _ = χ ((ZMod.chineseRemainder h).symm
            ((ZMod.chineseRemainder h z).1, 1)) *
          χ ((ZMod.chineseRemainder h).symm
            (1, (ZMod.chineseRemainder h z).2)) := χ.map_mul _ _

theorem burgessCRT_tupleNumerator_fst
    (m n B r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h (burgessTupleNumerator uv x)).1 =
      burgessTupleNumerator uv (ZMod.chineseRemainder h x).1 := by
  unfold burgessTupleNumerator
  rw [map_prod, Prod.fst_prod]
  simp [map_add, ZMod.chineseRemainder]

theorem burgessCRT_tupleNumerator_snd
    (m n B r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h (burgessTupleNumerator uv x)).2 =
      burgessTupleNumerator uv (ZMod.chineseRemainder h x).2 := by
  unfold burgessTupleNumerator
  rw [map_prod, Prod.snd_prod]
  simp [map_add, ZMod.chineseRemainder]

theorem burgessCRT_tupleDenominator_fst
    (m n B r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h (burgessTupleDenominator uv x)).1 =
      burgessTupleDenominator uv (ZMod.chineseRemainder h x).1 := by
  unfold burgessTupleDenominator
  rw [map_prod, Prod.fst_prod]
  simp [map_add, ZMod.chineseRemainder]

theorem burgessCRT_tupleDenominator_snd
    (m n B r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h (burgessTupleDenominator uv x)).2 =
      burgessTupleDenominator uv (ZMod.chineseRemainder h x).2 := by
  unfold burgessTupleDenominator
  rw [map_prod, Prod.snd_prod]
  simp [map_add, ZMod.chineseRemainder]

theorem burgessCRTLeftCharacter_inv
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n)) :
    burgessCRTLeftCharacter m n h χ⁻¹ =
      (burgessCRTLeftCharacter m n h χ)⁻¹ := by
  ext u
  rw [MulChar.inv_apply_eq_inv']
  change χ⁻¹ ((ZMod.chineseRemainder h).symm (u, 1)) =
    (χ ((ZMod.chineseRemainder h).symm (u, 1)))⁻¹
  exact MulChar.inv_apply_eq_inv' χ _

theorem burgessCRTRightCharacter_inv
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n)) :
    burgessCRTRightCharacter m n h χ⁻¹ =
      (burgessCRTRightCharacter m n h χ)⁻¹ := by
  ext u
  rw [MulChar.inv_apply_eq_inv']
  change χ⁻¹ ((ZMod.chineseRemainder h).symm (1, u)) =
    (χ ((ZMod.chineseRemainder h).symm (1, u)))⁻¹
  exact MulChar.inv_apply_eq_inv' χ _

theorem burgessCompleteCorrelation_mul_coprime
    (m n B r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n))
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    burgessCompleteCorrelation χ uv =
      burgessCompleteCorrelation (burgessCRTLeftCharacter m n h χ) uv *
        burgessCompleteCorrelation (burgessCRTRightCharacter m n h χ) uv := by
  let χm := burgessCRTLeftCharacter m n h χ
  let χn := burgessCRTRightCharacter m n h χ
  let F : ZMod (m * n) → ℂ := fun x =>
    χ (burgessTupleNumerator uv x) * χ⁻¹ (burgessTupleDenominator uv x)
  let Fm : ZMod m → ℂ := fun x =>
    χm (burgessTupleNumerator uv x) * χm⁻¹ (burgessTupleDenominator uv x)
  let Fn : ZMod n → ℂ := fun x =>
    χn (burgessTupleNumerator uv x) * χn⁻¹ (burgessTupleDenominator uv x)
  change (∑ x, F x) = (∑ x, Fm x) * ∑ x, Fn x
  calc
    (∑ x, F x) = ∑ p : ZMod m × ZMod n, Fm p.1 * Fn p.2 := by
      apply Fintype.sum_equiv (ZMod.chineseRemainder h).toEquiv
      intro x
      dsimp only [F, Fm, Fn, χm, χn]
      rw [burgessCRT_character_factorization m n h χ,
        burgessCRT_character_factorization m n h χ⁻¹,
        burgessCRT_tupleNumerator_fst m n B r h,
        burgessCRT_tupleNumerator_snd m n B r h,
        burgessCRT_tupleDenominator_fst m n B r h,
        burgessCRT_tupleDenominator_snd m n B r h,
        burgessCRTLeftCharacter_inv m n h χ,
        burgessCRTRightCharacter_inv m n h χ]
      have he : (ZMod.chineseRemainder h).toEquiv x =
          ZMod.chineseRemainder h x := rfl
      rw [he]
      ring
    _ = ∑ x : ZMod m, ∑ y : ZMod n, Fm x * Fn y := by
      rw [Fintype.sum_prod_type]
    _ = (∑ x, Fm x) * ∑ y, Fn y := (Fintype.sum_mul_sum Fm Fn).symm

theorem norm_burgessCompleteCorrelation_mul_coprime
    (m n B r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n))
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    ‖burgessCompleteCorrelation χ uv‖ =
      ‖burgessCompleteCorrelation (burgessCRTLeftCharacter m n h χ) uv‖ *
        ‖burgessCompleteCorrelation (burgessCRTRightCharacter m n h χ) uv‖ := by
  rw [burgessCompleteCorrelation_mul_coprime m n B r h χ uv, norm_mul]

/-- The global character is the product of the two canonical CRT characters
after both are changed back to the product level. -/
theorem burgessCRT_global_eq_local_changeLevel_mul
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n)) :
    χ = DirichletCharacter.changeLevel (m.dvd_mul_right n)
          (burgessCRTLeftCharacter m n h χ) *
        DirichletCharacter.changeLevel (n.dvd_mul_left m)
          (burgessCRTRightCharacter m n h χ) := by
  ext x
  change χ (x : ZMod (m * n)) =
    DirichletCharacter.changeLevel (m.dvd_mul_right n)
        (burgessCRTLeftCharacter m n h χ) (x : ZMod (m * n)) *
      DirichletCharacter.changeLevel (n.dvd_mul_left m)
        (burgessCRTRightCharacter m n h χ) (x : ZMod (m * n))
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd,
    DirichletCharacter.changeLevel_eq_cast_of_dvd]
  rw [burgessCRT_character_factorization m n h χ x]
  congr 2
  · change ((ZMod.chineseRemainder h) (x : ZMod (m * n))).1 =
      (ZMod.cast (x : ZMod (m * n)) : ZMod m)
    simp [ZMod.chineseRemainder]
  · change ((ZMod.chineseRemainder h) (x : ZMod (m * n))).2 =
      (ZMod.cast (x : ZMod (m * n)) : ZMod n)
    simp [ZMod.chineseRemainder]

/-- If the left CRT character factors through `d`, the global character
factors through `d * n`. -/
theorem burgessCRT_factorsThrough_mul_right
    (m n d : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n))
    (hd : DirichletCharacter.FactorsThrough
      (burgessCRTLeftCharacter m n h χ) d) :
    DirichletCharacter.FactorsThrough χ (d * n) := by
  let θ : DirichletCharacter ℂ (d * n) :=
    DirichletCharacter.changeLevel (d.dvd_mul_right n) hd.χ₀ *
      DirichletCharacter.changeLevel (n.dvd_mul_left d)
        (burgessCRTRightCharacter m n h χ)
  refine ⟨Nat.mul_dvd_mul_right hd.dvd n, θ, ?_⟩
  have hleft :
      DirichletCharacter.changeLevel (m.dvd_mul_right n)
          (burgessCRTLeftCharacter m n h χ) =
        DirichletCharacter.changeLevel
          (Nat.dvd_trans hd.dvd (m.dvd_mul_right n)) hd.χ₀ := by
    calc
      _ = DirichletCharacter.changeLevel (m.dvd_mul_right n)
          (DirichletCharacter.changeLevel hd.dvd hd.χ₀) := by rw [← hd.eq_changeLevel]
      _ = _ := (DirichletCharacter.changeLevel_trans hd.χ₀ hd.dvd
        (m.dvd_mul_right n)).symm
  calc
    χ = DirichletCharacter.changeLevel (m.dvd_mul_right n)
          (burgessCRTLeftCharacter m n h χ) *
        DirichletCharacter.changeLevel (n.dvd_mul_left m)
          (burgessCRTRightCharacter m n h χ) :=
      burgessCRT_global_eq_local_changeLevel_mul m n h χ
    _ = DirichletCharacter.changeLevel
          (Nat.dvd_trans hd.dvd (m.dvd_mul_right n)) hd.χ₀ *
        DirichletCharacter.changeLevel (n.dvd_mul_left m)
          (burgessCRTRightCharacter m n h χ) := congrArg₂ (· * ·) hleft rfl
    _ = DirichletCharacter.changeLevel
        (Nat.mul_dvd_mul_right hd.dvd n) θ := by
      dsimp only [θ]
      rw [map_mul]
      rw [← DirichletCharacter.changeLevel_trans,
        ← DirichletCharacter.changeLevel_trans]

/-- Primitivity of a character modulo a coprime product descends to its left
canonical CRT character. -/
theorem burgessCRTLeftCharacter_isPrimitive
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n))
    (hχ : DirichletCharacter.IsPrimitive χ) :
    DirichletCharacter.IsPrimitive (burgessCRTLeftCharacter m n h χ) := by
  rw [DirichletCharacter.isPrimitive_def]
  apply Nat.dvd_antisymm
  · exact DirichletCharacter.conductor_dvd_level _
  · have hfactor := burgessCRT_factorsThrough_mul_right m n
      (DirichletCharacter.conductor (burgessCRTLeftCharacter m n h χ)) h χ
      (DirichletCharacter.factorsThrough_conductor _)
    have hc := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hfactor
    rw [(DirichletCharacter.isPrimitive_def χ).mp hχ] at hc
    exact (Nat.mul_dvd_mul_iff_right
      (Nat.pos_of_ne_zero (NeZero.ne n))).mp hc

/-- If the right CRT character factors through `d`, the global character
factors through `m * d`. -/
theorem burgessCRT_factorsThrough_mul_left
    (m n d : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n))
    (hd : DirichletCharacter.FactorsThrough
      (burgessCRTRightCharacter m n h χ) d) :
    DirichletCharacter.FactorsThrough χ (m * d) := by
  let θ : DirichletCharacter ℂ (m * d) :=
    DirichletCharacter.changeLevel (m.dvd_mul_right d)
        (burgessCRTLeftCharacter m n h χ) *
      DirichletCharacter.changeLevel (d.dvd_mul_left m) hd.χ₀
  refine ⟨Nat.mul_dvd_mul_left m hd.dvd, θ, ?_⟩
  have hright :
      DirichletCharacter.changeLevel (n.dvd_mul_left m)
          (burgessCRTRightCharacter m n h χ) =
        DirichletCharacter.changeLevel
          (Nat.dvd_trans hd.dvd (n.dvd_mul_left m)) hd.χ₀ := by
    calc
      _ = DirichletCharacter.changeLevel (n.dvd_mul_left m)
          (DirichletCharacter.changeLevel hd.dvd hd.χ₀) := by rw [← hd.eq_changeLevel]
      _ = _ := (DirichletCharacter.changeLevel_trans hd.χ₀ hd.dvd
        (n.dvd_mul_left m)).symm
  calc
    χ = DirichletCharacter.changeLevel (m.dvd_mul_right n)
          (burgessCRTLeftCharacter m n h χ) *
        DirichletCharacter.changeLevel (n.dvd_mul_left m)
          (burgessCRTRightCharacter m n h χ) :=
      burgessCRT_global_eq_local_changeLevel_mul m n h χ
    _ = DirichletCharacter.changeLevel (m.dvd_mul_right n)
          (burgessCRTLeftCharacter m n h χ) *
        DirichletCharacter.changeLevel
          (Nat.dvd_trans hd.dvd (n.dvd_mul_left m)) hd.χ₀ :=
      congrArg₂ (· * ·) rfl hright
    _ = DirichletCharacter.changeLevel
        (Nat.mul_dvd_mul_left m hd.dvd) θ := by
      dsimp only [θ]
      rw [map_mul]
      rw [← DirichletCharacter.changeLevel_trans,
        ← DirichletCharacter.changeLevel_trans]

/-- Primitivity of a character modulo a coprime product descends to its right
canonical CRT character. -/
theorem burgessCRTRightCharacter_isPrimitive
    (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n))
    (hχ : DirichletCharacter.IsPrimitive χ) :
    DirichletCharacter.IsPrimitive (burgessCRTRightCharacter m n h χ) := by
  rw [DirichletCharacter.isPrimitive_def]
  apply Nat.dvd_antisymm
  · exact DirichletCharacter.conductor_dvd_level _
  · have hfactor := burgessCRT_factorsThrough_mul_left m n
      (DirichletCharacter.conductor (burgessCRTRightCharacter m n h χ)) h χ
      (DirichletCharacter.factorsThrough_conductor _)
    have hc := DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hfactor
    rw [(DirichletCharacter.isPrimitive_def χ).mp hχ] at hc
    exact (Nat.mul_dvd_mul_iff_left
      (Nat.pos_of_ne_zero (NeZero.ne m))).mp hc

/-- The elementary Weil factor is multiplicative across coprime moduli. -/
theorem burgessCompositeWeilFactor_mul_coprime
    (m n r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    burgessCompositeWeilFactor (m * n) r =
      burgessCompositeWeilFactor m r * burgessCompositeWeilFactor n r := by
  unfold burgessCompositeWeilFactor
  rw [h.primeFactors_mul, Finset.card_union_of_disjoint h.disjoint_primeFactors,
    pow_add, Nat.cast_mul, Nat.cast_mul, Real.sqrt_mul (by positivity)]
  ring

/-- A fixed nonzero-coefficient gcd contribution is multiplicative across
coprime moduli. -/
theorem burgessCoefficientGcdContribution_mul_coprime
    (m n B r : ℕ) (h : m.Coprime n)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r) :
    burgessCoefficientGcdContribution (m * n) uv j =
      burgessCoefficientGcdContribution m uv j *
        burgessCoefficientGcdContribution n uv j := by
  unfold burgessCoefficientGcdContribution
  split_ifs
  · exact h.gcd_mul _
  · simp

/-- Each single zero-extended coefficient contribution is bounded by the
relaxed sum over all nonzero coefficients. -/
theorem burgessCoefficientGcdContribution_le_tupleGcdWeight
    (q B r : ℕ) (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r) :
    burgessCoefficientGcdContribution q uv j ≤
      burgessTupleGcdWeight q uv := by
  rw [burgessTupleGcdWeight_eq_sum_contributions]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

/-- Bounds at two coprime local factors using the same coefficient witness
multiply to the fixed-coefficient bound at their product. -/
theorem norm_burgessCompleteCorrelation_le_coefficient_of_coprime
    (m n B r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hm : ‖burgessCompleteCorrelation
        (burgessCRTLeftCharacter m n h χ) uv‖ ≤
      burgessCompositeWeilFactor m r *
        burgessCoefficientGcdContribution m uv j)
    (hn : ‖burgessCompleteCorrelation
        (burgessCRTRightCharacter m n h χ) uv‖ ≤
      burgessCompositeWeilFactor n r *
        burgessCoefficientGcdContribution n uv j) :
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor (m * n) r *
        burgessCoefficientGcdContribution (m * n) uv j := by
  rw [norm_burgessCompleteCorrelation_mul_coprime m n B r h χ uv]
  calc
    ‖burgessCompleteCorrelation (burgessCRTLeftCharacter m n h χ) uv‖ *
        ‖burgessCompleteCorrelation (burgessCRTRightCharacter m n h χ) uv‖ ≤
      (burgessCompositeWeilFactor m r *
          burgessCoefficientGcdContribution m uv j) *
        (burgessCompositeWeilFactor n r *
          burgessCoefficientGcdContribution n uv j) := by
      exact mul_le_mul hm hn (norm_nonneg _) (by
        unfold burgessCompositeWeilFactor
        positivity)
    _ = burgessCompositeWeilFactor (m * n) r *
        burgessCoefficientGcdContribution (m * n) uv j := by
      rw [burgessCompositeWeilFactor_mul_coprime m n r h,
        burgessCoefficientGcdContribution_mul_coprime m n B r h uv j]
      push_cast
      ring

/-- A common coefficient witness at two coprime local factors gives the
relaxed composite bound at their product.  This is the exact CRT assembly
needed after the prime and prime-square local estimates: factors, square
roots, and the chosen gcd all multiply, and the final chosen contribution is
inserted into the source's relaxed gcd sum. -/
theorem norm_burgessCompleteCorrelation_le_compositeWeil_of_coprime
    (m n B r : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m * n))
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r)
    (hm : ‖burgessCompleteCorrelation
        (burgessCRTLeftCharacter m n h χ) uv‖ ≤
      burgessCompositeWeilFactor m r *
        burgessCoefficientGcdContribution m uv j)
    (hn : ‖burgessCompleteCorrelation
        (burgessCRTRightCharacter m n h χ) uv‖ ≤
      burgessCompositeWeilFactor n r *
        burgessCoefficientGcdContribution n uv j) :
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor (m * n) r *
        burgessTupleGcdWeight (m * n) uv := by
  have hcoefficient :
      (burgessCoefficientGcdContribution (m * n) uv j : ℝ) ≤
        burgessTupleGcdWeight (m * n) uv := by
    exact_mod_cast burgessCoefficientGcdContribution_le_tupleGcdWeight
      (m * n) B r uv j
  exact (norm_burgessCompleteCorrelation_le_coefficient_of_coprime
      m n B r h χ uv j hm hn).trans
    (mul_le_mul_of_nonneg_left hcoefficient (by
      unfold burgessCompositeWeilFactor
      positivity))

end

end Tao2026
