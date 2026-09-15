import Tao2026.ExceptionalCharacterBurgess
import Tao2026.VinogradovMeanValue
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite moment expansion for the cubefree Burgess estimate

This file begins the proof of the remaining primitive analytic Burgess input.
It records the exact finite `2r`-moment identity underlying the Burgess method:
after expanding the shifted character sums, the moment is a sum over ordered
pairs of `r`-tuples of shifts and complete residue classes modulo `q`.
-/

namespace Tao2026

open Finset Complex
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The length-`B` shifted character sum at the residue class `x`. -/
def burgessShiftSum {q : ℕ} (B : ℕ) (χ : DirichletCharacter ℂ q)
    (x : ZMod q) : ℂ :=
  ∑ b : Fin B, χ (x + ((b.1 + 1 : ℕ) : ZMod q))

/-- The complete character correlation attached to an ordered pair of
`r`-tuples of shifts. -/
def burgessTupleCharacter {q B r : ℕ}
    (χ : DirichletCharacter ℂ q)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (x : ZMod q) : ℂ :=
  (∏ i, χ (x + ((((uv.1 i).1 + 1 : ℕ)) : ZMod q))) *
    star (∏ i, χ (x + ((((uv.2 i).1 + 1 : ℕ)) : ZMod q)))

/-- Product of the numerator shifts associated to a Burgess tuple. -/
def burgessTupleNumerator {q B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (x : ZMod q) : ZMod q :=
  Finset.univ.prod
    (fun i : Fin r => x + ((((uv.1 i).1 + 1 : ℕ)) : ZMod q))

/-- Product of the denominator shifts associated to a Burgess tuple. -/
def burgessTupleDenominator {q B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (x : ZMod q) : ZMod q :=
  Finset.univ.prod
    (fun i : Fin r => x + ((((uv.2 i).1 + 1 : ℕ)) : ZMod q))

/-- Flatten an ordered pair of `r`-tuples to a function on two tagged copies
of `Fin r`. -/
def burgessTupleFlatten {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    Fin r ⊕ Fin r → Fin B :=
  Sum.elim uv.1 uv.2

/-- Flattening loses no information. -/
theorem burgessTupleFlatten_injective {B r : ℕ} :
    Function.Injective
      (burgessTupleFlatten (B := B) (r := r)) := by
  intro uv vw h
  apply Prod.ext
  · funext i
    exact congrFun h (Sum.inl i)
  · funext i
    exact congrFun h (Sum.inr i)

/-- The distinct shifts occurring in both halves of an ordered Burgess
tuple. -/
def burgessTupleShiftSet {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) : Finset (Fin B) :=
  Finset.univ.image uv.1 ∪ Finset.univ.image uv.2

/-- The diagonal (or degenerate) tuples are those using at most `r` distinct
shifts among their `2r` entries. -/
def BurgessTupleDegenerate {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) : Prop :=
  Fintype.card (Set.range (burgessTupleFlatten uv)) ≤ r

/-- The finite set of degenerate ordered tuple pairs. -/
noncomputable def burgessDegenerateTuples (B r : ℕ) :
    Finset ((Fin r → Fin B) × (Fin r → Fin B)) := by
  classical
  exact Finset.univ.filter BurgessTupleDegenerate

/-- The complementary finite set of tuple pairs with at least `r+1`
distinct shifts. -/
noncomputable def burgessNondegenerateTuples (B r : ℕ) :
    Finset ((Fin r → Fin B) × (Fin r → Fin B)) := by
  classical
  exact Finset.univ.filter (fun uv => ¬BurgessTupleDegenerate uv)

/-- The cardinality of the range subtype agrees with the finite image of all
tagged tuple positions. -/
theorem card_range_burgessTupleFlatten_eq_card_image {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    Fintype.card (Set.range (burgessTupleFlatten uv)) =
      (Finset.univ.image (burgessTupleFlatten uv)).card := by
  classical
  rw [← Set.toFinset_card, Set.toFinset_range]

/-- If more than `r` different values occur in `2r` positions, some value
occurs exactly once.  This is the combinatorial fact that makes one source
coefficient `A_j` nonzero. -/
theorem exists_unique_position_of_not_burgessTupleDegenerate
    {B r : ℕ} (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (hnd : ¬BurgessTupleDegenerate uv) :
    ∃ j : Fin r ⊕ Fin r, ∀ i,
      burgessTupleFlatten uv i = burgessTupleFlatten uv j → i = j := by
  classical
  let f := burgessTupleFlatten uv
  let t : Finset (Fin B) := Finset.univ.image f
  by_contra hunique
  have hrepeat : ∀ j : Fin r ⊕ Fin r,
      ∃ i, f i = f j ∧ i ≠ j := by
    intro j
    by_contra hj
    apply hunique
    refine ⟨j, ?_⟩
    intro i hi
    by_contra hij
    exact hj ⟨i, hi, hij⟩
  have hfiber : ∀ y ∈ t,
      2 ≤ (Finset.univ.filter (fun i : Fin r ⊕ Fin r => f i = y)).card := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    rcases hrepeat j with ⟨i, hfi, hij⟩
    apply Nat.succ_le_iff.mpr
    apply Finset.one_lt_card.mpr
    refine ⟨j, by simp, i, ?_, hij.symm⟩
    simp [hfi]
  have hdouble : t.card * 2 ≤
      (Finset.univ : Finset (Fin r ⊕ Fin r)).card := by
    calc
      t.card * 2 = ∑ _y ∈ t, 2 := by simp
      _ ≤ ∑ y ∈ t,
          (Finset.univ.filter (fun i : Fin r ⊕ Fin r => f i = y)).card := by
        exact Finset.sum_le_sum hfiber
      _ = (Finset.univ : Finset (Fin r ⊕ Fin r)).card := by
        symm
        exact Finset.card_eq_sum_card_image f Finset.univ
  have ht : t.card ≤ r := by
    have hdouble' : t.card * 2 ≤ r + r := by
      simpa only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] using
        hdouble
    omega
  apply hnd
  unfold BurgessTupleDegenerate
  rw [card_range_burgessTupleFlatten_eq_card_image]
  exact ht

/-- The source shift `b_i`, viewed as an integer in `{1, …, B}`. -/
def burgessTupleShiftInt {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (i : Fin r ⊕ Fin r) : ℤ :=
  ((burgessTupleFlatten uv i).1 + 1 : ℕ)

/-- Equality of the integer shifts is exactly equality of the underlying
`Fin B` values. -/
theorem burgessTupleShiftInt_eq_iff {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (i j : Fin r ⊕ Fin r) :
    burgessTupleShiftInt uv i = burgessTupleShiftInt uv j ↔
      burgessTupleFlatten uv i = burgessTupleFlatten uv j := by
  constructor
  · intro h
    apply Fin.ext
    unfold burgessTupleShiftInt at h
    norm_cast at h
    omega
  · intro h
    unfold burgessTupleShiftInt
    rw [h]

/-- The literal coefficient
`A_j = ∏_{i ≠ j} (b_i - b_j)` from the pinned composite Burgess source. -/
def burgessTupleDifferenceProduct {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r) : ℤ :=
  ∏ i ∈ (Finset.univ.erase j),
    (burgessTupleShiftInt uv i - burgessTupleShiftInt uv j)

/-- A position has nonzero `A_j` exactly when its shift occurs only once. -/
theorem burgessTupleDifferenceProduct_ne_zero_iff {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (j : Fin r ⊕ Fin r) :
    burgessTupleDifferenceProduct uv j ≠ 0 ↔
      ∀ i, burgessTupleFlatten uv i = burgessTupleFlatten uv j → i = j := by
  classical
  constructor
  · intro hprod i hi
    by_contra hij
    apply hprod
    unfold burgessTupleDifferenceProduct
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)
    rw [sub_eq_zero]
    exact (burgessTupleShiftInt_eq_iff uv i j).2 hi
  · intro hunique
    unfold burgessTupleDifferenceProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [sub_ne_zero]
    intro hshift
    have hvalue := (burgessTupleShiftInt_eq_iff uv i j).1 hshift
    exact (Finset.ne_of_mem_erase hi) (hunique i hvalue)

/-- Every nondegenerate tuple has one nonzero source coefficient `A_j`. -/
theorem exists_burgessTupleDifferenceProduct_ne_zero_of_not_degenerate
    {B r : ℕ} (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (hnd : ¬BurgessTupleDegenerate uv) :
    ∃ j : Fin r ⊕ Fin r, burgessTupleDifferenceProduct uv j ≠ 0 := by
  rcases exists_unique_position_of_not_burgessTupleDegenerate uv hnd with
    ⟨j, hj⟩
  exact ⟨j, (burgessTupleDifferenceProduct_ne_zero_iff uv j).2 hj⟩

/-- Finset-membership form used by the forthcoming nondegenerate complete-sum
estimate. -/
theorem exists_burgessTupleDifferenceProduct_ne_zero_of_mem_nondegenerate
    {B r : ℕ} (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (huv : uv ∈ burgessNondegenerateTuples B r) :
    ∃ j : Fin r ⊕ Fin r, burgessTupleDifferenceProduct uv j ≠ 0 := by
  classical
  apply exists_burgessTupleDifferenceProduct_ne_zero_of_not_degenerate uv
  simpa [burgessNondegenerateTuples] using huv

/-- Positions at which the source coefficient `A_j` is nonzero. -/
noncomputable def burgessNonzeroDifferencePositions {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    Finset (Fin r ⊕ Fin r) := by
  classical
  exact Finset.univ.filter (fun j => burgessTupleDifferenceProduct uv j ≠ 0)

/-- The relaxed source gcd weight
`∑_{j : A_j ≠ 0} gcd(|A_j|,q)` for one ordered tuple. -/
noncomputable def burgessTupleGcdWeight (q : ℕ) {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) : ℕ :=
  ∑ j ∈ burgessNonzeroDifferencePositions uv,
    Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs q

/-- A nondegenerate tuple has a nonempty set of nonzero source
coefficients. -/
theorem burgessNonzeroDifferencePositions_nonempty_of_mem_nondegenerate
    {B r : ℕ} (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (huv : uv ∈ burgessNondegenerateTuples B r) :
    (burgessNonzeroDifferencePositions uv).Nonempty := by
  classical
  rcases exists_burgessTupleDifferenceProduct_ne_zero_of_mem_nondegenerate
    uv huv with ⟨j, hj⟩
  exact ⟨j, by simp [burgessNonzeroDifferencePositions, hj]⟩

/-- Trivial pointwise bound for the relaxed gcd weight. -/
theorem burgessTupleGcdWeight_le (q : ℕ) [NeZero q] {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    burgessTupleGcdWeight q uv ≤ 2 * r * q := by
  classical
  unfold burgessTupleGcdWeight
  calc
    (∑ j ∈ burgessNonzeroDifferencePositions uv,
        Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs q) ≤
        ∑ _j ∈ burgessNonzeroDifferencePositions uv, q := by
      apply Finset.sum_le_sum
      intro j hj
      exact Nat.gcd_le_right _ (NeZero.pos q)
    _ = (burgessNonzeroDifferencePositions uv).card * q := by simp
    _ ≤ (Finset.univ : Finset (Fin r ⊕ Fin r)).card * q := by
      apply Nat.mul_le_mul_right
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = 2 * r * q := by
      simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
      rw [show r + r = 2 * r by omega]

/-- The sum of `gcd(n,q)` over the initial positive interval. -/
def burgessInitialGcdSum (q H : ℕ) : ℕ :=
  ∑ n ∈ Finset.Ioc 0 H, Nat.gcd n q

/-- A gcd is bounded by the sum of those divisors of `q` which divide the
other argument.  This elementary majorization is convenient because its
interval sum can be counted exactly. -/
theorem gcd_le_sum_divisor_multiples (q n : ℕ) [NeZero q] :
    Nat.gcd n q ≤
      ∑ d ∈ q.divisors, if d ∣ n then d else 0 := by
  have hsingle := Finset.single_le_sum
    (s := q.divisors) (f := fun d => if d ∣ n then d else 0)
    (fun d hd => by omega)
    (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n q, NeZero.ne q⟩)
  simpa [Nat.gcd_dvd_left] using hsingle

/-- Divisor-count estimate
`∑_{1 ≤ n ≤ H} gcd(n,q) ≤ H τ(q)`. -/
theorem burgessInitialGcdSum_le (q H : ℕ) [NeZero q] :
    burgessInitialGcdSum q H ≤ H * q.divisors.card := by
  unfold burgessInitialGcdSum
  calc
    (∑ n ∈ Finset.Ioc 0 H, Nat.gcd n q) ≤
        ∑ n ∈ Finset.Ioc 0 H,
          ∑ d ∈ q.divisors, if d ∣ n then d else 0 := by
      exact Finset.sum_le_sum (fun n hn => gcd_le_sum_divisor_multiples q n)
    _ = ∑ d ∈ q.divisors,
          ∑ n ∈ Finset.Ioc 0 H, if d ∣ n then d else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ q.divisors, (H / d) * d := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (∑ n ∈ Finset.Ioc 0 H, if d ∣ n then d else 0) =
            ∑ n ∈ (Finset.Ioc 0 H).filter (fun n => d ∣ n), d := by
          rw [Finset.sum_filter]
        _ = ((Finset.Ioc 0 H).filter (fun n => d ∣ n)).card * d := by
          simp
        _ = (H / d) * d := by
          rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ _d ∈ q.divisors, H := by
      apply Finset.sum_le_sum
      intro d hd
      exact Nat.div_mul_le_self H d
    _ = H * q.divisors.card := by
      simp [Nat.mul_comm]

/-- Integer absolute difference agrees with the natural-number distance. -/
theorem burgess_natAbs_int_sub_eq_dist (a b : ℕ) :
    Int.natAbs ((a : ℤ) - (b : ℤ)) = Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    have hnonneg : 0 ≤ (b : ℤ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
    apply Nat.cast_injective (R := ℤ)
    rw [Int.natCast_natAbs, abs_of_nonpos (by omega), Nat.cast_sub hab]
    omega
  · rw [Nat.dist_eq_sub_of_le_right hba]
    have hnonneg : 0 ≤ (a : ℤ) - b := sub_nonneg.mpr (by exact_mod_cast hba)
    apply Nat.cast_injective (R := ℤ)
    rw [Int.natCast_natAbs, abs_of_nonneg hnonneg, Nat.cast_sub hba]

/-- Gcd mass around a distinguished integer `a`, with the zero difference
removed. -/
def burgessCenteredNatGcdSum (q B a : ℕ) : ℕ :=
  ∑ b ∈ Finset.range B, if b = a then 0 else Nat.gcd (Nat.dist b a) q

/-- Both sides of a distinguished shift contribute at most one initial gcd
sum, giving a harmless factor `2`. -/
theorem burgessCenteredNatGcdSum_le (q B a : ℕ) [NeZero q] (ha : a < B) :
    burgessCenteredNatGcdSum q B a ≤ 2 * B * q.divisors.card := by
  classical
  let low := (Finset.range B).filter (fun b => b < a)
  let high := (Finset.range B).filter (fun b => a < b)
  have hlowInj : Set.InjOn (fun b : ℕ => a - b) low := by
    intro b hb c hc hbc
    have hb' : b < a := (Finset.mem_filter.mp hb).2
    have hc' : c < a := (Finset.mem_filter.mp hc).2
    change a - b = a - c at hbc
    omega
  have hhighInj : Set.InjOn (fun b : ℕ => b - a) high := by
    intro b hb c hc hbc
    have hb' : a < b := (Finset.mem_filter.mp hb).2
    have hc' : a < c := (Finset.mem_filter.mp hc).2
    change b - a = c - a at hbc
    omega
  have hlowSubset : low.image (fun b => a - b) ⊆ Finset.Ioc 0 B := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨b, hb, rfl⟩
    have hb' : b < a := (Finset.mem_filter.mp hb).2
    simp only [Finset.mem_Ioc]
    omega
  have hhighSubset : high.image (fun b => b - a) ⊆ Finset.Ioc 0 B := by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨b, hb, rfl⟩
    have hbData := Finset.mem_filter.mp hb
    have hbB : b < B := Finset.mem_range.mp hbData.1
    have hab : a < b := hbData.2
    simp only [Finset.mem_Ioc]
    omega
  have hlow : (∑ b ∈ low, Nat.gcd (Nat.dist b a) q) ≤
      burgessInitialGcdSum q B := by
    calc
      (∑ b ∈ low, Nat.gcd (Nat.dist b a) q) =
          ∑ b ∈ low, Nat.gcd (a - b) q := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt (Finset.mem_filter.mp hb).2)]
      _ = ∑ n ∈ low.image (fun b => a - b), Nat.gcd n q := by
        exact (Finset.sum_image (f := fun n => Nat.gcd n q) hlowInj).symm
      _ ≤ ∑ n ∈ Finset.Ioc 0 B, Nat.gcd n q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hlowSubset
          (fun n hn hnot => by omega)
      _ = burgessInitialGcdSum q B := rfl
  have hhigh : (∑ b ∈ high, Nat.gcd (Nat.dist b a) q) ≤
      burgessInitialGcdSum q B := by
    calc
      (∑ b ∈ high, Nat.gcd (Nat.dist b a) q) =
          ∑ b ∈ high, Nat.gcd (b - a) q := by
        apply Finset.sum_congr rfl
        intro b hb
        rw [Nat.dist_eq_sub_of_le_right
          (Nat.le_of_lt (Finset.mem_filter.mp hb).2)]
      _ = ∑ n ∈ high.image (fun b => b - a), Nat.gcd n q := by
        exact (Finset.sum_image (f := fun n => Nat.gcd n q) hhighInj).symm
      _ ≤ ∑ n ∈ Finset.Ioc 0 B, Nat.gcd n q := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hhighSubset
          (fun n hn hnot => by omega)
      _ = burgessInitialGcdSum q B := rfl
  have hsplit : burgessCenteredNatGcdSum q B a =
      (∑ b ∈ low, Nat.gcd (Nat.dist b a) q) +
        ∑ b ∈ high, Nat.gcd (Nat.dist b a) q := by
    unfold burgessCenteredNatGcdSum low high
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs <;> omega
  rw [hsplit]
  calc
    (∑ b ∈ low, Nat.gcd (Nat.dist b a) q) +
        ∑ b ∈ high, Nat.gcd (Nat.dist b a) q ≤
        burgessInitialGcdSum q B + burgessInitialGcdSum q B :=
      Nat.add_le_add hlow hhigh
    _ ≤ B * q.divisors.card + B * q.divisors.card :=
      Nat.add_le_add (burgessInitialGcdSum_le q B)
        (burgessInitialGcdSum_le q B)
    _ = 2 * B * q.divisors.card := by ring

/-- Gcd is submultiplicative in its first argument when the second argument
is nonzero. -/
theorem burgess_gcd_mul_le_mul_gcd (q a b : ℕ) [NeZero q] :
    Nat.gcd (a * b) q ≤ Nat.gcd a q * Nat.gcd b q := by
  apply Nat.le_of_dvd
  · exact Nat.mul_pos (Nat.gcd_pos_of_pos_right a (NeZero.pos q))
      (Nat.gcd_pos_of_pos_right b (NeZero.pos q))
  · simpa [Nat.gcd_comm] using (gcd_mul_dvd_mul_gcd q a b)

/-- Finite-product form of gcd submultiplicativity. -/
theorem burgess_gcd_prod_le_prod_gcd {ι : Type*} [DecidableEq ι]
    (q : ℕ) [NeZero q] (s : Finset ι) (f : ι → ℕ) :
    Nat.gcd (∏ i ∈ s, f i) q ≤ ∏ i ∈ s, Nat.gcd (f i) q := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact (burgess_gcd_mul_le_mul_gcd q (f i) (∏ x ∈ s, f x)).trans
        (Nat.mul_le_mul_left (Nat.gcd (f i) q) ih)

/-- The gcd of the literal coefficient `A_j` is bounded by the product of
the gcds of its `2r-1` differences. -/
theorem burgessTupleDifferenceProduct_gcd_le {q B r : ℕ} [NeZero q]
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (j : Fin r ⊕ Fin r) :
    Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs q ≤
      ∏ i ∈ Finset.univ.erase j,
        Nat.gcd (Nat.dist (burgessTupleFlatten uv i).1
          (burgessTupleFlatten uv j).1) q := by
  have hfactor : ∀ i : Fin r ⊕ Fin r,
      (burgessTupleShiftInt uv i - burgessTupleShiftInt uv j).natAbs =
        Nat.dist (burgessTupleFlatten uv i).1
          (burgessTupleFlatten uv j).1 := by
    intro i
    unfold burgessTupleShiftInt
    rw [show
      ((((burgessTupleFlatten uv i).1 + 1 : ℕ) : ℤ) -
          (((burgessTupleFlatten uv j).1 + 1 : ℕ) : ℤ)) =
        ((burgessTupleFlatten uv i).1 : ℤ) -
          (burgessTupleFlatten uv j).1 by norm_num]
    exact burgess_natAbs_int_sub_eq_dist _ _
  unfold burgessTupleDifferenceProduct
  have hnatabs :
      (∏ i ∈ Finset.univ.erase j,
          (burgessTupleShiftInt uv i - burgessTupleShiftInt uv j)).natAbs =
        ∏ i ∈ Finset.univ.erase j,
          (burgessTupleShiftInt uv i - burgessTupleShiftInt uv j).natAbs := by
    change Int.natAbsHom
        (∏ i ∈ Finset.univ.erase j,
          (burgessTupleShiftInt uv i - burgessTupleShiftInt uv j)) = _
    exact map_prod Int.natAbsHom _ _
  rw [hnatabs]
  simp_rw [hfactor]
  exact burgess_gcd_prod_le_prod_gcd q (Finset.univ.erase j)
    (fun i => Nat.dist (burgessTupleFlatten uv i).1
      (burgessTupleFlatten uv j).1)

/-- Independent finite coordinates factor a product sum as a power. -/
theorem burgess_sum_pi_prod_eq_pow {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] (h : β → ℕ) :
    (∑ g : ι → β, ∏ i, h (g i)) = (∑ b : β, h b) ^ Fintype.card ι := by
  classical
  let e := Fintype.equivFin ι
  let E : (ι → β) ≃ (Fin (Fintype.card ι) → β) :=
    Equiv.piCongrLeft (fun _ => β) e
  calc
    (∑ g : ι → β, ∏ i, h (g i)) =
        ∑ p : Fin (Fintype.card ι) → β, ∏ k, h (p k) := by
      apply Fintype.sum_equiv E
      intro g
      exact Fintype.prod_equiv e (fun i => h (g i))
        (fun k => h (E g k)) (fun i => by simp [E])
    _ = (∑ b : β, h b) ^ Fintype.card ι :=
      (Fintype.sum_pow h (Fintype.card ι)).symm

/-- Product majorant attached to one distinguished position, with a zero
factor whenever another coordinate repeats the distinguished shift. -/
def burgessPositionGcdMajorant (q : ℕ) {B r : ℕ} (j : Fin r ⊕ Fin r)
    (f : Fin r ⊕ Fin r → Fin B) : ℕ :=
  ∏ i ∈ Finset.univ.erase j,
    if f i = f j then 0 else Nat.gcd (Nat.dist (f i).1 (f j).1) q

/-- Centered gcd mass on the actual finite shift type. -/
def burgessFinCenteredGcdSum (q : ℕ) {B : ℕ} (a : Fin B) : ℕ :=
  ∑ b : Fin B, if b = a then 0 else Nat.gcd (Nat.dist b.1 a.1) q

theorem burgessFinCenteredGcdSum_eq (q : ℕ) {B : ℕ} (a : Fin B) :
    burgessFinCenteredGcdSum q a = burgessCenteredNatGcdSum q B a.1 := by
  unfold burgessFinCenteredGcdSum burgessCenteredNatGcdSum
  calc
    (∑ b : Fin B, if b = a then 0 else Nat.gcd (Nat.dist b.1 a.1) q) =
        ∑ b : Fin B, if b.1 = a.1 then 0
          else Nat.gcd (Nat.dist b.1 a.1) q := by
      apply Fintype.sum_congr
      intro b
      by_cases h : b = a
      · subst b
        simp
      · have hv : b.1 ≠ a.1 := fun hv => h (Fin.ext hv)
        simp [h, hv]
    _ = ∑ b ∈ Finset.range B, if b = a.1 then 0
          else Nat.gcd (Nat.dist b a.1) q := by
      exact Fin.sum_univ_eq_sum_range
        (fun b : ℕ => if b = a.1 then 0
          else Nat.gcd (Nat.dist b a.1) q) B

theorem burgessFinCenteredGcdSum_le (q : ℕ) [NeZero q] {B : ℕ} (a : Fin B) :
    burgessFinCenteredGcdSum q a ≤ 2 * B * q.divisors.card := by
  rw [burgessFinCenteredGcdSum_eq]
  exact burgessCenteredNatGcdSum_le q B a.1 a.2

/-- There are exactly `2r-1` tuple positions other than a fixed one. -/
theorem card_burgessPositions_ne {r : ℕ} (j : Fin r ⊕ Fin r) :
    Fintype.card {i : Fin r ⊕ Fin r // i ≠ j} = 2 * r - 1 := by
  rw [Fintype.card_subtype_compl (fun i : Fin r ⊕ Fin r => i = j)]
  simp
  omega

/-- Exact factorization of the sum of one-position product majorants. -/
theorem sum_burgessPositionGcdMajorant_eq (q B r : ℕ) (j : Fin r ⊕ Fin r) :
    (∑ f : Fin r ⊕ Fin r → Fin B, burgessPositionGcdMajorant q j f) =
      ∑ a : Fin B, (burgessFinCenteredGcdSum q a) ^ (2 * r - 1) := by
  classical
  let e := Equiv.piSplitAt j (fun _ : Fin r ⊕ Fin r => Fin B)
  let G := fun ag : Fin B × ({i : Fin r ⊕ Fin r // i ≠ j} → Fin B) =>
    ∏ i : {i : Fin r ⊕ Fin r // i ≠ j},
      if ag.2 i = ag.1 then 0
      else Nat.gcd (Nat.dist (ag.2 i).1 ag.1.1) q
  calc
    (∑ f : Fin r ⊕ Fin r → Fin B, burgessPositionGcdMajorant q j f) =
        ∑ ag : Fin B × ({i : Fin r ⊕ Fin r // i ≠ j} → Fin B), G ag := by
      apply Fintype.sum_equiv e
      intro f
      unfold burgessPositionGcdMajorant G
      rw [Finset.prod_subtype (p := fun i => i ≠ j) (Finset.univ.erase j)
        (fun i => by simp)]
      apply Fintype.prod_congr
      intro i
      simp [e, Equiv.piSplitAt]
    _ = ∑ a : Fin B,
        ∑ g : {i : Fin r ⊕ Fin r // i ≠ j} → Fin B,
          ∏ i, if g i = a then 0
            else Nat.gcd (Nat.dist (g i).1 a.1) q := by
      exact Fintype.sum_prod_type G
    _ = ∑ a : Fin B,
        (burgessFinCenteredGcdSum q a) ^
          Fintype.card {i : Fin r ⊕ Fin r // i ≠ j} := by
      apply Fintype.sum_congr
      intro a
      exact burgess_sum_pi_prod_eq_pow
        (fun b : Fin B => if b = a then 0
          else Nat.gcd (Nat.dist b.1 a.1) q)
    _ = ∑ a : Fin B,
        (burgessFinCenteredGcdSum q a) ^ (2 * r - 1) := by
      rw [card_burgessPositions_ne j]

/-- The total one-position majorant has the expected `B^(2r)` scale and
only a fixed power of the divisor count. -/
theorem sum_burgessPositionGcdMajorant_le (q B r : ℕ) [NeZero q]
    (j : Fin r ⊕ Fin r) :
    (∑ f : Fin r ⊕ Fin r → Fin B, burgessPositionGcdMajorant q j f) ≤
      B * (2 * B * q.divisors.card) ^ (2 * r - 1) := by
  rw [sum_burgessPositionGcdMajorant_eq]
  calc
    (∑ a : Fin B, (burgessFinCenteredGcdSum q a) ^ (2 * r - 1)) ≤
        ∑ _a : Fin B, (2 * B * q.divisors.card) ^ (2 * r - 1) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Nat.pow_le_pow_left (burgessFinCenteredGcdSum_le q a) _
    _ = B * (2 * B * q.divisors.card) ^ (2 * r - 1) := by
      simp

/-- Contribution of one coefficient, extended by zero when `A_j=0`. -/
def burgessCoefficientGcdContribution (q : ℕ) {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (j : Fin r ⊕ Fin r) : ℕ :=
  if burgessTupleDifferenceProduct uv j ≠ 0 then
    Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs q else 0

theorem burgessCoefficientGcdContribution_le_positionMajorant
    {q B r : ℕ} [NeZero q]
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) (j : Fin r ⊕ Fin r) :
    burgessCoefficientGcdContribution q uv j ≤
      burgessPositionGcdMajorant q j (burgessTupleFlatten uv) := by
  classical
  by_cases hA : burgessTupleDifferenceProduct uv j ≠ 0
  · rw [burgessCoefficientGcdContribution, if_pos hA]
    calc
      Nat.gcd (burgessTupleDifferenceProduct uv j).natAbs q ≤
          ∏ i ∈ Finset.univ.erase j,
            Nat.gcd (Nat.dist (burgessTupleFlatten uv i).1
              (burgessTupleFlatten uv j).1) q :=
        burgessTupleDifferenceProduct_gcd_le uv j
      _ = burgessPositionGcdMajorant q j (burgessTupleFlatten uv) := by
        unfold burgessPositionGcdMajorant
        apply Finset.prod_congr rfl
        intro i hi
        rw [if_neg]
        intro hvalue
        have hunique := (burgessTupleDifferenceProduct_ne_zero_iff uv j).1 hA
        exact Finset.ne_of_mem_erase hi (hunique i hvalue)
  · simp [burgessCoefficientGcdContribution, hA]

/-- The relaxed tuple weight is the sum of the zero-extended coefficient
contributions over all `2r` positions. -/
theorem burgessTupleGcdWeight_eq_sum_contributions (q : ℕ) {B r : ℕ}
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    burgessTupleGcdWeight q uv =
      ∑ j : Fin r ⊕ Fin r, burgessCoefficientGcdContribution q uv j := by
  classical
  unfold burgessTupleGcdWeight burgessNonzeroDifferencePositions
  rw [Finset.sum_filter]
  rfl

/-- Source gcd-weight summation bound.  Its divisor-count power depends only
on the fixed Burgess moment parameter and is therefore absorbable into an
arbitrarily small power of `q`. -/
theorem sum_burgessTupleGcdWeight_le (q B r : ℕ) [NeZero q] :
    (∑ uv ∈ burgessNondegenerateTuples B r,
        burgessTupleGcdWeight q uv) ≤
      2 * r * B * (2 * B * q.divisors.card) ^ (2 * r - 1) := by
  classical
  let eTuple :
      ((Fin r → Fin B) × (Fin r → Fin B)) ≃
        (Fin r ⊕ Fin r → Fin B) :=
    (Equiv.sumPiEquivProdPi (fun _ : Fin r ⊕ Fin r => Fin B)).symm
  calc
    (∑ uv ∈ burgessNondegenerateTuples B r,
        burgessTupleGcdWeight q uv) ≤
        ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
          burgessTupleGcdWeight q uv := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun uv huv hnot => by omega)
    _ = ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
        ∑ j : Fin r ⊕ Fin r, burgessCoefficientGcdContribution q uv j := by
      apply Fintype.sum_congr
      intro uv
      exact burgessTupleGcdWeight_eq_sum_contributions q uv
    _ ≤ ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
        ∑ j : Fin r ⊕ Fin r,
          burgessPositionGcdMajorant q j (burgessTupleFlatten uv) := by
      apply Finset.sum_le_sum
      intro uv huv
      apply Finset.sum_le_sum
      intro j hj
      exact burgessCoefficientGcdContribution_le_positionMajorant uv j
    _ = ∑ j : Fin r ⊕ Fin r,
        ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
          burgessPositionGcdMajorant q j (burgessTupleFlatten uv) := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin r ⊕ Fin r,
        ∑ f : Fin r ⊕ Fin r → Fin B,
          burgessPositionGcdMajorant q j f := by
      apply Fintype.sum_congr
      intro j
      apply Fintype.sum_equiv eTuple
      intro uv
      congr 1
    _ ≤ ∑ _j : Fin r ⊕ Fin r,
        B * (2 * B * q.divisors.card) ^ (2 * r - 1) := by
      apply Finset.sum_le_sum
      intro j hj
      exact sum_burgessPositionGcdMajorant_le q B r j
    _ = 2 * r * B * (2 * B * q.divisors.card) ^ (2 * r - 1) := by
      simp
      ring

/-- The elementary factor in Burgess's composite complete-sum estimate. -/
def burgessCompositeWeilFactor (q r : ℕ) : ℝ :=
  (((4 * r) ^ q.primeFactors.card : ℕ) : ℝ) * Real.sqrt q

/-- Embed the set of shifts actually used by a degenerate tuple into its
`r` available labels. -/
noncomputable def burgessDegenerateRangeEmbedding {B r : ℕ}
    (uv : {uv : (Fin r → Fin B) × (Fin r → Fin B) //
      BurgessTupleDegenerate uv}) :
    Set.range (burgessTupleFlatten uv.1) ↪ Fin r := by
  classical
  apply Classical.choice
  apply Function.Embedding.nonempty_of_card_le
  have h := uv.2
  change Fintype.card (Set.range (burgessTupleFlatten uv.1)) ≤ r at h
  simpa only [Fintype.card_fin] using h

/-- Code a nonempty-length degenerate tuple by `r` shift values and one of
`r` labels at each of its `2r` positions. -/
noncomputable def burgessDegenerateCode {B r : ℕ} (hr : 0 < r)
    (uv : {uv : (Fin r → Fin B) × (Fin r → Fin B) //
      BurgessTupleDegenerate uv}) :
    (Fin r → Fin B) × (Fin r ⊕ Fin r → Fin r) := by
  classical
  let f := burgessTupleFlatten uv.1
  let e := burgessDegenerateRangeEmbedding uv
  let fallback : Fin r → Fin B := fun _ => uv.1.1 ⟨0, hr⟩
  exact
    (Function.extend e Subtype.val fallback,
      fun i => e ⟨f i, ⟨i, rfl⟩⟩)

/-- Evaluation of a degenerate tuple is recovered by looking up the label in
its code. -/
theorem burgessDegenerateCode_reconstruct {B r : ℕ} (hr : 0 < r)
    (uv : {uv : (Fin r → Fin B) × (Fin r → Fin B) //
      BurgessTupleDegenerate uv}) (i : Fin r ⊕ Fin r) :
    (burgessDegenerateCode hr uv).1
        ((burgessDegenerateCode hr uv).2 i) =
      burgessTupleFlatten uv.1 i := by
  classical
  unfold burgessDegenerateCode
  dsimp only
  exact (burgessDegenerateRangeEmbedding uv).injective.extend_apply
    Subtype.val (fun _ => uv.1.1 ⟨0, hr⟩)
    ⟨burgessTupleFlatten uv.1 i, ⟨i, rfl⟩⟩

/-- The value/label code determines the original degenerate tuple. -/
theorem burgessDegenerateCode_injective {B r : ℕ} (hr : 0 < r) :
    Function.Injective (burgessDegenerateCode (B := B) hr) := by
  intro uv vw hcode
  apply Subtype.ext
  apply burgessTupleFlatten_injective
  funext i
  calc
    burgessTupleFlatten uv.1 i =
        (burgessDegenerateCode hr uv).1
          ((burgessDegenerateCode hr uv).2 i) :=
      (burgessDegenerateCode_reconstruct hr uv i).symm
    _ = (burgessDegenerateCode hr vw).1
          ((burgessDegenerateCode hr vw).2 i) := by rw [hcode]
    _ = burgessTupleFlatten vw.1 i :=
      burgessDegenerateCode_reconstruct hr vw i

/-- The subtype defined by the degeneracy predicate is the subtype carried
by the corresponding filtered finset. -/
noncomputable def burgessDegenerateSubtypeEquiv (B r : ℕ) :
    {uv : (Fin r → Fin B) × (Fin r → Fin B) //
      BurgessTupleDegenerate uv} ≃
      ↥(burgessDegenerateTuples B r) := by
  classical
  refine
    { toFun := fun uv => ⟨uv.1, ?_⟩
      invFun := fun uv => ⟨uv.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · simpa [burgessDegenerateTuples] using uv.2
  · have hmem := uv.2
    change uv.1 ∈ Finset.univ.filter BurgessTupleDegenerate at hmem
    exact (Finset.mem_filter.mp hmem).2
  · intro uv
    rfl
  · intro uv
    rfl

/-- Standard diagonal count: tuples using at most `r` different shifts are
encoded by `r` shift values and `2r` labels. -/
theorem card_burgessDegenerateTuples_le (B r : ℕ) :
    (burgessDegenerateTuples B r).card ≤ r ^ (2 * r) * B ^ r := by
  by_cases hr : r = 0
  · subst r
    simp [burgessDegenerateTuples, BurgessTupleDegenerate,
      burgessTupleFlatten]
  · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
    calc
      (burgessDegenerateTuples B r).card =
          Fintype.card {uv : (Fin r → Fin B) × (Fin r → Fin B) //
            BurgessTupleDegenerate uv} := by
        rw [Fintype.card_congr (burgessDegenerateSubtypeEquiv B r)]
        exact (Fintype.card_coe _).symm
      _ ≤ Fintype.card
          ((Fin r → Fin B) × (Fin r ⊕ Fin r → Fin r)) :=
        Fintype.card_le_of_injective (burgessDegenerateCode hrpos)
          (burgessDegenerateCode_injective hrpos)
      _ = r ^ (2 * r) * B ^ r := by
        simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_sum]
        rw [show r + r = 2 * r by omega, Nat.mul_comm]

/-- There are exactly `B^(2r)` ordered pairs of `r`-tuples of shifts. -/
theorem card_burgessTupleSpace (B r : ℕ) :
    Fintype.card ((Fin r → Fin B) × (Fin r → Fin B)) = B ^ (2 * r) := by
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  omega

/-- The expanded tuple term is exactly the quotient-character correlation
used by the complete-sum estimate.  This identity remains valid at nonunits:
both a character and its inverse vanish there. -/
theorem burgessTupleCharacter_eq_quotient_values {q B r : ℕ}
    (χ : DirichletCharacter ℂ q)
    (uv : (Fin r → Fin B) × (Fin r → Fin B))
    (x : ZMod q) :
    burgessTupleCharacter χ uv x =
      χ (burgessTupleNumerator uv x) *
        χ⁻¹ (burgessTupleDenominator uv x) := by
  unfold burgessTupleCharacter burgessTupleNumerator burgessTupleDenominator
  rw [map_prod χ _ Finset.univ, map_prod χ⁻¹ _ Finset.univ,
    star_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact (dirichletCharacter_inv_apply_eq_conj χ _).symm

/-- The complete quotient-character correlation belonging to a pair of
ordered shift tuples. -/
def burgessCompleteCorrelation {q B r : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) : ℂ :=
  ∑ x : ZMod q,
    χ (burgessTupleNumerator uv x) *
      χ⁻¹ (burgessTupleDenominator uv x)

/-- Literal proposition-valued interface for the remaining composite
Weil-type estimate.  It is the relaxed "in particular" form in the pinned
source, with the sum of `gcd(A_j,q)` over all nonzero coefficients. -/
def TaoPrimitiveCubefreeBurgessCompleteWeilBound : Prop :=
  ∀ (q B r : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)),
    2 ≤ r →
    TaoCubefree q →
    DirichletCharacter.IsPrimitive χ →
    uv ∈ burgessNondegenerateTuples B r →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor q r * burgessTupleGcdWeight q uv

/-- The exact complete-sum input used by Tao's chosen fourteenth moment.
Unlike the generic convenience predicate above, this proposition fixes
`r = 7` and therefore quantifies only over fourteen shifts. -/
def TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven : Prop :=
  ∀ (q B : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
    (uv : (Fin 7 → Fin B) × (Fin 7 → Fin B)),
    TaoCubefree q →
    DirichletCharacter.IsPrimitive χ →
    uv ∈ burgessNondegenerateTuples B 7 →
    ‖burgessCompleteCorrelation χ uv‖ ≤
      burgessCompositeWeilFactor q 7 * burgessTupleGcdWeight q uv

/-- The generic complete-sum predicate specializes to the only moment order
used in the final Burgess argument. -/
theorem TaoPrimitiveCubefreeBurgessCompleteWeilBound.toRSeven
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBound) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven := by
  intro q B _ χ uv hq hχ huv
  exact hweil q B 7 χ uv (by norm_num) hq hχ huv

/-- The unconditional complete-correlation bound obtained term by term. -/
theorem norm_burgessCompleteCorrelation_le_modulus
    {q B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (uv : (Fin r → Fin B) × (Fin r → Fin B)) :
    ‖burgessCompleteCorrelation χ uv‖ ≤ (q : ℝ) := by
  unfold burgessCompleteCorrelation
  calc
    ‖∑ x : ZMod q,
        χ (burgessTupleNumerator uv x) *
          χ⁻¹ (burgessTupleDenominator uv x)‖ ≤
        ∑ x : ZMod q,
          ‖χ (burgessTupleNumerator uv x) *
            χ⁻¹ (burgessTupleDenominator uv x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ZMod q, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul]
      exact mul_le_one₀ (DirichletCharacter.norm_le_one χ _)
        (norm_nonneg _) (DirichletCharacter.norm_le_one χ⁻¹ _)
    _ = (q : ℝ) := by simp [ZMod.card]

/-- Exact ordered-tuple expansion of the complete `2r`-moment of Burgess's
shifted character sums. -/
theorem burgess_shift_moment_expand {q B r : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (((∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ)) : ℂ) =
      ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
        ∑ x : ZMod q, burgessTupleCharacter χ uv x := by
  calc
    (((∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ)) : ℂ) =
        ∑ x : ZMod q,
          (((‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ)) : ℂ) := by
      norm_cast
    _ = ∑ x : ZMod q,
        ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
          burgessTupleCharacter χ uv x := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa only [burgessShiftSum, burgessTupleCharacter] using
        (complex_norm_sum_even_pow_eq_sum_pair
          (fun b : Fin B => χ (x + ((b.1 + 1 : ℕ) : ZMod q))) r)
    _ = ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
        ∑ x : ZMod q, burgessTupleCharacter χ uv x := by
      rw [Finset.sum_comm]

/-- Source-facing form of the moment expansion: every tuple contributes one
complete quotient-character correlation modulo `q`. -/
theorem burgess_shift_moment_expand_completeCorrelation
    {q B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (((∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ)) : ℂ) =
      ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
        burgessCompleteCorrelation χ uv := by
  rw [burgess_shift_moment_expand]
  apply Finset.sum_congr rfl
  intro uv huv
  unfold burgessCompleteCorrelation
  apply Finset.sum_congr rfl
  intro x hx
  exact burgessTupleCharacter_eq_quotient_values χ uv x

/-- Taking absolute values in the exact expansion leaves the analytic task as
the sum of the norms of the complete tuple correlations. -/
theorem burgess_shift_moment_le_sum_norm_completeCorrelation
    {q B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤
      ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
        ‖burgessCompleteCorrelation χ uv‖ := by
  let M : ℝ := ∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  calc
    M = ‖(M : ℂ)‖ := by simp [Complex.norm_real, abs_of_nonneg hM]
    _ = ‖∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
        burgessCompleteCorrelation χ uv‖ := by
      rw [burgess_shift_moment_expand_completeCorrelation]
    _ ≤ ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
        ‖burgessCompleteCorrelation χ uv‖ := norm_sum_le _ _

/-- Exact diagonal/off-diagonal reduction for the Burgess moment.  Degenerate
tuples use only the trivial modulus bound; the nondegenerate contribution is
controlled by the supplied complete-sum majorant `W`. -/
theorem burgess_shift_moment_le_degenerate_add_nondegenerate
    {q B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (W : ((Fin r → Fin B) × (Fin r → Fin B)) → ℝ)
    (hW : ∀ uv ∈ burgessNondegenerateTuples B r,
      ‖burgessCompleteCorrelation χ uv‖ ≤ W uv) :
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤
      ((burgessDegenerateTuples B r).card : ℝ) * q +
        ∑ uv ∈ burgessNondegenerateTuples B r, W uv := by
  classical
  calc
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤
        ∑ uv : (Fin r → Fin B) × (Fin r → Fin B),
          ‖burgessCompleteCorrelation χ uv‖ :=
      burgess_shift_moment_le_sum_norm_completeCorrelation χ
    _ = (∑ uv ∈ burgessDegenerateTuples B r,
          ‖burgessCompleteCorrelation χ uv‖) +
        ∑ uv ∈ burgessNondegenerateTuples B r,
          ‖burgessCompleteCorrelation χ uv‖ := by
      simp only [burgessDegenerateTuples, burgessNondegenerateTuples]
      rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ ((burgessDegenerateTuples B r).card : ℝ) * q +
        ∑ uv ∈ burgessNondegenerateTuples B r, W uv := by
      apply add_le_add
      · calc
          (∑ uv ∈ burgessDegenerateTuples B r,
              ‖burgessCompleteCorrelation χ uv‖) ≤
              ∑ _uv ∈ burgessDegenerateTuples B r, (q : ℝ) := by
            apply Finset.sum_le_sum
            intro uv huv
            exact norm_burgessCompleteCorrelation_le_modulus χ uv
          _ = ((burgessDegenerateTuples B r).card : ℝ) * q := by
            simp [nsmul_eq_mul]
      · exact Finset.sum_le_sum hW

/-- The pinned composite Weil interface reduces the complete moment to the
source gcd-weight sum, with the diagonal term already closed. -/
theorem burgess_shift_moment_le_of_completeWeil
    {q B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBound)
    (hr : 2 ≤ r) (hq : TaoCubefree q)
    (hχ : DirichletCharacter.IsPrimitive χ) :
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤
      ((r ^ (2 * r) * B ^ r : ℕ) : ℝ) * q +
        burgessCompositeWeilFactor q r *
          ∑ uv ∈ burgessNondegenerateTuples B r,
            (burgessTupleGcdWeight q uv : ℝ) := by
  classical
  have hsplit := burgess_shift_moment_le_degenerate_add_nondegenerate χ
    (fun uv => burgessCompositeWeilFactor q r * burgessTupleGcdWeight q uv)
    (fun uv huv => hweil q B r χ uv hr hq hχ huv)
  have hbadNat : (burgessDegenerateTuples B r).card ≤
      r ^ (2 * r) * B ^ r := card_burgessDegenerateTuples_le B r
  have hbad : ((burgessDegenerateTuples B r).card : ℝ) ≤
      ((r ^ (2 * r) * B ^ r : ℕ) : ℝ) := by
    exact_mod_cast hbadNat
  calc
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤
        ((burgessDegenerateTuples B r).card : ℝ) * q +
          ∑ uv ∈ burgessNondegenerateTuples B r,
            burgessCompositeWeilFactor q r *
              (burgessTupleGcdWeight q uv : ℝ) := hsplit
    _ = ((burgessDegenerateTuples B r).card : ℝ) * q +
        burgessCompositeWeilFactor q r *
          ∑ uv ∈ burgessNondegenerateTuples B r,
            (burgessTupleGcdWeight q uv : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ((r ^ (2 * r) * B ^ r : ℕ) : ℝ) * q +
        burgessCompositeWeilFactor q r *
          ∑ uv ∈ burgessNondegenerateTuples B r,
            (burgessTupleGcdWeight q uv : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hbad (Nat.cast_nonneg q)) le_rfl

/-- The proved gcd-weight summation closes the arithmetic side of the
composite-Weil moment reduction.  Only the proposition-valued complete Weil
estimate remains as input. -/
theorem burgess_shift_moment_le_of_completeWeil_divisor
    {q B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBound)
    (hr : 2 ≤ r) (hq : TaoCubefree q)
    (hχ : DirichletCharacter.IsPrimitive χ) :
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤
      ((r ^ (2 * r) * B ^ r : ℕ) : ℝ) * q +
        burgessCompositeWeilFactor q r *
          ((2 * r * B *
            (2 * B * q.divisors.card) ^ (2 * r - 1) : ℕ) : ℝ) := by
  have hmoment := burgess_shift_moment_le_of_completeWeil
    (B := B) χ hweil hr hq hχ
  have hsumNat := sum_burgessTupleGcdWeight_le q B r
  have hsumReal :
      (∑ uv ∈ burgessNondegenerateTuples B r,
          (burgessTupleGcdWeight q uv : ℝ)) ≤
        ((2 * r * B *
          (2 * B * q.divisors.card) ^ (2 * r - 1) : ℕ) : ℝ) := by
    exact_mod_cast hsumNat
  have hfactor0 : 0 ≤ burgessCompositeWeilFactor q r := by
    unfold burgessCompositeWeilFactor
    positivity
  have htail := mul_le_mul_of_nonneg_left hsumReal hfactor0
  exact hmoment.trans (add_le_add le_rfl htail)

/-- Literal `r = 7` version of the composite-Weil/gcd-sum reduction. -/
theorem burgess_shift_fourteenth_moment_le_of_completeWeil
    {q B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    (hq : TaoCubefree q) (hχ : DirichletCharacter.IsPrimitive χ) :
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤
      ((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        burgessCompositeWeilFactor q 7 *
          ∑ uv ∈ burgessNondegenerateTuples B 7,
            (burgessTupleGcdWeight q uv : ℝ) := by
  have hsplit := burgess_shift_moment_le_degenerate_add_nondegenerate χ
    (fun uv => burgessCompositeWeilFactor q 7 * burgessTupleGcdWeight q uv)
    (fun uv huv => hweil q B χ uv hq hχ huv)
  have hbadNat : (burgessDegenerateTuples B 7).card ≤
      7 ^ 14 * B ^ 7 := by
    simpa using card_burgessDegenerateTuples_le B 7
  have hbad : ((burgessDegenerateTuples B 7).card : ℝ) ≤
      ((7 ^ 14 * B ^ 7 : ℕ) : ℝ) := by exact_mod_cast hbadNat
  calc
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤
        ((burgessDegenerateTuples B 7).card : ℝ) * q +
          ∑ uv ∈ burgessNondegenerateTuples B 7,
            burgessCompositeWeilFactor q 7 *
              (burgessTupleGcdWeight q uv : ℝ) := by
      simpa using hsplit
    _ = ((burgessDegenerateTuples B 7).card : ℝ) * q +
        burgessCompositeWeilFactor q 7 *
          ∑ uv ∈ burgessNondegenerateTuples B 7,
            (burgessTupleGcdWeight q uv : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ ((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        burgessCompositeWeilFactor q 7 *
          ∑ uv ∈ burgessNondegenerateTuples B 7,
            (burgessTupleGcdWeight q uv : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hbad (Nat.cast_nonneg q)) le_rfl

/-- Literal `r = 7` divisor-count form of the composite-Weil moment bound. -/
theorem burgess_shift_fourteenth_moment_le_of_completeWeil_divisor
    {q B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    (hq : TaoCubefree q) (hχ : DirichletCharacter.IsPrimitive χ) :
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤
      ((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        burgessCompositeWeilFactor q 7 *
          ((14 * B * (2 * B * q.divisors.card) ^ 13 : ℕ) : ℝ) := by
  have hmoment := burgess_shift_fourteenth_moment_le_of_completeWeil
    (B := B) χ hweil hq hχ
  have hsumNat := sum_burgessTupleGcdWeight_le q B 7
  have hsumReal :
      (∑ uv ∈ burgessNondegenerateTuples B 7,
          (burgessTupleGcdWeight q uv : ℝ)) ≤
        ((14 * B * (2 * B * q.divisors.card) ^ 13 : ℕ) : ℝ) := by
    norm_num only [Nat.reduceMul, Nat.reduceSub] at hsumNat
    exact_mod_cast hsumNat
  have hfactor0 : 0 ≤ burgessCompositeWeilFactor q 7 := by
    unfold burgessCompositeWeilFactor
    positivity
  exact hmoment.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left hsumReal hfactor0))

/-- After the elementary divisor and prime-factor losses are absorbed, the
`r = 7` moment has the analytic shape used by Burgess: a diagonal term plus
`C_ε B^14 q^(1/2+ε)`.  The complete Weil estimate is now the only hypothesis
in this finite-moment statement. -/
theorem exists_burgess_shift_fourteenth_moment_le_of_completeWeil_rpow
    (hweil : TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {q B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        TaoCubefree q → DirichletCharacter.IsPrimitive χ →
        (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤
          ((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
            C * (B : ℝ) ^ 14 * (q : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
  obtain ⟨Cω, hCω, hω⟩ :=
    RiemannZeta.GuthMaynard.exists_pow_card_primeFactors_le_const_mul_rpow
      (A := (28 : ℝ)) (ε := ε / 2) (by norm_num) (by linarith)
  let D : ℝ := RiemannZeta.GuthMaynard.divisorEpsilonConstant (ε / 26)
  have hD : 0 < D := by
    exact RiemannZeta.GuthMaynard.divisorEpsilonConstant_pos (ε / 26)
  refine ⟨14 * 2 ^ 13 * Cω * D ^ 13, by positivity, ?_⟩
  intro q B _ χ hq hχ
  have hqPosNat : 0 < q := Nat.pos_of_ne_zero hq.ne_zero
  have hqPos : (0 : ℝ) < q := by exact_mod_cast hqPosNat
  have hmoment :=
    burgess_shift_fourteenth_moment_le_of_completeWeil_divisor
      (B := B) χ hweil hq hχ
  have hωq : (28 : ℝ) ^ q.primeFactors.card ≤
      Cω * (q : ℝ) ^ (ε / 2) := hω hqPosNat
  have hdiv : (q.divisors.card : ℝ) ≤ D * (q : ℝ) ^ (ε / 26) := by
    exact RiemannZeta.GuthMaynard.card_divisors_le_const_mul_rpow
      (by linarith) hq.ne_zero
  have htail : burgessCompositeWeilFactor q 7 *
        ((14 * B * (2 * B * q.divisors.card) ^ 13 : ℕ) : ℝ) ≤
      (14 * 2 ^ 13 * Cω * D ^ 13) * (B : ℝ) ^ 14 *
        (q : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
    have hpow13 : ((q : ℝ) ^ (ε / 26)) ^ 13 =
        (q : ℝ) ^ (ε / 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hqPos.le]
      congr 1
      norm_num
      ring
    have hqPowers : (q : ℝ) ^ (ε / 2) *
          (q : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ (ε / 2) =
        (q : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
      rw [← Real.rpow_add hqPos, ← Real.rpow_add hqPos]
      congr 1
      ring
    unfold burgessCompositeWeilFactor
    push_cast
    rw [Real.sqrt_eq_rpow]
    calc
      ((28 : ℝ) ^ q.primeFactors.card * (q : ℝ) ^ (1 / 2 : ℝ)) *
          (14 * B * (2 * B * q.divisors.card) ^ 13) ≤
        (Cω * (q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (1 / 2 : ℝ)) *
          (14 * B * (2 * B * (D * (q : ℝ) ^ (ε / 26))) ^ 13) := by
        gcongr
      _ = (14 * 2 ^ 13 * Cω * D ^ 13) * (B : ℝ) ^ 14 *
          (q : ℝ) ^ ((1 / 2 : ℝ) + ε) := by
        rw [mul_pow, mul_pow, mul_pow, hpow13]
        calc
          _ = (14 * 2 ^ 13 * Cω * D ^ 13) * (B : ℝ) ^ 14 *
              ((q : ℝ) ^ (ε / 2) * (q : ℝ) ^ (1 / 2 : ℝ) *
                (q : ℝ) ^ (ε / 2)) := by ring
          _ = _ := by rw [hqPowers]
  exact hmoment.trans (add_le_add le_rfl htail)

/-- Uniform complete-sum input gives the standard two-term Burgess moment
majorant.  The first term is the diagonal count times `q`; the second uses all
`B^(2r)` ordered tuples. -/
theorem burgess_shift_moment_le_standard
    {q B r : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {W : ℝ}
    (hW0 : 0 ≤ W)
    (hW : ∀ uv ∈ burgessNondegenerateTuples B r,
      ‖burgessCompleteCorrelation χ uv‖ ≤ W) :
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤
      ((r ^ (2 * r) * B ^ r : ℕ) : ℝ) * q +
        ((B ^ (2 * r) : ℕ) : ℝ) * W := by
  classical
  have hsplit := burgess_shift_moment_le_degenerate_add_nondegenerate
    χ (fun _ => W) hW
  have hbadNat : (burgessDegenerateTuples B r).card ≤
      r ^ (2 * r) * B ^ r := card_burgessDegenerateTuples_le B r
  have hbad : ((burgessDegenerateTuples B r).card : ℝ) ≤
      ((r ^ (2 * r) * B ^ r : ℕ) : ℝ) := by
    exact_mod_cast hbadNat
  have hgoodNat : (burgessNondegenerateTuples B r).card ≤ B ^ (2 * r) := by
    calc
      (burgessNondegenerateTuples B r).card ≤
          (Finset.univ : Finset
            ((Fin r → Fin B) × (Fin r → Fin B))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card ((Fin r → Fin B) × (Fin r → Fin B)) :=
        Finset.card_univ
      _ = B ^ (2 * r) := card_burgessTupleSpace B r
  have hgood : ((burgessNondegenerateTuples B r).card : ℝ) ≤
      ((B ^ (2 * r) : ℕ) : ℝ) := by
    exact_mod_cast hgoodNat
  calc
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ (2 * r) : ℝ) ≤
        ((burgessDegenerateTuples B r).card : ℝ) * q +
          ∑ _uv ∈ burgessNondegenerateTuples B r, W := hsplit
    _ = ((burgessDegenerateTuples B r).card : ℝ) * q +
        ((burgessNondegenerateTuples B r).card : ℝ) * W := by
      simp [nsmul_eq_mul]
    _ ≤ ((r ^ (2 * r) * B ^ r : ℕ) : ℝ) * q +
        ((B ^ (2 * r) : ℕ) : ℝ) * W :=
      add_le_add
        (mul_le_mul_of_nonneg_right hbad (Nat.cast_nonneg q))
        (mul_le_mul_of_nonneg_right hgood hW0)

/-- Literal `r = 7` specialization needed by Tao's decimal saving. -/
theorem burgess_shift_fourteenth_moment_le_standard
    {q B : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {W : ℝ}
    (hW0 : 0 ≤ W)
    (hW : ∀ uv ∈ burgessNondegenerateTuples B 7,
      ‖burgessCompleteCorrelation χ uv‖ ≤ W) :
    (∑ x : ZMod q, ‖burgessShiftSum B χ x‖ ^ 14 : ℝ) ≤
      ((7 ^ 14 * B ^ 7 : ℕ) : ℝ) * q +
        ((B ^ 14 : ℕ) : ℝ) * W := by
  simpa using burgess_shift_moment_le_standard (r := 7) χ hW0 hW

end

end Tao2026
