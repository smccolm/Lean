import Tao2026.BurgessWeilPrimeKummerAffineFourierSystem
import Tao2026.BurgessWeilPrimeThreeRoots

/-!
# The degree-divisible three-root Kummer Frobenius system

This file begins the unconditional construction of the remaining
three-or-more-root system.  The projective three-root change of variables is
generalized from `ZMod p` to an arbitrary field, so it can be applied on every
finite extension.  A split polynomial with exactly three roots is also given
an exact three-factor formula after arbitrary base change.

These identities are the extension-compatible algebraic input for combining
the projective Jacobi reduction with the now-proved Jacobi
Hasse--Davenport theorem.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The projective change sending `a` to zero and `c` to infinity, over an
arbitrary field. -/
def finiteFieldThreeRootMobiusEquiv
    (F : Type*) [Field F] [DecidableEq F]
    (a c : F) (hac : a ≠ c) : F ≃ F where
  toFun x := if x = c then 1 else (x - a) / (x - c)
  invFun y := if y = 1 then c else (y * c - a) / (y - 1)
  left_inv := by
    intro x
    by_cases hx : x = c
    · simp [hx]
    · have hden : x - c ≠ 0 := sub_ne_zero.mpr hx
      have hy : (x - a) / (x - c) ≠ 1 := by
        intro h
        rw [div_eq_one_iff_eq hden] at h
        exact hac (sub_right_inj.mp h)
      simp only [hx, ↓reduceIte, hy]
      rw [div_eq_iff (sub_ne_zero.mpr hy)]
      field_simp [hden]
      ring
  right_inv := by
    intro y
    by_cases hy : y = 1
    · simp [hy]
    · have hden : y - 1 ≠ 0 := sub_ne_zero.mpr hy
      have hx : (y * c - a) / (y - 1) ≠ c := by
        intro h
        rw [div_eq_iff hden] at h
        apply hac
        linear_combination -h
      simp only [hy, ↓reduceIte, hx]
      rw [div_eq_iff (sub_ne_zero.mpr hx)]
      field_simp [hden]
      ring

@[simp]
theorem finiteFieldThreeRootMobiusEquiv_symm_apply
    (F : Type*) [Field F] [DecidableEq F]
    (a c y : F) (hac : a ≠ c) :
    (finiteFieldThreeRootMobiusEquiv F a c hac).symm y =
      if y = 1 then c else (y * c - a) / (y - 1) :=
  rfl

/-- Pointwise cancellation of the common projective denominator for three
multiplicative characters whose product is trivial. -/
theorem finiteFieldThreeRootMobius_term
    {F : Type*} [Field F] [DecidableEq F]
    (α β γ : MulChar F ℂ) (hprod : α * β * γ = 1)
    (a b c : F) (hac : a ≠ c) (hbc : b ≠ c)
    (y : F) (hy : y ≠ 1) :
    let e := finiteFieldThreeRootMobiusEquiv F a c hac
    let lam := (a - b) / (c - b)
    α (e.symm y - a) * β (e.symm y - b) * γ (e.symm y - c) =
      (α (c - a) * β (c - b) * γ (c - a)) *
        (α y * β (y - lam)) := by
  dsimp only
  rw [finiteFieldThreeRootMobiusEquiv_symm_apply, if_neg hy]
  have hden : y - 1 ≠ 0 := sub_ne_zero.mpr hy
  have hcb : c - b ≠ 0 := sub_ne_zero.mpr hbc.symm
  have hxa : (y * c - a) / (y - 1) - a =
      y * (c - a) / (y - 1) := by field_simp; ring
  have hxb : (y * c - a) / (y - 1) - b =
      (c - b) * (y - (a - b) / (c - b)) / (y - 1) := by
    field_simp
    ring
  have hxc : (y * c - a) / (y - 1) - c =
      (c - a) / (y - 1) := by field_simp; ring
  rw [hxa, hxb, hxc]
  have hmapdivα (u v : F) : α (u / v) = α u / α v :=
    map_div₀ α.toMonoidWithZeroHom u v
  have hmapdivβ (u v : F) : β (u / v) = β u / β v :=
    map_div₀ β.toMonoidWithZeroHom u v
  have hmapdivγ (u v : F) : γ (u / v) = γ u / γ v :=
    map_div₀ γ.toMonoidWithZeroHom u v
  rw [hmapdivα, map_mul, hmapdivβ, map_mul, hmapdivγ]
  have hcancel : α (y - 1) * β (y - 1) * γ (y - 1) = 1 := by
    rw [← MulChar.mul_apply, ← MulChar.mul_apply, hprod]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hden)
  have hα : α (y - 1) ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hβ : β (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_mul] at hcancel
    exact zero_ne_one hcancel
  have hγ : γ (y - 1) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hcancel
    exact zero_ne_one hcancel
  field_simp [hα, hβ, hγ]
  linear_combination
    -(α y * α (c - a) * β (c - b) *
      β ((y * (c - b) - (a - b)) / (c - b)) * γ (c - a)) * hcancel

/-- The affine two-root Jacobi change of variables for two arbitrary
multiplicative characters over any finite field. -/
theorem finiteFieldTwoMulCharSum_eq_jacobiSum
    {F : Type*} [Field F] [Fintype F]
    (α β : MulChar F ℂ) (a b : F) (hab : a ≠ b) :
    (∑ x : F, α (x - a) * β (x - b)) =
      α (b - a) * β (a - b) * jacobiSum α β := by
  let d : F := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  let e : F ≃ F :=
    (Equiv.mulLeft₀ d hd).trans (Equiv.addRight a)
  calc
    (∑ x : F, α (x - a) * β (x - b)) =
        ∑ y : F, α (e y - a) * β (e y - b) :=
      (Equiv.sum_comp e
        (fun x : F => α (x - a) * β (x - b))).symm
    _ = α d * β (-d) * jacobiSum α β := by
      unfold jacobiSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      have hleft : e y - a = d * y := by simp [e]
      have hright : e y - b = (-d) * (1 - y) := by
        dsimp [e, d]
        ring
      rw [hleft, hright, map_mul, map_mul]
      ring
    _ = _ := by simp [d, neg_sub]

/-- The exact three-root projective reduction over an arbitrary finite
field. -/
theorem finiteFieldThreeRootMulCharSum_eq_twoRootSum_sub
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (α β γ : MulChar F ℂ) (hprod : α * β * γ = 1)
    (a b c : F) (hac : a ≠ c) (hbc : b ≠ c) :
    let lam := (a - b) / (c - b)
    (∑ x : F, α (x - a) * β (x - b) * γ (x - c)) =
      (α (c - a) * β (c - b) * γ (c - a)) *
        ((∑ y : F, α y * β (y - lam)) - β (1 - lam)) := by
  classical
  dsimp only
  let e := finiteFieldThreeRootMobiusEquiv F a c hac
  let f : F → ℂ := fun x =>
    α (x - a) * β (x - b) * γ (x - c)
  let g : F → ℂ := fun y =>
    α y * β (y - (a - b) / (c - b))
  let C : ℂ := α (c - a) * β (c - b) * γ (c - a)
  have hone : f (e.symm 1) = 0 := by
    simp [f, e, γ.map_zero]
  have hterm (y : F) (hy : y ∈ Finset.univ.erase 1) :
      f (e.symm y) = C * g y := by
    have hyOne : y ≠ 1 := by simpa using hy
    simpa [f, g, C, e] using
      finiteFieldThreeRootMobius_term α β γ hprod a b c hac hbc y hyOne
  calc
    (∑ x : F, α (x - a) * β (x - b) * γ (x - c)) =
        ∑ x : F, f x := by rfl
    _ = ∑ y : F, f (e.symm y) :=
      (Equiv.sum_comp e.symm f).symm
    _ = ∑ y ∈ Finset.univ.erase 1, f (e.symm y) := by
      exact (Finset.sum_erase (s := Finset.univ)
        (f := fun y => f (e.symm y)) hone).symm
    _ = C * ∑ y ∈ Finset.univ.erase 1, g y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      exact hterm
    _ = C * ((∑ y : F, g y) - g 1) := by
      congr 1
      have h := Finset.sum_erase_add Finset.univ g
        (Finset.mem_univ (1 : F))
      linear_combination h
    _ = _ := by simp [C, g, MulChar.map_one]

/-- Exact three-root factorization after base change to an arbitrary field. -/
theorem eval_map_eq_threeRootProduct
    {K L : Type*} [Field K] [DecidableEq K] [Field L] [Algebra K L]
    (P : Polynomial K) (a b c : K)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c}) (x : L) :
    (P.map (algebraMap K L)).eval x =
      algebraMap K L P.leadingCoeff *
        (x - algebraMap K L a) ^ P.rootMultiplicity a *
        (x - algebraMap K L b) ^ P.rootMultiplicity b *
        (x - algebraMap K L c) ^ P.rootMultiplicity c := by
  classical
  have hall : ∀ u ∈ P.roots, u = a ∨ u = b ∨ u = c := by
    intro u hu
    have hu' : u ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr hu
    rw [hroots] at hu'
    simpa [eq_comm] using hu'
  have hrootMultiset :
      P.roots =
        Multiset.replicate (P.roots.count a) a +
          Multiset.replicate (P.roots.count b) b +
            Multiset.replicate (P.roots.count c) c := by
    ext u
    by_cases hua : u = a
    · subst u
      rw [Multiset.count_add, Multiset.count_add,
        Multiset.count_replicate_self, Multiset.count_replicate,
        Multiset.count_replicate]
      simp [Ne.symm hab, Ne.symm hac]
    by_cases hub : u = b
    · subst u
      rw [Multiset.count_add, Multiset.count_add,
        Multiset.count_replicate, Multiset.count_replicate_self,
        Multiset.count_replicate]
      simp [hab, Ne.symm hbc]
    by_cases huc : u = c
    · subst u
      rw [Multiset.count_add, Multiset.count_add,
        Multiset.count_replicate, Multiset.count_replicate,
        Multiset.count_replicate_self]
      simp [hac, hbc]
    have hunot : u ∉ P.roots := by
      intro hu
      rcases hall u hu with rfl | rfl | rfl <;> contradiction
    rw [Multiset.count_eq_zero.mpr hunot, Multiset.count_add,
      Multiset.count_add, Multiset.count_replicate,
      Multiset.count_replicate, Multiset.count_replicate]
    simp [Ne.symm hua, Ne.symm hub, Ne.symm huc]
  have hcountA : P.roots.count a = P.rootMultiplicity a :=
    Polynomial.count_roots P
  have hcountB : P.roots.count b = P.rootMultiplicity b :=
    Polynomial.count_roots P
  have hcountC : P.roots.count c = P.rootMultiplicity c :=
    Polynomial.count_roots P
  conv_lhs => rw [Polynomial.eval_map, hP.eq_prod_roots]
  conv_lhs => rw [hrootMultiset]
  simp [hcountA, hcountB, hcountC, mul_assoc]

/-- The Jacobi main term attached to explicit three-root data over a finite
field. -/
def finiteFieldThreeRootJacobiMainData
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (lead a b c : F) (m n k : ℕ) : ℂ :=
  let lam := (a - b) / (c - b)
  χ lead *
    ((χ ^ m) (c - a) * (χ ^ n) (c - b) * (χ ^ k) (c - a)) *
      ((χ ^ m) lam * (χ ^ n) (-lam) * jacobiSum (χ ^ m) (χ ^ n))

/-- The projectively deleted-point term attached to explicit three-root
data. -/
def finiteFieldThreeRootDeletedData
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (lead a b c : F) (m n k : ℕ) : ℂ :=
  let lam := (a - b) / (c - b)
  χ lead *
    ((χ ^ m) (c - a) * (χ ^ n) (c - b) * (χ ^ k) (c - a)) *
      (χ ^ n) (1 - lam)

/-- The Jacobi main term in the projective reduction of a prime-field
three-root polynomial correlation. -/
def primeThreeRootJacobiMain
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) : ℂ :=
  finiteFieldThreeRootJacobiMainData χ P.leadingCoeff a b c
    (P.rootMultiplicity a) (P.rootMultiplicity b) (P.rootMultiplicity c)

/-- The single point deleted by the projective three-root transformation. -/
def primeThreeRootDeletedTerm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) : ℂ :=
  finiteFieldThreeRootDeletedData χ P.leadingCoeff a b c
    (P.rootMultiplicity a) (P.rootMultiplicity b) (P.rootMultiplicity c)

/-- Exact base-field three-root correlation as a Jacobi main term minus the
projectively deleted point. -/
theorem primePolynomialCharacterCorrelation_eq_threeRootMain_subDeleted
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hprod : (χ ^ P.rootMultiplicity a) *
      (χ ^ P.rootMultiplicity b) * (χ ^ P.rootMultiplicity c) = 1) :
    primePolynomialCharacterCorrelation p χ P =
      primeThreeRootJacobiMain p χ P a b c -
        primeThreeRootDeletedTerm p χ P a b c := by
  let m := P.rootMultiplicity a
  let n := P.rootMultiplicity b
  let k := P.rootMultiplicity c
  let lam : ZMod p := (a - b) / (c - b)
  have haMem : a ∈ P.roots.toFinset := by simp [hroots]
  have hbMem : b ∈ P.roots.toFinset := by simp [hroots]
  have hcMem : c ∈ P.roots.toFinset := by simp [hroots]
  have hm : m ≠ 0 := by
    dsimp [m]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haMem)).ne'
  have hn : n ≠ 0 := by
    dsimp [n]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hbMem)).ne'
  have hk : k ≠ 0 := by
    dsimp [k]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hcMem)).ne'
  have hlam : lam ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hbc.symm)
  unfold primePolynomialCharacterCorrelation
  calc
    (∑ x : ZMod p, χ (P.eval x)) =
        χ P.leadingCoeff *
          ∑ x : ZMod p,
            (χ ^ m) (x - a) * (χ ^ n) (x - b) * (χ ^ k) (x - c) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [show P.eval x =
          P.leadingCoeff * (x - a) ^ m * (x - b) ^ n * (x - c) ^ k by
        simpa [m, n, k] using
          (eval_map_eq_threeRootProduct P a b c hab hac hbc hP hroots x)]
      simp only [map_mul, map_pow]
      rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn,
        MulChar.pow_apply' χ hk]
      ring
    _ = χ P.leadingCoeff *
        (((χ ^ m) (c - a) * (χ ^ n) (c - b) * (χ ^ k) (c - a)) *
          ((∑ y : ZMod p, (χ ^ m) y * (χ ^ n) (y - lam)) -
            (χ ^ n) (1 - lam))) := by
      rw [finiteFieldThreeRootMulCharSum_eq_twoRootSum_sub
        (χ ^ m) (χ ^ n) (χ ^ k) (by simpa [m, n, k] using hprod)
        a b c hac hbc]
    _ = _ := by
      have htwo :
          (∑ y : ZMod p, (χ ^ m) y * (χ ^ n) (y - lam)) =
            (χ ^ m) lam * (χ ^ n) (-lam) *
              jacobiSum (χ ^ m) (χ ^ n) := by
        simpa using
          (finiteFieldTwoMulCharSum_eq_jacobiSum
            (χ ^ m) (χ ^ n) 0 lam hlam.symm)
      rw [htwo]
      simp [primeThreeRootJacobiMain, primeThreeRootDeletedTerm,
        finiteFieldThreeRootJacobiMainData, finiteFieldThreeRootDeletedData,
        m, n, k, lam]
      ring

/-- Exact projective Jacobi formula for every higher norm-lifted three-root
correlation. -/
theorem primeKummerExtensionCorrelation_succ_eq_threeRootJacobiSub
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hprod : (χ ^ P.rootMultiplicity a) *
      (χ ^ P.rootMultiplicity b) * (χ ^ P.rootMultiplicity c) = 1)
    (q : ℕ) :
    primeKummerExtensionCorrelation p χ P (q + 1) = by
      let E := FiniteField.Extension (ZMod p) p (q + 2)
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      let A : E := algebraMap (ZMod p) E a
      let B : E := algebraMap (ZMod p) E b
      let C : E := algebraMap (ZMod p) E c
      let m := P.rootMultiplicity a
      let n := P.rootMultiplicity b
      let k := P.rootMultiplicity c
      let lam : E := (A - B) / (C - B)
      exact χE (algebraMap (ZMod p) E P.leadingCoeff) *
        (((χE ^ m) (C - A) * (χE ^ n) (C - B) * (χE ^ k) (C - A)) *
          (((χE ^ m) lam * (χE ^ n) (-lam) *
              jacobiSum (χE ^ m) (χE ^ n)) -
            (χE ^ n) (1 - lam))) := by
  rw [primeKummerExtensionCorrelation_succ_eq_normLift]
  let E := FiniteField.Extension (ZMod p) p (q + 2)
  letI : Fintype E := Fintype.ofFinite E
  letI : DecidableEq E := Classical.decEq E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let A : E := algebraMap (ZMod p) E a
  let B : E := algebraMap (ZMod p) E b
  let C : E := algebraMap (ZMod p) E c
  let m := P.rootMultiplicity a
  let n := P.rootMultiplicity b
  let k := P.rootMultiplicity c
  let lam : E := (A - B) / (C - B)
  have hAB : A ≠ B := (algebraMap (ZMod p) E).injective.ne hab
  have hAC : A ≠ C := (algebraMap (ZMod p) E).injective.ne hac
  have hBC : B ≠ C := (algebraMap (ZMod p) E).injective.ne hbc
  have haMem : a ∈ P.roots.toFinset := by simp [hroots]
  have hbMem : b ∈ P.roots.toFinset := by simp [hroots]
  have hcMem : c ∈ P.roots.toFinset := by simp [hroots]
  have hm : m ≠ 0 := by
    dsimp [m]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haMem)).ne'
  have hn : n ≠ 0 := by
    dsimp [n]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hbMem)).ne'
  have hk : k ≠ 0 := by
    dsimp [k]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hcMem)).ne'
  have hprodE : (χE ^ m) * (χE ^ n) * (χE ^ k) = 1 := by
    change
      (finiteFieldNormLiftMulChar (ZMod p) E χ ^ m) *
        (finiteFieldNormLiftMulChar (ZMod p) E χ ^ n) *
          (finiteFieldNormLiftMulChar (ZMod p) E χ ^ k) = 1
    rw [← map_pow, ← map_pow, ← map_pow, ← map_mul, ← map_mul]
    rw [show χ ^ m * χ ^ n * χ ^ k = 1 by simpa [m, n, k] using hprod]
    exact map_one (finiteFieldNormLiftMulChar (ZMod p) E)
  have hlam : lam ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr hAB) (sub_ne_zero.mpr hBC.symm)
  calc
    (∑ x : E, χE ((P.map (algebraMap (ZMod p) E)).eval x)) =
        χE (algebraMap (ZMod p) E P.leadingCoeff) *
          ∑ x : E,
            (χE ^ m) (x - A) * (χE ^ n) (x - B) * (χE ^ k) (x - C) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [eval_map_eq_threeRootProduct P a b c hab hac hbc hP hroots x]
      change χE
          (algebraMap (ZMod p) E P.leadingCoeff *
            (x - A) ^ m * (x - B) ^ n * (x - C) ^ k) = _
      simp only [map_mul, map_pow]
      rw [MulChar.pow_apply' χE hm, MulChar.pow_apply' χE hn,
        MulChar.pow_apply' χE hk]
      ring
    _ = χE (algebraMap (ZMod p) E P.leadingCoeff) *
        (((χE ^ m) (C - A) * (χE ^ n) (C - B) * (χE ^ k) (C - A)) *
          ((∑ y : E, (χE ^ m) y * (χE ^ n) (y - lam)) -
            (χE ^ n) (1 - lam))) := by
      rw [finiteFieldThreeRootMulCharSum_eq_twoRootSum_sub
        (χE ^ m) (χE ^ n) (χE ^ k) hprodE A B C hAC hBC]
    _ = _ := by
      have htwo :
          (∑ y : E, (χE ^ m) y * (χE ^ n) (y - lam)) =
            (χE ^ m) lam * (χE ^ n) (-lam) *
              jacobiSum (χE ^ m) (χE ^ n) := by
        simpa using
          (finiteFieldTwoMulCharSum_eq_jacobiSum
            (χE ^ m) (χE ^ n) 0 lam hlam.symm)
      rw [htwo]

/-- Data-packaged form of the higher three-root projective formula. -/
theorem primeKummerExtensionCorrelation_succ_eq_threeRootData
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hprod : (χ ^ P.rootMultiplicity a) *
      (χ ^ P.rootMultiplicity b) * (χ ^ P.rootMultiplicity c) = 1)
    (q : ℕ) :
    primeKummerExtensionCorrelation p χ P (q + 1) = by
      let E := FiniteField.Extension (ZMod p) p (q + 2)
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      let A : E := algebraMap (ZMod p) E a
      let B : E := algebraMap (ZMod p) E b
      let C : E := algebraMap (ZMod p) E c
      exact
        finiteFieldThreeRootJacobiMainData χE
            (algebraMap (ZMod p) E P.leadingCoeff) A B C
            (P.rootMultiplicity a) (P.rootMultiplicity b)
            (P.rootMultiplicity c) -
          finiteFieldThreeRootDeletedData χE
            (algebraMap (ZMod p) E P.leadingCoeff) A B C
            (P.rootMultiplicity a) (P.rootMultiplicity b)
            (P.rootMultiplicity c) := by
  rw [primeKummerExtensionCorrelation_succ_eq_threeRootJacobiSub
    p χ P a b c hab hac hbc hP hroots hprod q]
  simp [finiteFieldThreeRootJacobiMainData, finiteFieldThreeRootDeletedData]
  ring

/-- Hasse--Davenport makes the three-root Jacobi main term a signed degree
power of its base-field value. -/
theorem finiteFieldNormLift_threeRootJacobiMainData
    (hHD : TaoPrimeFieldJacobiHasseDavenport)
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (lead a b c : ZMod p) (m n k : ℕ)
    (hχm : χ ^ m ≠ 1) : by
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      exact
        finiteFieldThreeRootJacobiMainData χE
            (algebraMap (ZMod p) E lead)
            (algebraMap (ZMod p) E a)
            (algebraMap (ZMod p) E b)
            (algebraMap (ZMod p) E c) m n k =
          (-1 : ℂ) ^ (d - 1) *
            finiteFieldThreeRootJacobiMainData χ lead a b c m n k ^ d := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let α := χ ^ m
  let β := χ ^ n
  let γ := χ ^ k
  have hpowM : χE ^ m = finiteFieldNormLiftMulChar (ZMod p) E α := by
    exact (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ m).symm
  have hpowN : χE ^ n = finiteFieldNormLiftMulChar (ZMod p) E β := by
    exact (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ n).symm
  have hpowK : χE ^ k = finiteFieldNormLiftMulChar (ZMod p) E γ := by
    exact (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ k).symm
  have hlift (η : MulChar (ZMod p) ℂ) (z : ZMod p) :
      finiteFieldNormLiftMulChar (ZMod p) E η
          (algebraMap (ZMod p) E z) = η z ^ d := by
    exact finiteFieldNormLiftMulChar_algebraMap_extension p d η z
  have hlamMap :
      algebraMap (ZMod p) E (a - b) /
          algebraMap (ZMod p) E (c - b) =
        algebraMap (ZMod p) E ((a - b) / (c - b)) := by
    exact (map_div₀ (algebraMap (ZMod p) E).toMonoidWithZeroHom
      (a - b) (c - b)).symm
  have hHD' := hHD p d α β (by simpa [α] using hχm)
  simp only [finiteFieldThreeRootJacobiMainData]
  change χE (algebraMap (ZMod p) E lead) *
      ((χE ^ m) (algebraMap (ZMod p) E c - algebraMap (ZMod p) E a) *
        (χE ^ n) (algebraMap (ZMod p) E c - algebraMap (ZMod p) E b) *
        (χE ^ k) (algebraMap (ZMod p) E c - algebraMap (ZMod p) E a)) *
      ((χE ^ m)
          ((algebraMap (ZMod p) E a - algebraMap (ZMod p) E b) /
            (algebraMap (ZMod p) E c - algebraMap (ZMod p) E b)) *
        (χE ^ n)
          (-((algebraMap (ZMod p) E a - algebraMap (ZMod p) E b) /
            (algebraMap (ZMod p) E c - algebraMap (ZMod p) E b))) *
        jacobiSum (χE ^ m) (χE ^ n)) = _
  rw [hpowM, hpowN, hpowK]
  simp only [← map_sub]
  rw [hlamMap, ← map_neg]
  rw [hlift χ lead, hlift α (c - a), hlift β (c - b),
    hlift γ (c - a), hlift α ((a - b) / (c - b)),
    hlift β (-((a - b) / (c - b))), hHD']
  dsimp [α, β, γ]
  ring

/-- The deleted-point contribution lifts as an ordinary degree power. -/
theorem finiteFieldNormLift_threeRootDeletedData
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (lead a b c : ZMod p) (m n k : ℕ) : by
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      exact
        finiteFieldThreeRootDeletedData χE
            (algebraMap (ZMod p) E lead)
            (algebraMap (ZMod p) E a)
            (algebraMap (ZMod p) E b)
            (algebraMap (ZMod p) E c) m n k =
          finiteFieldThreeRootDeletedData χ lead a b c m n k ^ d := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let α := χ ^ m
  let β := χ ^ n
  let γ := χ ^ k
  have hpowM : χE ^ m = finiteFieldNormLiftMulChar (ZMod p) E α := by
    exact (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ m).symm
  have hpowN : χE ^ n = finiteFieldNormLiftMulChar (ZMod p) E β := by
    exact (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ n).symm
  have hpowK : χE ^ k = finiteFieldNormLiftMulChar (ZMod p) E γ := by
    exact (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ k).symm
  have hlift (η : MulChar (ZMod p) ℂ) (z : ZMod p) :
      finiteFieldNormLiftMulChar (ZMod p) E η
          (algebraMap (ZMod p) E z) = η z ^ d := by
    exact finiteFieldNormLiftMulChar_algebraMap_extension p d η z
  have hlamMap :
      algebraMap (ZMod p) E (a - b) /
          algebraMap (ZMod p) E (c - b) =
        algebraMap (ZMod p) E ((a - b) / (c - b)) := by
    exact (map_div₀ (algebraMap (ZMod p) E).toMonoidWithZeroHom
      (a - b) (c - b)).symm
  have honeSubMap :
      1 - algebraMap (ZMod p) E (a - b) /
          algebraMap (ZMod p) E (c - b) =
        algebraMap (ZMod p) E (1 - (a - b) / (c - b)) := by
    rw [hlamMap, map_sub, map_one]
  simp only [finiteFieldThreeRootDeletedData]
  change χE (algebraMap (ZMod p) E lead) *
      ((χE ^ m) (algebraMap (ZMod p) E c - algebraMap (ZMod p) E a) *
        (χE ^ n) (algebraMap (ZMod p) E c - algebraMap (ZMod p) E b) *
        (χE ^ k) (algebraMap (ZMod p) E c - algebraMap (ZMod p) E a)) *
      (χE ^ n)
        (1 - (algebraMap (ZMod p) E a - algebraMap (ZMod p) E b) /
          (algebraMap (ZMod p) E c - algebraMap (ZMod p) E b)) = _
  rw [hpowM, hpowN, hpowK]
  simp only [← map_sub]
  rw [honeSubMap, hlift χ lead, hlift α (c - a), hlift β (c - b),
    hlift γ (c - a), hlift β (1 - (a - b) / (c - b))]
  dsimp [α, β, γ]
  ring

/-- The degree-divisible three-root correlation is the negative power sum of
the Jacobi eigenvalue and the deleted-point eigenvalue. -/
theorem primeKummerExtensionCorrelation_eq_threeRootTwoEigenPowers
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hprod : (χ ^ P.rootMultiplicity a) *
      (χ ^ P.rootMultiplicity b) * (χ ^ P.rootMultiplicity c) = 1)
    (hχm : χ ^ P.rootMultiplicity a ≠ 1) :
    ∀ q : ℕ, primeKummerExtensionCorrelation p χ P q =
      -((-primeThreeRootJacobiMain p χ P a b c) ^ (q + 1) +
        primeThreeRootDeletedTerm p χ P a b c ^ (q + 1))
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primePolynomialCharacterCorrelation_eq_threeRootMain_subDeleted
          p χ P a b c hab hac hbc hP hroots hprod]
      ring
  | q + 1 => by
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      let A : E := algebraMap (ZMod p) E a
      let B : E := algebraMap (ZMod p) E b
      let C : E := algebraMap (ZMod p) E c
      let m := P.rootMultiplicity a
      let n := P.rootMultiplicity b
      let k := P.rootMultiplicity c
      have hmain := finiteFieldNormLift_threeRootJacobiMainData
        taoPrimeFieldJacobiHasseDavenport p d χ P.leadingCoeff a b c
          m n k (by simpa [m] using hχm)
      have hdeleted := finiteFieldNormLift_threeRootDeletedData
        p d χ P.leadingCoeff a b c m n k
      rw [primeKummerExtensionCorrelation_succ_eq_threeRootData
        p χ P a b c hab hac hbc hP hroots hprod q]
      rw [show q + 1 + 1 = d by omega]
      change
        finiteFieldThreeRootJacobiMainData χE
            (algebraMap (ZMod p) E P.leadingCoeff) A B C m n k -
          finiteFieldThreeRootDeletedData χE
            (algebraMap (ZMod p) E P.leadingCoeff) A B C m n k = _
      rw [hmain, hdeleted]
      have hsign : (-1 : ℂ) ^ (d - 1) = -((-1 : ℂ) ^ d) := by
        simp [d, pow_succ]
      rw [hsign, neg_pow]
      simp only [primeThreeRootJacobiMain, primeThreeRootDeletedTerm]
      ring

/-- Prime-field Jacobi sums are algebraic integers. -/
theorem isIntegral_primeJacobiSum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (α β : MulChar (ZMod p) ℂ) : IsIntegral ℤ (jacobiSum α β) := by
  unfold jacobiSum
  exact IsIntegral.sum
    (fun x : ZMod p => α x * β (1 - x))
    (fun x _hx =>
      (isIntegral_mulChar_apply α x).mul
        (isIntegral_mulChar_apply β (1 - x)))

/-- The three-root Jacobi main term is an algebraic integer. -/
theorem isIntegral_primeThreeRootJacobiMain
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) :
    IsIntegral ℤ (primeThreeRootJacobiMain p χ P a b c) := by
  simp only [primeThreeRootJacobiMain,
    finiteFieldThreeRootJacobiMainData]
  exact ((isIntegral_mulChar_apply χ P.leadingCoeff).mul
    (((isIntegral_mulChar_apply (χ ^ P.rootMultiplicity a) (c - a)).mul
      (isIntegral_mulChar_apply (χ ^ P.rootMultiplicity b) (c - b))).mul
      (isIntegral_mulChar_apply (χ ^ P.rootMultiplicity c) (c - a)))).mul
    (((isIntegral_mulChar_apply (χ ^ P.rootMultiplicity a)
      ((a - b) / (c - b))).mul
      (isIntegral_mulChar_apply (χ ^ P.rootMultiplicity b)
        (-((a - b) / (c - b))))).mul
      (isIntegral_primeJacobiSum p
        (χ ^ P.rootMultiplicity a) (χ ^ P.rootMultiplicity b)))

/-- The projectively deleted-point term is an algebraic integer. -/
theorem isIntegral_primeThreeRootDeletedTerm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) :
    IsIntegral ℤ (primeThreeRootDeletedTerm p χ P a b c) := by
  simp only [primeThreeRootDeletedTerm,
    finiteFieldThreeRootDeletedData]
  exact ((isIntegral_mulChar_apply χ P.leadingCoeff).mul
    (((isIntegral_mulChar_apply (χ ^ P.rootMultiplicity a) (c - a)).mul
      (isIntegral_mulChar_apply (χ ^ P.rootMultiplicity b) (c - b))).mul
      (isIntegral_mulChar_apply (χ ^ P.rootMultiplicity c) (c - a)))).mul
    (isIntegral_mulChar_apply (χ ^ P.rootMultiplicity b)
      (1 - (a - b) / (c - b)))

/-- The Jacobi eigenvalue has weight at most one. -/
theorem norm_primeThreeRootJacobiMain_le_sqrt
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p)
    (hχm : χ ^ P.rootMultiplicity a ≠ 1) :
    ‖primeThreeRootJacobiMain p χ P a b c‖ ≤ Real.sqrt p := by
  simp only [primeThreeRootJacobiMain,
    finiteFieldThreeRootJacobiMainData, norm_mul]
  have hJ := norm_jacobiSum_le_sqrt_prime p
    (χ ^ P.rootMultiplicity a) (χ ^ P.rootMultiplicity b) hχm
  calc
    ‖χ P.leadingCoeff‖ *
          (‖(χ ^ P.rootMultiplicity a) (c - a)‖ *
            ‖(χ ^ P.rootMultiplicity b) (c - b)‖ *
            ‖(χ ^ P.rootMultiplicity c) (c - a)‖) *
          (‖(χ ^ P.rootMultiplicity a) ((a - b) / (c - b))‖ *
            ‖(χ ^ P.rootMultiplicity b) (-((a - b) / (c - b)))‖ *
            ‖jacobiSum (χ ^ P.rootMultiplicity a)
              (χ ^ P.rootMultiplicity b)‖) ≤
        1 * (1 * 1 * 1) * (1 * 1 * Real.sqrt p) := by
      gcongr <;> exact DirichletCharacter.norm_le_one _ _
    _ = Real.sqrt p := by ring

/-- The deleted-point eigenvalue has norm at most one. -/
theorem norm_primeThreeRootDeletedTerm_le_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) :
    ‖primeThreeRootDeletedTerm p χ P a b c‖ ≤ 1 := by
  simp only [primeThreeRootDeletedTerm,
    finiteFieldThreeRootDeletedData, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
          (‖(χ ^ P.rootMultiplicity a) (c - a)‖ *
            ‖(χ ^ P.rootMultiplicity b) (c - b)‖ *
            ‖(χ ^ P.rootMultiplicity c) (c - a)‖) *
          ‖(χ ^ P.rootMultiplicity b) (1 - (a - b) / (c - b))‖ ≤
        1 * (1 * 1 * 1) * 1 := by
      gcongr <;> exact DirichletCharacter.norm_le_one _ _
    _ = 1 := by ring

/-- The two eigenvalues in the projective three-root reduction. -/
def primeThreeRootEigenvalue
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) : Fin 2 → ℂ :=
  Fin.cases (-primeThreeRootJacobiMain p χ P a b c)
    (fun _ => primeThreeRootDeletedTerm p χ P a b c)

@[simp]
theorem sum_primeThreeRootEigenvalue_pow
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (d : ℕ) :
    (∑ i : Fin 2, primeThreeRootEigenvalue p χ P a b c i ^ d) =
      (-primeThreeRootJacobiMain p χ P a b c) ^ d +
        primeThreeRootDeletedTerm p χ P a b c ^ d := by
  rw [Fin.sum_univ_two]
  rfl

/-- A degree-divisible three-root correlation with a nontrivial first local
character has a genuine rank-two all-extension Frobenius system.  The two
eigenvalues are the signed Jacobi main term and the projectively deleted
point. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_product_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hcard : P.roots.toFinset.card = 3)
    (hprod : (χ ^ P.rootMultiplicity a) *
      (χ ^ P.rootMultiplicity b) * (χ ^ P.rootMultiplicity c) = 1)
    (hχm : χ ^ P.rootMultiplicity a ≠ 1) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  refine ⟨{
    rank := 2
    eigenvalue := primeThreeRootEigenvalue p χ P a b c
    rank_le := by omega
    integral := by
      intro i
      fin_cases i
      · simpa [primeThreeRootEigenvalue] using
          (isIntegral_primeThreeRootJacobiMain p χ P a b c).neg
      · simpa [primeThreeRootEigenvalue] using
          isIntegral_primeThreeRootDeletedTerm p χ P a b c
    weight_le := by
      intro i
      fin_cases i
      · simpa [primeThreeRootEigenvalue] using
          norm_primeThreeRootJacobiMain_le_sqrt p χ P a b c hχm
      · exact (by
          simpa [primeThreeRootEigenvalue] using
            (norm_primeThreeRootDeletedTerm_le_one p χ P a b c).trans hsqrt)
    trace_eq := by
      rw [primePolynomialCharacterCorrelation_eq_threeRootMain_subDeleted
          p χ P a b c hab hac hbc hP hroots hprod]
      have hsum := sum_primeThreeRootEigenvalue_pow p χ P a b c 1
      simp only [pow_one] at hsum
      rw [hsum]
      ring
    extensionTrace_eq := fun q => by
      rw [sum_primeThreeRootEigenvalue_pow p χ P a b c (q + 1)]
      exact primeKummerExtensionCorrelation_eq_threeRootTwoEigenPowers
        p χ P a b c hab hac hbc hP hroots hprod hχm q }⟩

/-- The exactly-three-root, all-active, degree-divisible part of the prime
Kummer Frobenius source theorem is unconditional. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_allActive_degree_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hcard : P.roots.toFinset.card = 3)
    (hactive : primeActiveRoots p χ P = P.roots.toFinset)
    (hdegree : orderOf χ ∣ P.natDegree) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
  obtain ⟨a, b, c, hab, hac, hbc, hroots⟩ := Finset.card_eq_three.mp hcard
  have haActive : a ∈ primeActiveRoots p χ P := by
    rw [hactive, hroots]
    simp
  have haNotDvd : ¬orderOf χ ∣ P.rootMultiplicity a := by
    intro hdvd
    exact (Finset.mem_filter.mp haActive).2
      ((Polynomial.count_roots P).symm ▸ hdvd)
  have hχm : χ ^ P.rootMultiplicity a ≠ 1 := by
    intro heq
    exact haNotDvd (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hsum := orderOf_dvd_sum_primeActiveRoots_count p χ P hP hdegree
  have habc : orderOf χ ∣
      P.rootMultiplicity a + P.rootMultiplicity b + P.rootMultiplicity c := by
    simpa [hactive, hroots, hab, hac, hbc, Polynomial.count_roots,
      add_assoc, add_comm, add_left_comm] using hsum
  have hprod : (χ ^ P.rootMultiplicity a) *
      (χ ^ P.rootMultiplicity b) * (χ ^ P.rootMultiplicity c) = 1 := by
    rw [← pow_add, ← pow_add]
    exact orderOf_dvd_iff_pow_eq_one.mp habc
  exact exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_product_one
    p χ P a b c hab hac hbc hP hroots hcard hprod hχm

/-- Every degree-divisible exactly-three-root case is unconditional.  Only one
root character needs to be nontrivial; the other two may include the unique
inactive root. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_degree_dvd
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hdegree : orderOf χ ∣ P.natDegree)
    (hcard : P.roots.toFinset.card = 3) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
  have hnotCount : ¬orderOf χ ∣ P.roots.count a := by
    intro hdvd
    exact hnot ((Polynomial.count_roots P) ▸ hdvd)
  have hcountA : P.roots.count a ≠ 0 := by
    intro hzero
    exact hnotCount (by simp [hzero])
  have haRoot : a ∈ P.roots.toFinset :=
    Multiset.mem_toFinset.mpr
      (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcountA))
  obtain ⟨u, v, w, huv, huw, hvw, hroots⟩ := Finset.card_eq_three.mp hcard
  have haCases : a = u ∨ a = v ∨ a = w := by
    rw [hroots] at haRoot
    simpa using haRoot
  have build (r s t : ZMod p) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
      (hset : P.roots.toFinset = {r, s, t})
      (hrActive : ¬orderOf χ ∣ P.rootMultiplicity r) :
      Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
    have htotal :
        (∑ x ∈ P.roots.toFinset, P.roots.count x) = P.natDegree := by
      rw [Multiset.toFinset_sum_count_eq, ← hP.natDegree_eq_card_roots]
    have hdiv := hdegree
    rw [← htotal] at hdiv
    have hrst : orderOf χ ∣
        P.rootMultiplicity r + P.rootMultiplicity s + P.rootMultiplicity t := by
      simpa [hset, hrs, hrt, hst, Polynomial.count_roots,
        add_assoc, add_comm, add_left_comm] using hdiv
    have hprod : (χ ^ P.rootMultiplicity r) *
        (χ ^ P.rootMultiplicity s) * (χ ^ P.rootMultiplicity t) = 1 := by
      rw [← pow_add, ← pow_add]
      exact orderOf_dvd_iff_pow_eq_one.mp hrst
    have hχr : χ ^ P.rootMultiplicity r ≠ 1 := by
      intro heq
      exact hrActive (orderOf_dvd_iff_pow_eq_one.mpr heq)
    exact exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_product_one
      p χ P r s t hrs hrt hst hP hset hcard hprod hχr
  rcases haCases with hau | hav | haw
  · subst u
    exact build a v w huv huw hvw hroots hnot
  · subst v
    apply build a u w huv.symm hvw huw
    · rw [hroots]
      ext x
      simp [or_left_comm]
    · exact hnot
  · subst w
    apply build a u v huw.symm hvw.symm huv
    · rw [hroots]
      ext x
      simp [or_comm, or_left_comm]
    · exact hnot

/-- The remaining three-or-more-root source after removing the unconditional
degree-divisible exactly-three-root case. -/
def TaoPrimeKummerIsotypicFrobeniusSystemThreeNondivisibleOrFourRootsOrMore :
    Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      ((P.roots.toFinset.card = 3 ∧ ¬orderOf χ ∣ P.natDegree) ∨
        4 ≤ P.roots.toFinset.card) →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- The full three-or-more-root geometric source is equivalent to the smaller
residual consisting of the nondivisible three-root case and four or more
roots. -/
theorem taoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore_iff_threeNondivisibleOrFourRootsOrMore :
    TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore ↔
      TaoPrimeKummerIsotypicFrobeniusSystemThreeNondivisibleOrFourRootsOrMore := by
  constructor
  · intro hfull p _ _ χ P hχ hP hpower hcases
    apply hfull p χ P hχ hP hpower
    rcases hcases with ⟨hcard, _⟩ | hfour
    · omega
    · omega
  · intro hres p _ _ χ P hχ hP hpower hthree
    by_cases hcard : P.roots.toFinset.card = 3
    · by_cases hdegree : orderOf χ ∣ P.natDegree
      · have hP0 : P ≠ 0 := by
          intro hzero
          subst P
          exact hpower (isMulCharOrderScalarPower_zero χ)
        obtain ⟨a, _ha, hnot⟩ :=
          (not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
            χ P hP0 hP).mp hpower
        exact exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_degree_dvd
          p χ P a hP hnot hdegree hcard
      · exact hres p χ P hχ hP hpower (Or.inl ⟨hcard, hdegree⟩)
    · exact hres p χ P hχ hP hpower (Or.inr (by omega))

end

end Tao2026
