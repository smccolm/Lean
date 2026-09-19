import Tao2026.BurgessWeilPrimeKummerThreeRootFrobenius

/-!
# Three-root Kummer systems with an inactive root

If one of three roots is inactive, its local character is the trivial
multiplicative character.  The correlation is therefore a two-root Jacobi
sum with one affine point deleted.  Both terms lift by fixed degree powers,
giving an explicit rank-two Frobenius system without a degree-divisibility
assumption.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Multiplication by a trivial third local character deletes exactly its
zero. -/
theorem finiteFieldThreeRootMulCharSum_of_third_eq_one
    {F : Type*} [Field F] [Fintype F]
    (α β γ : MulChar F ℂ) (hγ : γ = 1)
    (a b c : F) :
    (∑ x : F, α (x - a) * β (x - b) * γ (x - c)) =
      (∑ x : F, α (x - a) * β (x - b)) -
        α (c - a) * β (c - b) := by
  classical
  let f : F → ℂ := fun x => α (x - a) * β (x - b)
  let g : F → ℂ := fun x => f x * γ (x - c)
  have hgc : g c = 0 := by
    simp only [g, f, sub_self]
    rw [hγ, MulChar.map_zero]
    ring
  have hterm (x : F) (hx : x ∈ Finset.univ.erase c) : g x = f x := by
    have hxc : x - c ≠ 0 := sub_ne_zero.mpr (by simpa using hx)
    simp [g, hγ, MulChar.one_apply (isUnit_iff_ne_zero.mpr hxc)]
  calc
    (∑ x : F, α (x - a) * β (x - b) * γ (x - c)) =
        ∑ x : F, g x := by rfl
    _ = ∑ x ∈ Finset.univ.erase c, g x :=
      (Finset.sum_erase (s := Finset.univ) (f := g) hgc).symm
    _ = ∑ x ∈ Finset.univ.erase c, f x := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = (∑ x : F, f x) - f c := by
      have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ c)
      linear_combination h
    _ = _ := by rfl

/-- Jacobi main term for three roots when the third local character is
trivial. -/
def finiteFieldThreeRootInactiveJacobiMainData
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (lead a b : F) (m n : ℕ) : ℂ :=
  χ lead * ((χ ^ m) (b - a) * (χ ^ n) (a - b) *
    jacobiSum (χ ^ m) (χ ^ n))

/-- The point removed by the inactive third root. -/
def finiteFieldThreeRootInactiveDeletedData
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (lead a b c : F) (m n : ℕ) : ℂ :=
  χ lead * ((χ ^ m) (c - a) * (χ ^ n) (c - b))

def primeThreeRootInactiveJacobiMain
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) : ℂ :=
  finiteFieldThreeRootInactiveJacobiMainData χ P.leadingCoeff a b
    (P.rootMultiplicity a) (P.rootMultiplicity b)

def primeThreeRootInactiveDeletedTerm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) : ℂ :=
  finiteFieldThreeRootInactiveDeletedData χ P.leadingCoeff a b c
    (P.rootMultiplicity a) (P.rootMultiplicity b)

/-- Base-field correlation in the presence of an inactive third root. -/
theorem primePolynomialCharacterCorrelation_eq_threeRootInactiveMain_subDeleted
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hχc : χ ^ P.rootMultiplicity c = 1) :
    primePolynomialCharacterCorrelation p χ P =
      primeThreeRootInactiveJacobiMain p χ P a b -
        primeThreeRootInactiveDeletedTerm p χ P a b c := by
  let m := P.rootMultiplicity a
  let n := P.rootMultiplicity b
  let k := P.rootMultiplicity c
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
        (((χ ^ m) (b - a) * (χ ^ n) (a - b) *
            jacobiSum (χ ^ m) (χ ^ n)) -
          ((χ ^ m) (c - a) * (χ ^ n) (c - b))) := by
      rw [finiteFieldThreeRootMulCharSum_of_third_eq_one
        (χ ^ m) (χ ^ n) (χ ^ k) (by simpa [k] using hχc) a b c]
      rw [finiteFieldTwoMulCharSum_eq_jacobiSum (χ ^ m) (χ ^ n) a b hab]
    _ = _ := by
      simp [primeThreeRootInactiveJacobiMain,
        primeThreeRootInactiveDeletedTerm,
        finiteFieldThreeRootInactiveJacobiMainData,
        finiteFieldThreeRootInactiveDeletedData, m, n]
      ring

/-- Higher-extension correlation in the presence of an inactive third root. -/
theorem primeKummerExtensionCorrelation_succ_eq_threeRootInactiveData
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hχc : χ ^ P.rootMultiplicity c = 1) (q : ℕ) :
    primeKummerExtensionCorrelation p χ P (q + 1) = by
      let d := q + 2
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      exact finiteFieldThreeRootInactiveJacobiMainData χE
          (algebraMap (ZMod p) E P.leadingCoeff)
          (algebraMap (ZMod p) E a) (algebraMap (ZMod p) E b)
          (P.rootMultiplicity a) (P.rootMultiplicity b) -
        finiteFieldThreeRootInactiveDeletedData χE
          (algebraMap (ZMod p) E P.leadingCoeff)
          (algebraMap (ZMod p) E a) (algebraMap (ZMod p) E b)
          (algebraMap (ZMod p) E c)
          (P.rootMultiplicity a) (P.rootMultiplicity b) := by
  rw [primeKummerExtensionCorrelation_succ_eq_normLift]
  let d := q + 2
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let A : E := algebraMap (ZMod p) E a
  let B : E := algebraMap (ZMod p) E b
  let C : E := algebraMap (ZMod p) E c
  let m := P.rootMultiplicity a
  let n := P.rootMultiplicity b
  let k := P.rootMultiplicity c
  have hAB : A ≠ B := (algebraMap (ZMod p) E).injective.ne hab
  have hpowK : χE ^ k = finiteFieldNormLiftMulChar (ZMod p) E (χ ^ k) :=
    (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ k).symm
  have hχEk : χE ^ k = 1 := by
    rw [hpowK, show χ ^ k = 1 by simpa [k] using hχc]
    exact map_one (finiteFieldNormLiftMulChar (ZMod p) E)
  have haMem : a ∈ P.roots.toFinset := by simp [hroots]
  have hbMem : b ∈ P.roots.toFinset := by simp [hroots]
  have hcMem : c ∈ P.roots.toFinset := by simp [hroots]
  have hm : m ≠ 0 := by
    dsimp [m]; rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haMem)).ne'
  have hn : n ≠ 0 := by
    dsimp [n]; rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hbMem)).ne'
  have hk : k ≠ 0 := by
    dsimp [k]; rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hcMem)).ne'
  calc
    (∑ x : E, χE ((P.map (algebraMap (ZMod p) E)).eval x)) =
        χE (algebraMap (ZMod p) E P.leadingCoeff) *
          ∑ x : E, (χE ^ m) (x - A) * (χE ^ n) (x - B) *
            (χE ^ k) (x - C) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [eval_map_eq_threeRootProduct P a b c hab hac hbc hP hroots x,
        map_mul, map_mul, map_mul, map_pow, map_pow, map_pow]
      rw [MulChar.pow_apply' χE hm, MulChar.pow_apply' χE hn,
        MulChar.pow_apply' χE hk]
      dsimp [A, B, C, m, n, k]
      ring
    _ = χE (algebraMap (ZMod p) E P.leadingCoeff) *
        (((χE ^ m) (B - A) * (χE ^ n) (A - B) *
            jacobiSum (χE ^ m) (χE ^ n)) -
          ((χE ^ m) (C - A) * (χE ^ n) (C - B))) := by
      rw [finiteFieldThreeRootMulCharSum_of_third_eq_one
        (χE ^ m) (χE ^ n) (χE ^ k) hχEk A B C]
      rw [finiteFieldTwoMulCharSum_eq_jacobiSum
        (χE ^ m) (χE ^ n) A B hAB]
    _ = _ := by
      simp only [finiteFieldThreeRootInactiveJacobiMainData,
        finiteFieldThreeRootInactiveDeletedData]
      ring

/-- The inactive-root Jacobi main term obeys signed Hasse--Davenport lifting. -/
theorem finiteFieldNormLift_threeRootInactiveJacobiMainData
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (lead a b : ZMod p) (m n : ℕ)
    (hχm : χ ^ m ≠ 1) : by
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      exact finiteFieldThreeRootInactiveJacobiMainData χE
          (algebraMap (ZMod p) E lead) (algebraMap (ZMod p) E a)
          (algebraMap (ZMod p) E b) m n =
        (-1 : ℂ) ^ (d - 1) *
          finiteFieldThreeRootInactiveJacobiMainData χ lead a b m n ^ d := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let α := χ ^ m
  let β := χ ^ n
  have hpowM : χE ^ m = finiteFieldNormLiftMulChar (ZMod p) E α :=
    (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ m).symm
  have hpowN : χE ^ n = finiteFieldNormLiftMulChar (ZMod p) E β :=
    (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ n).symm
  have hlift (η : MulChar (ZMod p) ℂ) (z : ZMod p) :
      finiteFieldNormLiftMulChar (ZMod p) E η
          (algebraMap (ZMod p) E z) = η z ^ d :=
    finiteFieldNormLiftMulChar_algebraMap_extension p d η z
  have hHD := taoPrimeFieldJacobiHasseDavenport p d α β
    (by simpa [α] using hχm)
  simp only [finiteFieldThreeRootInactiveJacobiMainData]
  change χE (algebraMap (ZMod p) E lead) *
      ((χE ^ m) (algebraMap (ZMod p) E b - algebraMap (ZMod p) E a) *
        (χE ^ n) (algebraMap (ZMod p) E a - algebraMap (ZMod p) E b) *
        jacobiSum (χE ^ m) (χE ^ n)) = _
  rw [hpowM, hpowN, ← map_sub, ← map_sub,
    hlift χ lead, hlift α (b - a), hlift β (a - b), hHD]
  dsimp [α, β]
  ring

/-- The deleted inactive-root point lifts by an ordinary degree power. -/
theorem finiteFieldNormLift_threeRootInactiveDeletedData
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (lead a b c : ZMod p) (m n : ℕ) : by
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      exact finiteFieldThreeRootInactiveDeletedData χE
          (algebraMap (ZMod p) E lead) (algebraMap (ZMod p) E a)
          (algebraMap (ZMod p) E b) (algebraMap (ZMod p) E c) m n =
        finiteFieldThreeRootInactiveDeletedData χ lead a b c m n ^ d := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let α := χ ^ m
  let β := χ ^ n
  have hpowM : χE ^ m = finiteFieldNormLiftMulChar (ZMod p) E α :=
    (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ m).symm
  have hpowN : χE ^ n = finiteFieldNormLiftMulChar (ZMod p) E β :=
    (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ n).symm
  have hlift (η : MulChar (ZMod p) ℂ) (z : ZMod p) :
      finiteFieldNormLiftMulChar (ZMod p) E η
          (algebraMap (ZMod p) E z) = η z ^ d :=
    finiteFieldNormLiftMulChar_algebraMap_extension p d η z
  simp only [finiteFieldThreeRootInactiveDeletedData]
  change χE (algebraMap (ZMod p) E lead) *
      ((χE ^ m) (algebraMap (ZMod p) E c - algebraMap (ZMod p) E a) *
        (χE ^ n) (algebraMap (ZMod p) E c - algebraMap (ZMod p) E b)) = _
  rw [hpowM, hpowN, ← map_sub, ← map_sub,
    hlift χ lead, hlift α (c - a), hlift β (c - b)]
  dsimp [α, β]
  ring

/-- All inactive-root extension correlations are the negative power sum of
two fixed eigenvalues. -/
theorem primeKummerExtensionCorrelation_eq_threeRootInactiveTwoEigenPowers
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hχa : χ ^ P.rootMultiplicity a ≠ 1)
    (hχc : χ ^ P.rootMultiplicity c = 1) :
    ∀ q : ℕ, primeKummerExtensionCorrelation p χ P q =
      -((-primeThreeRootInactiveJacobiMain p χ P a b) ^ (q + 1) +
        primeThreeRootInactiveDeletedTerm p χ P a b c ^ (q + 1))
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primePolynomialCharacterCorrelation_eq_threeRootInactiveMain_subDeleted
          p χ P a b c hab hac hbc hP hroots hχc]
      ring
  | q + 1 => by
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      have hmain := finiteFieldNormLift_threeRootInactiveJacobiMainData
        p d χ P.leadingCoeff a b (P.rootMultiplicity a)
          (P.rootMultiplicity b) hχa
      have hdeleted := finiteFieldNormLift_threeRootInactiveDeletedData
        p d χ P.leadingCoeff a b c (P.rootMultiplicity a)
          (P.rootMultiplicity b)
      rw [primeKummerExtensionCorrelation_succ_eq_threeRootInactiveData
        p χ P a b c hab hac hbc hP hroots hχc q]
      rw [show q + 1 + 1 = d by omega]
      change finiteFieldThreeRootInactiveJacobiMainData χE
          (algebraMap (ZMod p) E P.leadingCoeff)
          (algebraMap (ZMod p) E a) (algebraMap (ZMod p) E b)
          (P.rootMultiplicity a) (P.rootMultiplicity b) -
        finiteFieldThreeRootInactiveDeletedData χE
          (algebraMap (ZMod p) E P.leadingCoeff)
          (algebraMap (ZMod p) E a) (algebraMap (ZMod p) E b)
          (algebraMap (ZMod p) E c)
          (P.rootMultiplicity a) (P.rootMultiplicity b) = _
      rw [hmain, hdeleted]
      have hsign : (-1 : ℂ) ^ (d - 1) = -((-1 : ℂ) ^ d) := by
        simp [d, pow_succ]
      rw [hsign, neg_pow]
      simp only [primeThreeRootInactiveJacobiMain,
        primeThreeRootInactiveDeletedTerm]
      ring

theorem isIntegral_primeThreeRootInactiveJacobiMain
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) :
    IsIntegral ℤ (primeThreeRootInactiveJacobiMain p χ P a b) := by
  simp only [primeThreeRootInactiveJacobiMain,
    finiteFieldThreeRootInactiveJacobiMainData]
  exact (isIntegral_mulChar_apply χ P.leadingCoeff).mul
    (((isIntegral_mulChar_apply (χ ^ P.rootMultiplicity a) (b - a)).mul
      (isIntegral_mulChar_apply (χ ^ P.rootMultiplicity b) (a - b))).mul
      (isIntegral_primeJacobiSum p
        (χ ^ P.rootMultiplicity a) (χ ^ P.rootMultiplicity b)))

theorem isIntegral_primeThreeRootInactiveDeletedTerm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) :
    IsIntegral ℤ (primeThreeRootInactiveDeletedTerm p χ P a b c) := by
  simp only [primeThreeRootInactiveDeletedTerm,
    finiteFieldThreeRootInactiveDeletedData]
  exact (isIntegral_mulChar_apply χ P.leadingCoeff).mul
    ((isIntegral_mulChar_apply (χ ^ P.rootMultiplicity a) (c - a)).mul
      (isIntegral_mulChar_apply (χ ^ P.rootMultiplicity b) (c - b)))

theorem norm_primeThreeRootInactiveJacobiMain_le_sqrt
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hχa : χ ^ P.rootMultiplicity a ≠ 1) :
    ‖primeThreeRootInactiveJacobiMain p χ P a b‖ ≤ Real.sqrt p := by
  simp only [primeThreeRootInactiveJacobiMain,
    finiteFieldThreeRootInactiveJacobiMainData, norm_mul]
  have hJ := norm_jacobiSum_le_sqrt_prime p
    (χ ^ P.rootMultiplicity a) (χ ^ P.rootMultiplicity b) hχa
  calc
    ‖χ P.leadingCoeff‖ *
        (‖(χ ^ P.rootMultiplicity a) (b - a)‖ *
          ‖(χ ^ P.rootMultiplicity b) (a - b)‖ *
          ‖jacobiSum (χ ^ P.rootMultiplicity a)
            (χ ^ P.rootMultiplicity b)‖) ≤
        1 * (1 * 1 * Real.sqrt p) := by
      gcongr <;> exact DirichletCharacter.norm_le_one _ _
    _ = Real.sqrt p := by ring

theorem norm_primeThreeRootInactiveDeletedTerm_le_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) :
    ‖primeThreeRootInactiveDeletedTerm p χ P a b c‖ ≤ 1 := by
  simp only [primeThreeRootInactiveDeletedTerm,
    finiteFieldThreeRootInactiveDeletedData, norm_mul]
  calc
    ‖χ P.leadingCoeff‖ *
        (‖(χ ^ P.rootMultiplicity a) (c - a)‖ *
          ‖(χ ^ P.rootMultiplicity b) (c - b)‖) ≤
        1 * (1 * 1) := by
      gcongr <;> exact DirichletCharacter.norm_le_one _ _
    _ = 1 := by ring

def primeThreeRootInactiveEigenvalue
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) : Fin 2 → ℂ :=
  Fin.cases (-primeThreeRootInactiveJacobiMain p χ P a b)
    (fun _ => primeThreeRootInactiveDeletedTerm p χ P a b c)

@[simp]
theorem sum_primeThreeRootInactiveEigenvalue_pow
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (d : ℕ) :
    (∑ i : Fin 2, primeThreeRootInactiveEigenvalue p χ P a b c i ^ d) =
      (-primeThreeRootInactiveJacobiMain p χ P a b) ^ d +
        primeThreeRootInactiveDeletedTerm p χ P a b c ^ d := by
  rw [Fin.sum_univ_two]
  rfl

/-- An active first root and inactive third root give an explicit rank-two
all-extension Frobenius system. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_inactive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b c : ZMod p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hP : P.Splits) (hroots : P.roots.toFinset = {a, b, c})
    (hcard : P.roots.toFinset.card = 3)
    (hχa : χ ^ P.rootMultiplicity a ≠ 1)
    (hχc : χ ^ P.rootMultiplicity c = 1) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  refine ⟨{
    rank := 2
    eigenvalue := primeThreeRootInactiveEigenvalue p χ P a b c
    rank_le := by omega
    integral := by
      intro i
      fin_cases i
      · simpa [primeThreeRootInactiveEigenvalue] using
          (isIntegral_primeThreeRootInactiveJacobiMain p χ P a b).neg
      · simpa [primeThreeRootInactiveEigenvalue] using
          isIntegral_primeThreeRootInactiveDeletedTerm p χ P a b c
    weight_le := by
      intro i
      fin_cases i
      · simpa [primeThreeRootInactiveEigenvalue] using
          norm_primeThreeRootInactiveJacobiMain_le_sqrt p χ P a b hχa
      · simpa [primeThreeRootInactiveEigenvalue] using
          (norm_primeThreeRootInactiveDeletedTerm_le_one p χ P a b c).trans hsqrt
    trace_eq := by
      rw [primePolynomialCharacterCorrelation_eq_threeRootInactiveMain_subDeleted
        p χ P a b c hab hac hbc hP hroots hχc]
      have hsum := sum_primeThreeRootInactiveEigenvalue_pow p χ P a b c 1
      simp only [pow_one] at hsum
      rw [hsum]
      ring
    extensionTrace_eq := fun q => by
      rw [sum_primeThreeRootInactiveEigenvalue_pow p χ P a b c (q + 1)]
      exact primeKummerExtensionCorrelation_eq_threeRootInactiveTwoEigenPowers
        p χ P a b c hab hac hbc hP hroots hχa hχc q }⟩

/-- Every exactly-three-root case with at least one inactive root has an
explicit rank-two Frobenius system. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_not_allActive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hpower : ¬IsMulCharOrderScalarPower χ P)
    (hcard : P.roots.toFinset.card = 3)
    (hactive : primeActiveRoots p χ P ≠ P.roots.toFinset) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
  have hP0 : P ≠ 0 := by
    intro hzero
    subst P
    exact hpower (isMulCharOrderScalarPower_zero χ)
  obtain ⟨a, haRoot, haNotDvd⟩ :=
    (not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
      χ P hP0 hP).mp hpower
  have haNotCount : ¬orderOf χ ∣ P.roots.count a := by
    intro hdvd
    exact haNotDvd ((Polynomial.count_roots P) ▸ hdvd)
  have haActive : a ∈ primeActiveRoots p χ P :=
    Finset.mem_filter.mpr ⟨haRoot, haNotCount⟩
  have hstrict : primeActiveRoots p χ P ⊂ P.roots.toFinset :=
    Finset.ssubset_iff_subset_ne.mpr
      ⟨primeActiveRoots_subset_roots p χ P, hactive⟩
  obtain ⟨c, hcRoot, hcNotActive⟩ := Finset.exists_of_ssubset hstrict
  have hcDvdCount : orderOf χ ∣ P.roots.count c := by
    by_contra hcNotDvd
    exact hcNotActive (Finset.mem_filter.mpr ⟨hcRoot, hcNotDvd⟩)
  have hcDvd : orderOf χ ∣ P.rootMultiplicity c :=
    (Polynomial.count_roots P) ▸ hcDvdCount
  have hac : a ≠ c := by
    intro heq
    subst c
    exact haNotDvd hcDvd
  have hχa : χ ^ P.rootMultiplicity a ≠ 1 := by
    intro heq
    exact haNotDvd (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hχc : χ ^ P.rootMultiplicity c = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hcDvd
  have hcardErase : (P.roots.toFinset.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem haRoot, hcard]
  obtain ⟨u, v, huv, herase⟩ := Finset.card_eq_two.mp hcardErase
  have hcErase : c ∈ P.roots.toFinset.erase a :=
    Finset.mem_erase.mpr ⟨hac.symm, hcRoot⟩
  have hcCases : c = u ∨ c = v := by
    rw [herase] at hcErase
    simpa using hcErase
  rcases hcCases with hcu | hcv
  · subst u
    have hvErase : v ∈ P.roots.toFinset.erase a := by simp [herase]
    have hav : a ≠ v := (Finset.mem_erase.mp hvErase).1.symm
    have hroots : P.roots.toFinset = {a, v, c} := by
      calc
        P.roots.toFinset = insert a (P.roots.toFinset.erase a) :=
          (Finset.insert_erase haRoot).symm
        _ = {a, v, c} := by
          rw [herase]
          ext x
          simp [or_comm]
    exact exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_inactive
      p χ P a v c hav hac huv.symm hP hroots hcard hχa hχc
  · subst v
    have huErase : u ∈ P.roots.toFinset.erase a := by simp [herase]
    have hau : a ≠ u := (Finset.mem_erase.mp huErase).1.symm
    have hroots : P.roots.toFinset = {a, u, c} := by
      calc
        P.roots.toFinset = insert a (P.roots.toFinset.erase a) :=
          (Finset.insert_erase haRoot).symm
        _ = {a, u, c} := by rw [herase]
    exact exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_inactive
      p χ P a u c hau hac huv hP hroots hcard hχa hχc

/-- The residual after all elementary exact-three-root cases are removed. -/
def TaoPrimeKummerIsotypicFrobeniusSystemThreeAllActiveNondivisibleOrFourRootsOrMore :
    Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      ((P.roots.toFinset.card = 3 ∧
          primeActiveRoots p χ P = P.roots.toFinset ∧
          ¬orderOf χ ∣ P.natDegree) ∨
        4 ≤ P.roots.toFinset.card) →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- The three-or-more-root source is equivalent to the genuinely
three-point all-active nondivisible case together with four or more roots. -/
theorem taoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore_iff_threeAllActiveNondivisibleOrFourRootsOrMore :
    TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore ↔
      TaoPrimeKummerIsotypicFrobeniusSystemThreeAllActiveNondivisibleOrFourRootsOrMore := by
  constructor
  · intro hfull p _ _ χ P hχ hP hpower hcases
    apply hfull p χ P hχ hP hpower
    rcases hcases with ⟨hcard, _⟩ | hfour
    · omega
    · omega
  · intro hres p _ _ χ P hχ hP hpower hthree
    by_cases hcard : P.roots.toFinset.card = 3
    · by_cases hactive : primeActiveRoots p χ P = P.roots.toFinset
      · by_cases hdegree : orderOf χ ∣ P.natDegree
        · exact
            exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_allActive_degree_dvd
              p χ P hP hcard hactive hdegree
        · exact hres p χ P hχ hP hpower
            (Or.inl ⟨hcard, hactive, hdegree⟩)
      · exact
          exists_primeKummerIsotypicFrobeniusSystem_of_threeRoots_not_allActive
            p χ P hP hpower hcard hactive
    · exact hres p χ P hχ hP hpower (Or.inr (by omega))

end

end Tao2026
