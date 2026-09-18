import Tao2026.BurgessWeilPrimeKummerNormLift

/-!
# Two-root Kummer traces over finite extensions

The remaining elementary all-extension case is governed by the
Hasse--Davenport lifting identity for Jacobi sums.  This file rewrites a
two-root polynomial correlation over an arbitrary finite field as one Jacobi
sum, and specializes the identity to the norm-lifted Kummer correlations.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The affine two-root change of variables is valid over every finite
field, not only a prime field. -/
theorem finiteFieldTwoRootCharacterSum_eq_jacobiSum
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (a b : F) (hab : a ≠ b)
    (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    (∑ x : F, χ (x - a) ^ m * χ (x - b) ^ n) =
      (χ ^ m) (b - a) * (χ ^ n) (a - b) *
        jacobiSum (χ ^ m) (χ ^ n) := by
  let d : F := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  let e : F ≃ F :=
    (Equiv.mulLeft₀ d hd).trans (Equiv.addRight a)
  calc
    (∑ x : F, χ (x - a) ^ m * χ (x - b) ^ n) =
        ∑ x : F, (χ ^ m) (x - a) * (χ ^ n) (x - b) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [MulChar.pow_apply' χ hm, MulChar.pow_apply' χ hn]
    _ = ∑ y : F, (χ ^ m) (e y - a) * (χ ^ n) (e y - b) :=
      (Equiv.sum_comp e
        (fun x : F => (χ ^ m) (x - a) * (χ ^ n) (x - b))).symm
    _ = (χ ^ m) d * (χ ^ n) (-d) *
        jacobiSum (χ ^ m) (χ ^ n) := by
      unfold jacobiSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      have hleft : e y - a = d * y := by
        simp [e]
      have hright : e y - b = (-d) * (1 - y) := by
        dsimp [e, d]
        ring
      rw [hleft, hright, map_mul, map_mul]
      ring
    _ = _ := by simp [d, neg_sub]

/-- Exact two-root factorization after base change to an arbitrary extension
field. -/
theorem eval_map_eq_twoRootProduct
    {K L : Type*} [Field K] [DecidableEq K] [Field L] [Algebra K L]
    (P : Polynomial K) (a b : K) (hab : a ≠ b) (hP : P.Splits)
    (hroots : P.roots.toFinset = {a, b}) (x : L) :
    (P.map (algebraMap K L)).eval x =
      algebraMap K L P.leadingCoeff *
        (x - algebraMap K L a) ^ P.rootMultiplicity a *
          (x - algebraMap K L b) ^ P.rootMultiplicity b := by
  classical
  have hall : ∀ c ∈ P.roots, c = a ∨ c = b := by
    intro c hc
    have hc' : c ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr hc
    rw [hroots] at hc'
    simpa [eq_comm] using hc'
  have hrootMultiset :
      P.roots =
        Multiset.replicate (P.roots.count a) a +
          Multiset.replicate (P.roots.count b) b := by
    ext c
    by_cases hca : c = a
    · subst c
      rw [Multiset.count_add, Multiset.count_replicate_self,
        Multiset.count_replicate]
      simp [Ne.symm hab]
    by_cases hcb : c = b
    · subst c
      rw [Multiset.count_add, Multiset.count_replicate,
        Multiset.count_replicate_self]
      simp [hab]
    have hcnot : c ∉ P.roots := by
      intro hc
      rcases hall c hc with rfl | rfl <;> contradiction
    rw [Multiset.count_eq_zero.mpr hcnot]
    rw [Multiset.count_add, Multiset.count_replicate,
      Multiset.count_replicate]
    simp [Ne.symm hca, Ne.symm hcb]
  have hcountA : P.roots.count a = P.rootMultiplicity a :=
    Polynomial.count_roots P
  have hcountB : P.roots.count b = P.rootMultiplicity b :=
    Polynomial.count_roots P
  conv_lhs => rw [Polynomial.eval_map, hP.eq_prod_roots]
  conv_lhs => rw [hrootMultiset]
  simp [hcountA, hcountB, mul_assoc]

/-- Exact two-root formula for every higher norm-lifted Kummer correlation. -/
theorem primeKummerExtensionCorrelation_succ_eq_twoRootJacobiSum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b) (hP : P.Splits)
    (hroots : P.roots.toFinset = {a, b}) (k : ℕ) :
    primeKummerExtensionCorrelation p χ P (k + 1) = by
      let E := FiniteField.Extension (ZMod p) p (k + 2)
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      let A : E := algebraMap (ZMod p) E a
      let B : E := algebraMap (ZMod p) E b
      let m := P.rootMultiplicity a
      let n := P.rootMultiplicity b
      exact χE (algebraMap (ZMod p) E P.leadingCoeff) *
        ((χE ^ m) (B - A) * (χE ^ n) (A - B) *
          jacobiSum (χE ^ m) (χE ^ n)) := by
  rw [primeKummerExtensionCorrelation_succ_eq_normLift]
  let E := FiniteField.Extension (ZMod p) p (k + 2)
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let A : E := algebraMap (ZMod p) E a
  let B : E := algebraMap (ZMod p) E b
  let m := P.rootMultiplicity a
  let n := P.rootMultiplicity b
  have hAB : A ≠ B := by
    exact (algebraMap (ZMod p) E).injective.ne hab
  have haMem : a ∈ P.roots.toFinset := by simp [hroots]
  have hbMem : b ∈ P.roots.toFinset := by simp [hroots]
  have hm : m ≠ 0 := by
    dsimp [m]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haMem)).ne'
  have hn : n ≠ 0 := by
    dsimp [n]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hbMem)).ne'
  calc
    (∑ x : E, χE ((P.map (algebraMap (ZMod p) E)).eval x)) =
        χE (algebraMap (ZMod p) E P.leadingCoeff) *
          ∑ x : E, χE (x - A) ^ m * χE (x - B) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [eval_map_eq_twoRootProduct P a b hab hP hroots x,
        map_mul, map_mul, map_pow, map_pow]
      ring
    _ = _ := by
      rw [finiteFieldTwoRootCharacterSum_eq_jacobiSum χE A B hAB m n hm hn]

/-- Norm lifting evaluated on a base-field scalar is the corresponding
degree power of the original character value. -/
theorem finiteFieldNormLiftMulChar_algebraMap_extension
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (c : ZMod p) : by
      let E := FiniteField.Extension (ZMod p) p d
      exact finiteFieldNormLiftMulChar (ZMod p) E χ
        (algebraMap (ZMod p) E c) = χ c ^ d := by
  let E := FiniteField.Extension (ZMod p) p d
  dsimp only
  rw [finiteFieldNormLiftMulChar_apply, Algebra.norm_algebraMap]
  rw [show Module.finrank (ZMod p)
      (FiniteField.Extension (ZMod p) p d) = d by
    simpa using FiniteField.finrank_zmod_extension (ZMod p) p d]
  rw [map_pow]

/-- Base-field version of the exact two-root Jacobi formula. -/
theorem primePolynomialCharacterCorrelation_eq_twoRootJacobiSum
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b) (hP : P.Splits)
    (hroots : P.roots.toFinset = {a, b}) :
    primePolynomialCharacterCorrelation p χ P =
      χ P.leadingCoeff *
        ((χ ^ P.rootMultiplicity a) (b - a) *
          (χ ^ P.rootMultiplicity b) (a - b) *
            jacobiSum (χ ^ P.rootMultiplicity a)
              (χ ^ P.rootMultiplicity b)) := by
  let m := P.rootMultiplicity a
  let n := P.rootMultiplicity b
  have haMem : a ∈ P.roots.toFinset := by simp [hroots]
  have hbMem : b ∈ P.roots.toFinset := by simp [hroots]
  have hm : m ≠ 0 := by
    dsimp [m]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haMem)).ne'
  have hn : n ≠ 0 := by
    dsimp [n]
    rw [← Polynomial.count_roots P]
    exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hbMem)).ne'
  unfold primePolynomialCharacterCorrelation
  calc
    (∑ x : ZMod p, χ (P.eval x)) =
        χ P.leadingCoeff *
          ∑ x : ZMod p, χ (x - a) ^ m * χ (x - b) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [show P.eval x =
          P.leadingCoeff * (x - a) ^ P.rootMultiplicity a *
            (x - b) ^ P.rootMultiplicity b by
        simpa using
          (eval_map_eq_twoRootProduct P a b hab hP hroots x)]
      simp only [map_mul, map_pow]
      ring
    _ = _ := by
      rw [finiteFieldTwoRootCharacterSum_eq_jacobiSum χ a b hab m n hm hn]

/-- The literal Jacobi-sum Hasse--Davenport theorem needed by the two-root
Kummer power traces. -/
def TaoPrimeFieldJacobiHasseDavenport : Prop :=
  ∀ (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ φ : MulChar (ZMod p) ℂ), χ ≠ 1 →
    let E := FiniteField.Extension (ZMod p) p d
    letI : Fintype E := Fintype.ofFinite E
    jacobiSum (finiteFieldNormLiftMulChar (ZMod p) E χ)
        (finiteFieldNormLiftMulChar (ZMod p) E φ) =
      (-1 : ℂ) ^ (d - 1) * jacobiSum χ φ ^ d

/-- Hasse--Davenport turns every two-root extension correlation into the
power trace of the negative base correlation. -/
theorem primeKummerExtensionCorrelation_eq_neg_neg_base_pow_of_twoRoots
    (hHD : TaoPrimeFieldJacobiHasseDavenport)
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b) (hP : P.Splits)
    (hroots : P.roots.toFinset = {a, b})
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a) :
    ∀ q : ℕ, primeKummerExtensionCorrelation p χ P q =
      -(-primePolynomialCharacterCorrelation p χ P) ^ (q + 1)
  | 0 => by simp
  | k + 1 => by
      let d := k + 2
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      let A : E := algebraMap (ZMod p) E a
      let B : E := algebraMap (ZMod p) E b
      let m := P.rootMultiplicity a
      let n := P.rootMultiplicity b
      have hm : m ≠ 0 := by
        intro hm0
        apply hnot
        rw [show P.rootMultiplicity a = 0 from hm0]
        exact dvd_zero _
      have hχm : χ ^ m ≠ 1 := by
        intro hpow
        exact hnot (orderOf_dvd_iff_pow_eq_one.mpr hpow)
      have hpowLiftM :
          χE ^ m = finiteFieldNormLiftMulChar (ZMod p) E (χ ^ m) := by
        exact (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ m).symm
      have hpowLiftN :
          χE ^ n = finiteFieldNormLiftMulChar (ZMod p) E (χ ^ n) := by
        exact (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ n).symm
      have hHD' := hHD p d (χ ^ m) (χ ^ n) hχm
      have hlead := finiteFieldNormLiftMulChar_algebraMap_extension
        p d χ P.leadingCoeff
      have hba := finiteFieldNormLiftMulChar_algebraMap_extension
        p d (χ ^ m) (b - a)
      have hab' := finiteFieldNormLiftMulChar_algebraMap_extension
        p d (χ ^ n) (a - b)
      rw [primeKummerExtensionCorrelation_succ_eq_twoRootJacobiSum
        p χ P a b hab hP hroots k]
      rw [primePolynomialCharacterCorrelation_eq_twoRootJacobiSum
        p χ P a b hab hP hroots]
      rw [show k + 1 + 1 = d by omega]
      change χE (algebraMap (ZMod p) E P.leadingCoeff) *
        ((χE ^ m) (B - A) *
          (χE ^ n) (A - B) *
            jacobiSum (χE ^ m) (χE ^ n)) = _
      dsimp [A, B]
      rw [← map_sub, ← map_sub]
      rw [hlead, hpowLiftM, hpowLiftN, hba, hab', hHD']
      have hsign : (-1 : ℂ) ^ (d - 1) = -((-1 : ℂ) ^ d) := by
        simp [d, pow_succ]
      rw [hsign, neg_pow]
      ring

/-- The literal Jacobi Hasse--Davenport theorem constructs the exact
two-root all-extension Frobenius residual. -/
theorem TaoPrimeFieldJacobiHasseDavenport.toTwoRoots
    (hHD : TaoPrimeFieldJacobiHasseDavenport) :
    TaoPrimeKummerIsotypicFrobeniusSystemTwoRoots := by
  intro p _ _ χ P _hχ hP hpower hcard
  have hP0 : P ≠ 0 := by
    intro hzero
    subst P
    exact hpower (isMulCharOrderScalarPower_zero χ)
  obtain ⟨a, ha, hactive⟩ :=
    (not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
      χ P hP0 hP).mp hpower
  obtain ⟨u, v, huv, hroots⟩ := Finset.card_eq_two.mp hcard
  have haCases : a = u ∨ a = v := by
    rw [hroots] at ha
    simpa using ha
  have hsharp :
      ‖primePolynomialCharacterCorrelation p χ P‖ ≤ Real.sqrt p := by
    rw [primePolynomialCharacterCorrelation_eq_kummerRootCorrelation χ P hP]
    simpa [hcard] using
      (primeKummerRootCorrelation_le_of_card_roots_le_two
        p χ P hP
          ((not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
            χ P hP0 hP).mp hpower) (by omega))
  have build (r s : ZMod p) (hrs : r ≠ s)
      (hset : P.roots.toFinset = {r, s})
      (hact : ¬orderOf χ ∣ P.rootMultiplicity r) :
      Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
    refine ⟨{
      rank := 1
      eigenvalue := fun _ => -primePolynomialCharacterCorrelation p χ P
      rank_le := by simp [hcard]
      integral := fun _ =>
        (isIntegral_primePolynomialCharacterCorrelation p χ P).neg
      weight_le := by
        intro _
        simpa using hsharp
      trace_eq := by simp
      extensionTrace_eq := fun q => by
        rw [primeKummerExtensionCorrelation_eq_neg_neg_base_pow_of_twoRoots
          hHD p χ P r s hrs hP hset hact q]
        simp }⟩
  rcases haCases with hau | hav
  · subst a
    exact build u v huv hroots hactive
  · subst a
    exact build v u (Ne.symm huv) (by simpa [pair_comm] using hroots) hactive

end

end Tao2026
