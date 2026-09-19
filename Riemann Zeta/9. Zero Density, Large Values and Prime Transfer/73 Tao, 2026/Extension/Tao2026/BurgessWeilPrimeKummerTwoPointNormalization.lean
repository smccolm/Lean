import Tao2026.BurgessWeilPrimeKummerMonicNormalization

/-!
# Two-point normalization of the reduced Kummer source

A split monic polynomial with at least three distinct roots has two distinct
roots `a` and `b`.  The affine coordinate `x ↦ a + (b - a) * x`
sends these roots to zero and one.  This file constructs the corresponding
monic polynomial directly from its root multiset and proves the exact
extension-field correlation identity.

The scalar produced by the affine change of variables is absorbed into every
Frobenius eigenvalue.  Thus the remaining Kummer source is equivalent to the
source restricted to polynomials having both zero and one as roots.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

def primeKummerTwoPointNormalization
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p) :
    Polynomial (ZMod p) :=
  (P.roots.map fun r =>
    Polynomial.X - Polynomial.C ((r - a) / (b - a))).prod

theorem primeKummerTwoPointNormalization_monic
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p) :
    (primeKummerTwoPointNormalization P a b).Monic := by
  simpa [primeKummerTwoPointNormalization, Multiset.map_map] using
    Polynomial.monic_multisetProd_X_sub_C
      (P.roots.map fun r => (r - a) / (b - a))

theorem primeKummerTwoPointNormalization_roots
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p) :
    (primeKummerTwoPointNormalization P a b).roots =
      P.roots.map fun r => (r - a) / (b - a) := by
  simpa [primeKummerTwoPointNormalization, Multiset.map_map] using
    Polynomial.roots_multiset_prod_X_sub_C
      (P.roots.map fun r => (r - a) / (b - a))

theorem primeKummerTwoPointMap_injective
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (a b : ZMod p) (hab : a ≠ b) :
    Function.Injective (fun r : ZMod p => (r - a) / (b - a)) := by
  intro r s hrs
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hsub : r - a = s - a := (div_left_inj' hba).mp hrs
  exact sub_left_injective hsub

theorem primeKummerTwoPointNormalization_roots_card
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p) (hab : a ≠ b) :
    (primeKummerTwoPointNormalization P a b).roots.toFinset.card = P.roots.toFinset.card := by
  rw [primeKummerTwoPointNormalization_roots, Multiset.toFinset_map,
    Finset.card_image_of_injective _ (primeKummerTwoPointMap_injective a b hab)]

theorem primeKummerTwoPointNormalization_rootMultiplicity
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b r : ZMod p) (hab : a ≠ b) :
    (primeKummerTwoPointNormalization P a b).rootMultiplicity ((r - a) / (b - a)) =
      P.rootMultiplicity r := by
  rw [← Polynomial.count_roots, primeKummerTwoPointNormalization_roots,
    Multiset.count_map_eq_count' _ _ (primeKummerTwoPointMap_injective a b hab),
    Polynomial.count_roots]

theorem primeKummerTwoPointNormalization_splits
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p) :
    (primeKummerTwoPointNormalization P a b).Splits := by
  apply Polynomial.Splits.multisetProd
  intro f hf
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hf
  exact Polynomial.Splits.X_sub_C _

theorem primeKummerTwoPointNormalization_zero_mem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p)
    (ha : a ∈ P.roots.toFinset) :
    0 ∈ (primeKummerTwoPointNormalization P a b).roots.toFinset := by
  rw [primeKummerTwoPointNormalization_roots]
  apply Multiset.mem_toFinset.mpr
  apply Multiset.mem_map.mpr
  refine ⟨a, Multiset.mem_toFinset.mp ha, ?_⟩
  simp

theorem primeKummerTwoPointNormalization_one_mem
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p) (hab : a ≠ b)
    (hb : b ∈ P.roots.toFinset) :
    1 ∈ (primeKummerTwoPointNormalization P a b).roots.toFinset := by
  rw [primeKummerTwoPointNormalization_roots]
  apply Multiset.mem_toFinset.mpr
  apply Multiset.mem_map.mpr
  refine ⟨b, Multiset.mem_toFinset.mp hb, ?_⟩
  simp [sub_ne_zero.mpr (Ne.symm hab)]

theorem primeKummerTwoPointNormalization_reduced
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b)
    (hreduced : IsPrimeKummerReducedExponentPolynomial χ P) :
    IsPrimeKummerReducedExponentPolynomial χ (primeKummerTwoPointNormalization P a b) := by
  intro y hy
  rw [primeKummerTwoPointNormalization_roots] at hy
  obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_toFinset.mp hy)
  rw [primeKummerTwoPointNormalization_rootMultiplicity P a b r hab]
  exact hreduced r (Multiset.mem_toFinset.mpr hr)

theorem primeKummerTwoPointNormalization_eval_map
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p)
    {L : Type*} [Field L] [Algebra (ZMod p) L] (x : L) :
    ((primeKummerTwoPointNormalization P a b).map (algebraMap (ZMod p) L)).eval x =
      (P.roots.map fun r =>
        x - algebraMap (ZMod p) L ((r - a) / (b - a))).prod := by
  simp [primeKummerTwoPointNormalization, Polynomial.map_multiset_prod,
    Polynomial.eval_multiset_prod, Multiset.map_map]

theorem primeKummerTwoPointNormalization_eval_affine
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p) (hab : a ≠ b)
    (hP : P.Splits) (hmonic : P.Monic)
    {L : Type*} [Field L] [Algebra (ZMod p) L] (x : L) :
    (P.map (algebraMap (ZMod p) L)).eval
        (algebraMap (ZMod p) L a +
          algebraMap (ZMod p) L (b - a) * x) =
      algebraMap (ZMod p) L (b - a) ^ P.natDegree *
        ((primeKummerTwoPointNormalization P a b).map
          (algebraMap (ZMod p) L)).eval x := by
  let φ := algebraMap (ZMod p) L
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hbaMap : φ (b - a) ≠ 0 := by
    simpa [φ] using (algebraMap (ZMod p) L).injective.ne hba
  have hterm (r : ZMod p) :
      φ a + φ (b - a) * x - φ r =
        φ (b - a) * (x - φ ((r - a) / (b - a))) := by
    have hdiv : φ ((r - a) / (b - a)) =
        (φ r - φ a) / (φ b - φ a) := by
      simp only [div_eq_mul_inv, map_mul, _root_.map_sub, map_inv₀]
    have hden : φ b - φ a ≠ 0 := by
      simpa only [_root_.map_sub] using hbaMap
    have hsubMap : φ (b - a) = φ b - φ a := _root_.map_sub φ b a
    rw [hdiv, hsubMap]
    field_simp [hden]
    ring
  have hPeval :
      (P.map φ).eval (φ a + φ (b - a) * x) =
        (P.roots.map fun r => φ a + φ (b - a) * x - φ r).prod := by
    rw [hP.eq_prod_roots_of_monic hmonic]
    simp [Polynomial.map_multiset_prod, Polynomial.eval_multiset_prod,
      Multiset.map_map, φ]
  rw [hPeval, primeKummerTwoPointNormalization_eval_map]
  calc
    (P.roots.map fun r => φ a + φ (b - a) * x - φ r).prod =
        (P.roots.map fun r =>
          φ (b - a) * (x - φ ((r - a) / (b - a)))).prod := by
      congr 1
      apply Multiset.map_congr rfl
      intro r hr
      exact hterm r
    _ = (P.roots.map fun _ => φ (b - a)).prod *
        (P.roots.map fun r => x - φ ((r - a) / (b - a))).prod := by
      rw [Multiset.prod_map_mul]
    _ = φ (b - a) ^ P.roots.card *
        (P.roots.map fun r => x - φ ((r - a) / (b - a))).prod := by
      simp
    _ = φ (b - a) ^ P.natDegree *
        (P.roots.map fun r => x - φ ((r - a) / (b - a))).prod := by
      rw [hP.natDegree_eq_card_roots]

theorem finiteFieldPolynomialCharacterCorrelation_twoPointNormalization
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Polynomial (ZMod p)) (a b : ZMod p) (hab : a ≠ b)
    (hP : P.Splits) (hmonic : P.Monic)
    (L : Type*) [Field L] [Fintype L] [DecidableEq L]
    [Algebra (ZMod p) L]
    (ψ : MulChar L ℂ) :
    finiteFieldPolynomialCharacterCorrelation L ψ
        (P.map (algebraMap (ZMod p) L)) =
      ψ (algebraMap (ZMod p) L (b - a)) ^ P.natDegree *
        finiteFieldPolynomialCharacterCorrelation L ψ
          ((primeKummerTwoPointNormalization P a b).map (algebraMap (ZMod p) L)) := by
  classical
  let φ := algebraMap (ZMod p) L
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hbaMap : φ (b - a) ≠ 0 := by
    simpa [φ] using (algebraMap (ZMod p) L).injective.ne hba
  let e : L ≃ L :=
    (Equiv.mulLeft₀ (φ (b - a)) hbaMap).trans (Equiv.addRight (φ a))
  unfold finiteFieldPolynomialCharacterCorrelation
  calc
    (∑ y : L, ψ ((P.map φ).eval y)) =
        ∑ x : L, ψ ((P.map φ).eval (e x)) := by
      exact (Equiv.sum_comp e (fun y : L => ψ ((P.map φ).eval y))).symm
    _ = ∑ x : L,
        ψ (φ (b - a) ^ P.natDegree *
          ((primeKummerTwoPointNormalization P a b).map φ).eval x) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 1
      rw [show e x = φ a + φ (b - a) * x by
        dsimp [e]
        ring]
      exact primeKummerTwoPointNormalization_eval_affine P a b hab hP hmonic x
    _ = ψ (φ (b - a)) ^ P.natDegree *
        ∑ x : L, ψ (((primeKummerTwoPointNormalization P a b).map φ).eval x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [map_mul, map_pow]

theorem primeKummerExtensionCorrelation_twoPointNormalization
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ)
    (P : Polynomial (ZMod p)) (a b : ZMod p) (hab : a ≠ b)
    (hP : P.Splits) (hmonic : P.Monic) :
    ∀ n : ℕ,
      primeKummerExtensionCorrelation p χ P n =
        (χ (b - a) ^ P.natDegree) ^ (n + 1) *
          primeKummerExtensionCorrelation p χ
            (primeKummerTwoPointNormalization P a b) n
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primeKummerExtensionCorrelation_zero]
      have h := finiteFieldPolynomialCharacterCorrelation_twoPointNormalization
        P a b hab hP hmonic (ZMod p) χ
      simpa [finiteFieldPolynomialCharacterCorrelation,
        primePolynomialCharacterCorrelation] using h
  | n + 1 => by
      rw [primeKummerExtensionCorrelation_succ_eq_normLift,
        primeKummerExtensionCorrelation_succ_eq_normLift]
      let d := n + 2
      letI : NeZero d := ⟨by omega⟩
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      letI : DecidableEq E := Classical.decEq E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      change finiteFieldPolynomialCharacterCorrelation E χE
          (P.map (algebraMap (ZMod p) E)) =
        (χ (b - a) ^ P.natDegree) ^ (n + 1 + 1) *
          finiteFieldPolynomialCharacterCorrelation E χE
            ((primeKummerTwoPointNormalization P a b).map (algebraMap (ZMod p) E))
      have h := finiteFieldPolynomialCharacterCorrelation_twoPointNormalization
        P a b hab hP hmonic E χE
      rw [finiteFieldNormLiftMulChar_algebraMap_extension
        p d χ (b - a)] at h
      have hpows : (χ (b - a) ^ d) ^ P.natDegree =
          (χ (b - a) ^ P.natDegree) ^ d := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      rw [hpows] at h
      simpa [d] using h

def PrimeKummerIsotypicFrobeniusSystem.twistTwoPointNormalization
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {χ : MulChar (ZMod p) ℂ} {P : Polynomial (ZMod p)}
    {a b : ZMod p}
    (s : PrimeKummerIsotypicFrobeniusSystem p χ
      (primeKummerTwoPointNormalization P a b))
    (hab : a ≠ b) (hP : P.Splits) (hmonic : P.Monic) :
    PrimeKummerIsotypicFrobeniusSystem p χ P where
  rank := s.rank
  eigenvalue i := χ (b - a) ^ P.natDegree * s.eigenvalue i
  rank_le := by
    rw [← primeKummerTwoPointNormalization_roots_card P a b hab]
    exact s.rank_le
  integral i :=
    ((isIntegral_mulChar_apply χ (b - a)).pow P.natDegree).mul
      (s.integral i)
  weight_le i := by
    rw [norm_mul, norm_pow]
    have hz : ‖χ (b - a)‖ ^ P.natDegree ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
    calc
      ‖χ (b - a)‖ ^ P.natDegree * ‖s.eigenvalue i‖ ≤
          1 * Real.sqrt p := by
        gcongr
        exact s.weight_le i
      _ = Real.sqrt p := one_mul _
  trace_eq := by
    change primeKummerExtensionCorrelation p χ P 0 =
      -∑ i : Fin s.rank,
        (χ (b - a) ^ P.natDegree) * s.eigenvalue i
    rw [primeKummerExtensionCorrelation_twoPointNormalization p χ P a b hab hP hmonic 0,
      s.extensionTrace_eq 0]
    simp only [Nat.zero_add, pow_one]
    rw [mul_neg, Finset.mul_sum]
  extensionTrace_eq n := by
    rw [primeKummerExtensionCorrelation_twoPointNormalization p χ P a b hab hP hmonic n,
      s.extensionTrace_eq n]
    simp_rw [mul_pow]
    rw [mul_neg, Finset.mul_sum]

def TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemThreeRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Monic → P.Splits →
      IsPrimeKummerReducedExponentPolynomial χ P →
      0 ∈ P.roots.toFinset → 1 ∈ P.roots.toFinset →
      3 ≤ P.roots.toFinset.card →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

theorem taoPrimeKummerMonicReducedExponentFrobeniusSystemThreeRootsOrMore_iff_twoPointNormalized :
    TaoPrimeKummerMonicReducedExponentFrobeniusSystemThreeRootsOrMore ↔
      TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemThreeRootsOrMore := by
  constructor
  · intro h p _ _ χ P hχ hmonic hP hreduced _hzero _hone hcard
    exact h p χ P hχ hmonic hP hreduced hcard
  · intro h p _ _ χ P hχ hmonic hP hreduced hcard
    have htwo : 1 < P.roots.toFinset.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
    let Q := primeKummerTwoPointNormalization P a b
    have hQmonic : Q.Monic := primeKummerTwoPointNormalization_monic P a b
    have hQsplits : Q.Splits := primeKummerTwoPointNormalization_splits P a b
    have hQreduced : IsPrimeKummerReducedExponentPolynomial χ Q :=
      primeKummerTwoPointNormalization_reduced χ P a b hab hreduced
    have hQzero : 0 ∈ Q.roots.toFinset :=
      primeKummerTwoPointNormalization_zero_mem P a b ha
    have hQone : 1 ∈ Q.roots.toFinset :=
      primeKummerTwoPointNormalization_one_mem P a b hab hb
    have hQcard : 3 ≤ Q.roots.toFinset.card := by
      rwa [primeKummerTwoPointNormalization_roots_card P a b hab]
    exact (h p χ Q hχ hQmonic hQsplits hQreduced hQzero hQone hQcard).map
      (fun s => s.twistTwoPointNormalization hab hP hmonic)

theorem TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemThreeRootsOrMore.toFull
    (h : TaoPrimeKummerTwoPointNormalizedReducedExponentFrobeniusSystemThreeRootsOrMore) : TaoPrimeKummerIsotypicFrobeniusSystem :=
  TaoPrimeKummerMonicReducedExponentFrobeniusSystemThreeRootsOrMore.toFull
    (taoPrimeKummerMonicReducedExponentFrobeniusSystemThreeRootsOrMore_iff_twoPointNormalized.mpr h)

end
end Tao2026


