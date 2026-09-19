import Tao2026.BurgessWeilPrimeKummerThreeRootInactiveFrobenius

/-!
# Kummer Frobenius systems with at most two active roots

Inactive roots contribute only deleted affine points.  This file develops the
all-extension version of the active-root reduction, with the goal of removing
every polynomial having at most two active roots from the geometric source.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- The base-field value deleted at an inactive root after all inactive local
characters are removed. -/
def primeActiveDeletedTerm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) : ℂ :=
  χ P.leadingCoeff *
    ∏ a ∈ primeActiveRoots p χ P,
      (χ ^ P.rootMultiplicity a) (c - a)

/-- The corresponding deleted value on a finite extension. -/
def primeHigherActiveDeletedTerm
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) : ℂ := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  exact χE (algebraMap (ZMod p) E P.leadingCoeff) *
    ∏ a ∈ primeActiveRoots p χ P,
      (χE ^ P.rootMultiplicity a)
      (algebraMap (ZMod p) E c - algebraMap (ZMod p) E a)

/-- Root factorization of a split polynomial after arbitrary base change. -/
theorem eval_map_eq_rootProduct
    {K L : Type*} [Field K] [DecidableEq K] [Field L] [Algebra K L]
    (P : Polynomial K) (hP : P.Splits) (x : L) :
    (P.map (algebraMap K L)).eval x =
      algebraMap K L P.leadingCoeff *
        ∏ a ∈ P.roots.toFinset,
          (x - algebraMap K L a) ^ P.rootMultiplicity a := by
  classical
  conv_lhs => rw [Polynomial.eval_map, hP.eq_prod_roots]
  rw [eval₂_mul, eval₂_C]
  rw [Finset.prod_multiset_map_count]
  congr 1
  simp only [Polynomial.count_roots]
  change (eval₂RingHom (algebraMap K L) x)
      (∏ a ∈ P.roots.toFinset,
        (X - C a) ^ P.rootMultiplicity a) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a ha
  simp

/-- Every deleted inactive-root value lifts by an ordinary degree power. -/
theorem primeHigherActiveDeletedTerm_eq_pow
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) :
    primeHigherActiveDeletedTerm p d χ P c =
      primeActiveDeletedTerm p χ P c ^ d := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  have hpow (a : ZMod p) :
      χE ^ P.rootMultiplicity a =
        finiteFieldNormLiftMulChar (ZMod p) E
          (χ ^ P.rootMultiplicity a) :=
    (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ
      (P.rootMultiplicity a)).symm
  have hlift (η : MulChar (ZMod p) ℂ) (z : ZMod p) :
      finiteFieldNormLiftMulChar (ZMod p) E η
          (algebraMap (ZMod p) E z) = η z ^ d :=
    finiteFieldNormLiftMulChar_algebraMap_extension p d η z
  simp only [primeHigherActiveDeletedTerm, primeActiveDeletedTerm]
  change χE (algebraMap (ZMod p) E P.leadingCoeff) *
      (∏ a ∈ primeActiveRoots p χ P,
        (χE ^ P.rootMultiplicity a)
          (algebraMap (ZMod p) E c - algebraMap (ZMod p) E a)) = _
  rw [hlift χ P.leadingCoeff, mul_pow, ← Finset.prod_pow]
  congr 1
  apply Finset.prod_congr rfl
  intro a ha
  rw [hpow, ← map_sub, hlift]

/-- The unrestricted active-root character sum on the degree-`d` extension,
including the lifted leading coefficient. -/
def primeHigherActiveRootCharacterSum
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) : ℂ := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  exact χE (algebraMap (ZMod p) E P.leadingCoeff) *
    ∑ x : E, ∏ a ∈ primeActiveRoots p χ P,
      (χE ^ P.rootMultiplicity a)
        (x - algebraMap (ZMod p) E a)

/-- On every positive extension, the full Kummer correlation is the
unrestricted active-root sum minus one lifted value for each inactive root. -/
theorem primeKummerExtensionCorrelation_succ_eq_activeSum_sub_inactive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (q : ℕ) :
    primeKummerExtensionCorrelation p χ P (q + 1) = by
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      exact primeHigherActiveRootCharacterSum p d χ P -
        ∑ c ∈ primeInactiveRoots p χ P,
          primeHigherActiveDeletedTerm p d χ P c := by
  classical
  rw [primeKummerExtensionCorrelation_succ_eq_normLift]
  let d := q + 2
  letI : NeZero d := ⟨by omega⟩
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let φ : ZMod p →+* E := algebraMap (ZMod p) E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let A := primeActiveRoots p χ P
  let I := primeInactiveRoots p χ P
  let IE : Finset E := I.image φ
  let f : E → ℂ := fun x =>
    ∏ a ∈ A, (χE ^ P.rootMultiplicity a) (x - φ a)
  let g : E → ℂ := fun x =>
    ∏ a ∈ P.roots.toFinset,
      (χE ^ P.rootMultiplicity a) (x - φ a)
  have hpow (a : ZMod p) :
      χE ^ P.rootMultiplicity a =
        finiteFieldNormLiftMulChar (ZMod p) E
          (χ ^ P.rootMultiplicity a) :=
    (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ
      (P.rootMultiplicity a)).symm
  have hzero (x : E) (hx : x ∈ IE) : g x = 0 := by
    obtain ⟨c, hcI, rfl⟩ := Finset.mem_image.mp hx
    have hcRoot : c ∈ P.roots.toFinset :=
      primeInactiveRoots_subset_roots p χ P hcI
    apply Finset.prod_eq_zero hcRoot
    rw [sub_self, MulChar.map_zero]
  have hactive (x : E) (hx : x ∉ IE) : g x = f x := by
    symm
    apply Finset.prod_subset (primeActiveRoots_subset_roots p χ P)
    intro a haRoot haNotActive
    have haDvd : orderOf χ ∣ P.rootMultiplicity a := by
      rw [← Polynomial.count_roots P]
      by_contra hnot
      exact haNotActive (Finset.mem_filter.mpr ⟨haRoot, hnot⟩)
    have haI : a ∈ I := by
      exact Finset.mem_filter.mpr ⟨haRoot,
        (Polynomial.count_roots P).symm ▸ haDvd⟩
    have hxa : x - φ a ≠ 0 := by
      rw [sub_ne_zero]
      intro heq
      apply hx
      exact Finset.mem_image.mpr ⟨a, haI, heq.symm⟩
    rw [hpow, orderOf_dvd_iff_pow_eq_one.mp haDvd,
      map_one (finiteFieldNormLiftMulChar (ZMod p) E)]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hxa)
  have hsumRootActive :
      (∑ x : E, g x) =
        ∑ x ∈ (Finset.univ.filter fun x : E => x ∉ IE), f x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxIE : x ∈ IE
    · rw [if_neg (not_not.mpr hxIE), hzero x hxIE]
    · rw [if_pos hxIE, hactive x hxIE]
  have hsplit :
      (∑ x ∈ IE, f x) +
          (∑ x ∈ (Finset.univ.filter fun x : E => x ∉ IE), f x) =
        ∑ x : E, f x := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun x : E => x ∈ IE) f
    rw [show Finset.univ.filter (fun x : E => x ∈ IE) = IE by
      ext x
      simp] at h
    exact h
  have himage : (∑ x ∈ IE, f x) = ∑ c ∈ I, f (φ c) := by
    dsimp only [IE]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact φ.injective hab
  calc
    (∑ x : E, χE ((P.map φ).eval x)) =
        χE (φ P.leadingCoeff) * ∑ x : E, g x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [eval_map_eq_rootProduct P hP x, map_mul, map_prod]
      congr 1
      apply Finset.prod_congr rfl
      intro a ha
      have hmult : P.rootMultiplicity a ≠ 0 := by
        rw [← Polynomial.count_roots P]
        exact (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp ha)).ne'
      rw [map_pow, MulChar.pow_apply' χE hmult]
    _ = χE (φ P.leadingCoeff) * ∑ x : E, f x -
        ∑ c ∈ I, χE (φ P.leadingCoeff) * f (φ c) := by
      rw [hsumRootActive, ← Finset.mul_sum, ← himage]
      linear_combination χE (φ P.leadingCoeff) * hsplit
    _ = _ := by
      simp only [primeHigherActiveRootCharacterSum,
        primeHigherActiveDeletedTerm]
      rfl

/-- The base polynomial correlation is the unrestricted active-root sum minus
the values at all inactive roots. -/
theorem primePolynomialCharacterCorrelation_eq_activeSum_sub_inactive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) :
    primePolynomialCharacterCorrelation p χ P =
      χ P.leadingCoeff *
          (∑ x : ZMod p, ∏ a ∈ primeActiveRoots p χ P,
            χ (x - a) ^ P.roots.count a) -
        ∑ c ∈ primeInactiveRoots p χ P,
          primeActiveDeletedTerm p χ P c := by
  let A := primeActiveRoots p χ P
  let I := primeInactiveRoots p χ P
  let f : ZMod p → ℂ := fun x =>
    ∏ a ∈ A, χ (x - a) ^ P.roots.count a
  have hsplit :
      (∑ x ∈ I, f x) +
          (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) =
        ∑ x : ZMod p, f x := by
    simpa [I] using
      (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x : ZMod p => x ∈ I) f)
  rw [primePolynomialCharacterCorrelation_eq_rootProduct p χ P hP,
    sum_primeRootProduct_eq_filter_primeActiveRootProduct p χ P]
  change χ P.leadingCoeff *
      (∑ x ∈ (Finset.univ.filter fun x : ZMod p => x ∉ I), f x) = _
  have hdeleted :
      (∑ c ∈ I, primeActiveDeletedTerm p χ P c) =
        χ P.leadingCoeff * ∑ c ∈ I, f c := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    simp only [primeActiveDeletedTerm]
    congr 1
    apply Finset.prod_congr rfl
    intro a ha
    rw [← Polynomial.count_roots P,
      MulChar.pow_apply' χ (by
        exact (Multiset.count_pos.mpr
          (Multiset.mem_toFinset.mp
            (primeActiveRoots_subset_roots p χ P ha))).ne')]
  rw [hdeleted]
  linear_combination χ P.leadingCoeff * hsplit

theorem isIntegral_primeActiveDeletedTerm
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) : IsIntegral ℤ (primeActiveDeletedTerm p χ P c) := by
  unfold primeActiveDeletedTerm
  exact (isIntegral_mulChar_apply χ P.leadingCoeff).mul
    (IsIntegral.prod _ fun a _ha =>
      isIntegral_mulChar_apply (χ ^ P.rootMultiplicity a) (c - a))

theorem norm_primeActiveDeletedTerm_le_one
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (c : ZMod p) : ‖primeActiveDeletedTerm p χ P c‖ ≤ 1 := by
  simp only [primeActiveDeletedTerm, norm_mul, norm_prod]
  calc
    ‖χ P.leadingCoeff‖ *
        ∏ a ∈ primeActiveRoots p χ P,
          ‖(χ ^ P.rootMultiplicity a) (c - a)‖ ≤
      1 * ∏ _a ∈ primeActiveRoots p χ P, (1 : ℝ) := by
        gcongr
        · exact DirichletCharacter.norm_le_one _ _
        · exact DirichletCharacter.norm_le_one _ _
    _ = 1 := by simp

/-- A canonical finite index type for the elements of a finset. -/
def finEquivFinset { α : Type* } (s : Finset α) : Fin s.card ≃ s :=
  (Equiv.cast (congrArg Fin (Fintype.card_coe s).symm)).trans
    (Fintype.equivFin s).symm

theorem sum_finEquivFinset
    { α : Type* } (s : Finset α) (f : α → ℂ) :
    (∑ i : Fin s.card, f (finEquivFinset s i)) = ∑ x ∈ s, f x := by
  calc
    (∑ i : Fin s.card, f (finEquivFinset s i)) =
        ∑ x : s, f x := Equiv.sum_comp (finEquivFinset s) (fun x : s => f x)
    _ = ∑ x ∈ s, f x :=
      (Finset.sum_subtype s (fun x => by simp) f).symm

theorem card_primeActiveRoots_add_card_primeInactiveRoots
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    (primeActiveRoots p χ P).card + (primeInactiveRoots p χ P).card =
      P.roots.toFinset.card := by
  have hdisjoint :
      Disjoint (primeActiveRoots p χ P) (primeInactiveRoots p χ P) := by
    rw [Finset.disjoint_left]
    intro a haActive haInactive
    exact (Finset.mem_filter.mp haActive).2
      (Finset.mem_filter.mp haInactive).2
  rw [← primeActiveRoots_union_primeInactiveRoots p χ P,
    Finset.card_union_of_disjoint hdisjoint]

/-- With one active root, the unrestricted active sum vanishes on every
positive-degree extension. -/
theorem primeHigherActiveRootCharacterSum_eq_zero_of_single
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hactive : primeActiveRoots p χ P = {a})
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a) :
    primeHigherActiveRootCharacterSum p d χ P = 0 := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let m := P.rootMultiplicity a
  have hχm : χ ^ m ≠ 1 := by
    intro heq
    exact hnot (orderOf_dvd_iff_pow_eq_one.mpr heq)
  have hpow : χE ^ m = finiteFieldNormLiftMulChar (ZMod p) E (χ ^ m) :=
    (map_pow (finiteFieldNormLiftMulChar (ZMod p) E) χ m).symm
  have hχEm : χE ^ m ≠ 1 := by
    rw [hpow]
    exact finiteFieldNormLiftMulChar_ne_one (ZMod p) E hχm
  simp only [primeHigherActiveRootCharacterSum]
  change χE (algebraMap (ZMod p) E P.leadingCoeff) *
      (∑ x : E, ∏ b ∈ primeActiveRoots p χ P,
        (χE ^ P.rootMultiplicity b)
          (x - algebraMap (ZMod p) E b)) = 0
  rw [hactive]
  simp only [Finset.prod_singleton]
  rw [show (∑ x : E, (χE ^ m) (x - algebraMap (ZMod p) E a)) =
      ∑ x : E, (χE ^ m) x by
    exact Equiv.sum_comp (Equiv.subRight (algebraMap (ZMod p) E a))
      (fun x : E => (χE ^ m) x)]
  rw [MulChar.sum_eq_zero_of_ne_one hχEm, mul_zero]

theorem primeBaseActiveRootCharacterSum_eq_zero_of_single
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hactive : primeActiveRoots p χ P = {a})
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a) :
    χ P.leadingCoeff *
        (∑ x : ZMod p, ∏ b ∈ primeActiveRoots p χ P,
          χ (x - b) ^ P.roots.count b) = 0 := by
  have hcount : P.roots.count a ≠ 0 := by
    intro hzero
    apply hnot
    rw [← Polynomial.count_roots P, hzero]
    exact dvd_zero _
  have hpow : χ ^ P.roots.count a ≠ 1 := by
    intro heq
    exact hnot ((Polynomial.count_roots P) ▸
      orderOf_dvd_iff_pow_eq_one.mpr heq)
  rw [hactive]
  simp only [Finset.prod_singleton]
  have hconvert :
      (∑ x : ZMod p, χ (x - a) ^ P.roots.count a) =
        ∑ x : ZMod p, (χ ^ P.roots.count a) (x - a) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [MulChar.pow_apply' χ hcount]
  rw [hconvert, show
      (∑ x : ZMod p, (χ ^ P.roots.count a) (x - a)) =
        ∑ x : ZMod p, (χ ^ P.roots.count a) x by
    exact Equiv.sum_comp (Equiv.subRight a)
      (fun x : ZMod p => (χ ^ P.roots.count a) x)]
  rw [MulChar.sum_eq_zero_of_ne_one hpow, mul_zero]

/-- With one active root, every extension correlation is the negative power
sum of the deleted inactive-root values. -/
theorem primeKummerExtensionCorrelation_eq_inactivePowers_of_singleActive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hP : P.Splits)
    (hactive : primeActiveRoots p χ P = {a})
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a) :
    ∀ q : ℕ, primeKummerExtensionCorrelation p χ P q =
      -∑ c ∈ primeInactiveRoots p χ P,
        primeActiveDeletedTerm p χ P c ^ (q + 1)
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primePolynomialCharacterCorrelation_eq_activeSum_sub_inactive
          p χ P hP,
        primeBaseActiveRootCharacterSum_eq_zero_of_single
          p χ P a hactive hnot]
      simp
  | q + 1 => by
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      rw [primeKummerExtensionCorrelation_succ_eq_activeSum_sub_inactive
        p χ P hP q]
      change primeHigherActiveRootCharacterSum p d χ P -
          (∑ c ∈ primeInactiveRoots p χ P,
            primeHigherActiveDeletedTerm p d χ P c) = _
      rw [primeHigherActiveRootCharacterSum_eq_zero_of_single
        p d χ P a hactive hnot]
      simp only [zero_sub, neg_inj]
      apply Finset.sum_congr rfl
      intro c hc
      rw [primeHigherActiveDeletedTerm_eq_pow]

def primeSingleActiveEigenvalue
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    Fin (primeInactiveRoots p χ P).card → ℂ := fun i =>
  primeActiveDeletedTerm p χ P
    (finEquivFinset (primeInactiveRoots p χ P) i)

@[simp]
theorem sum_primeSingleActiveEigenvalue_pow
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) (d : ℕ) :
    (∑ i, primeSingleActiveEigenvalue p χ P i ^ d) =
      ∑ c ∈ primeInactiveRoots p χ P,
        primeActiveDeletedTerm p χ P c ^ d := by
  exact sum_finEquivFinset (primeInactiveRoots p χ P)
    (fun c => primeActiveDeletedTerm p χ P c ^ d)

/-- The exact one-active-root all-extension Frobenius system. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_singleActiveRoot
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hP : P.Splits)
    (hactive : primeActiveRoots p χ P = {a})
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hcard := card_primeActiveRoots_add_card_primeInactiveRoots p χ P
  have hactiveCard : (primeActiveRoots p χ P).card = 1 := by simp [hactive]
  refine ⟨{
    rank := (primeInactiveRoots p χ P).card
    eigenvalue := primeSingleActiveEigenvalue p χ P
    rank_le := by omega
    integral := by
      intro i
      exact isIntegral_primeActiveDeletedTerm p χ P _
    weight_le := by
      intro i
      exact (norm_primeActiveDeletedTerm_le_one p χ P _).trans hsqrt
    trace_eq := by
      have hcorr :=
        primeKummerExtensionCorrelation_eq_inactivePowers_of_singleActive
          p χ P a hP hactive hnot 0
      rw [primeKummerExtensionCorrelation_zero] at hcorr
      have hsum := sum_primeSingleActiveEigenvalue_pow p χ P 1
      simp only [pow_one] at hsum
      rw [hsum]
      simpa using hcorr
    extensionTrace_eq := fun q => by
      rw [sum_primeSingleActiveEigenvalue_pow]
      exact primeKummerExtensionCorrelation_eq_inactivePowers_of_singleActive
        p χ P a hP hactive hnot q }⟩

/-- With two active roots, the unrestricted extension sum is the lifted
two-root Jacobi main term. -/
theorem primeHigherActiveRootCharacterSum_eq_twoRootJacobiData
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b)
    (hactive : primeActiveRoots p χ P = {a, b}) : by
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
      exact primeHigherActiveRootCharacterSum p d χ P =
        finiteFieldThreeRootInactiveJacobiMainData χE
          (algebraMap (ZMod p) E P.leadingCoeff)
          (algebraMap (ZMod p) E a) (algebraMap (ZMod p) E b)
          (P.rootMultiplicity a) (P.rootMultiplicity b) := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let A : E := algebraMap (ZMod p) E a
  let B : E := algebraMap (ZMod p) E b
  let m := P.rootMultiplicity a
  let n := P.rootMultiplicity b
  have hAB : A ≠ B := (algebraMap (ZMod p) E).injective.ne hab
  simp only [primeHigherActiveRootCharacterSum]
  change χE (algebraMap (ZMod p) E P.leadingCoeff) *
      (∑ x : E, ∏ c ∈ primeActiveRoots p χ P,
        (χE ^ P.rootMultiplicity c)
          (x - algebraMap (ZMod p) E c)) = _
  rw [hactive]
  simp only [Finset.prod_insert, Finset.mem_singleton, hab, not_false_eq_true,
    Finset.prod_singleton]
  rw [finiteFieldTwoMulCharSum_eq_jacobiSum
    (χE ^ m) (χE ^ n) A B hAB]
  rfl

/-- Hasse--Davenport evaluates the two-active-root unrestricted sum in every
extension degree. -/
theorem primeHigherActiveRootCharacterSum_eq_signedPow_of_two
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b)
    (hactive : primeActiveRoots p χ P = {a, b})
    (hχa : χ ^ P.rootMultiplicity a ≠ 1) :
    primeHigherActiveRootCharacterSum p d χ P =
      (-1 : ℂ) ^ (d - 1) *
        primeThreeRootInactiveJacobiMain p χ P a b ^ d := by
  rw [primeHigherActiveRootCharacterSum_eq_twoRootJacobiData
    p d χ P a b hab hactive]
  rw [finiteFieldNormLift_threeRootInactiveJacobiMainData
    p d χ P.leadingCoeff a b (P.rootMultiplicity a)
      (P.rootMultiplicity b) hχa]
  rfl

theorem primeBaseActiveRootCharacterSum_eq_twoRootJacobiMain
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b)
    (hactive : primeActiveRoots p χ P = {a, b}) :
    χ P.leadingCoeff *
        (∑ x : ZMod p, ∏ c ∈ primeActiveRoots p χ P,
          χ (x - c) ^ P.roots.count c) =
      primeThreeRootInactiveJacobiMain p χ P a b := by
  have haActive : a ∈ primeActiveRoots p χ P := by simp [hactive]
  have hbActive : b ∈ primeActiveRoots p χ P := by simp [hactive]
  have haRoot := primeActiveRoots_subset_roots p χ P haActive
  have hbRoot := primeActiveRoots_subset_roots p χ P hbActive
  have hm : P.roots.count a ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp haRoot)).ne'
  have hn : P.roots.count b ≠ 0 :=
    (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hbRoot)).ne'
  rw [hactive]
  simp only [Finset.prod_insert, Finset.mem_singleton, hab, not_false_eq_true,
    Finset.prod_singleton]
  have hconvert :
      (∑ x : ZMod p,
        χ (x - a) ^ P.roots.count a * χ (x - b) ^ P.roots.count b) =
      ∑ x : ZMod p,
        (χ ^ P.rootMultiplicity a) (x - a) *
          (χ ^ P.rootMultiplicity b) (x - b) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← MulChar.pow_apply' χ hm, ← MulChar.pow_apply' χ hn,
      Polynomial.count_roots P, Polynomial.count_roots P]
  rw [hconvert, finiteFieldTwoMulCharSum_eq_jacobiSum
    (χ ^ P.rootMultiplicity a) (χ ^ P.rootMultiplicity b) a b hab]
  rfl

/-- With two active roots, every full correlation is the power sum of one
signed Jacobi eigenvalue and all inactive-root deleted values. -/
theorem primeKummerExtensionCorrelation_eq_inactivePowers_of_twoActive
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b) (hP : P.Splits)
    (hactive : primeActiveRoots p χ P = {a, b})
    (hχa : χ ^ P.rootMultiplicity a ≠ 1) :
    ∀ q : ℕ, primeKummerExtensionCorrelation p χ P q =
      -((-primeThreeRootInactiveJacobiMain p χ P a b) ^ (q + 1) +
        ∑ c ∈ primeInactiveRoots p χ P,
          primeActiveDeletedTerm p χ P c ^ (q + 1))
  | 0 => by
      rw [primeKummerExtensionCorrelation_zero,
        primePolynomialCharacterCorrelation_eq_activeSum_sub_inactive
          p χ P hP,
        primeBaseActiveRootCharacterSum_eq_twoRootJacobiMain
          p χ P a b hab hactive]
      ring_nf
  | q + 1 => by
      let d := q + 2
      letI : NeZero d := ⟨by omega⟩
      rw [primeKummerExtensionCorrelation_succ_eq_activeSum_sub_inactive
        p χ P hP q]
      change primeHigherActiveRootCharacterSum p d χ P -
          (∑ c ∈ primeInactiveRoots p χ P,
            primeHigherActiveDeletedTerm p d χ P c) = _
      rw [primeHigherActiveRootCharacterSum_eq_signedPow_of_two
        p d χ P a b hab hactive hχa]
      have hdeleted :
          (∑ c ∈ primeInactiveRoots p χ P,
            primeHigherActiveDeletedTerm p d χ P c) =
          ∑ c ∈ primeInactiveRoots p χ P,
            primeActiveDeletedTerm p χ P c ^ d := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [primeHigherActiveDeletedTerm_eq_pow]
      rw [hdeleted]
      rw [show q + 1 + 1 = d by omega]
      have hsign : (-1 : ℂ) ^ (d - 1) = -((-1 : ℂ) ^ d) := by
        simp [d, pow_succ]
      rw [hsign, neg_pow]
      ring

def primeTwoActiveEigenvalue
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) : Fin ((primeInactiveRoots p χ P).card + 1) → ℂ :=
  Fin.cases (-primeThreeRootInactiveJacobiMain p χ P a b)
    (fun i => primeSingleActiveEigenvalue p χ P i)

@[simp]
theorem sum_primeTwoActiveEigenvalue_pow
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (d : ℕ) :
    (∑ i, primeTwoActiveEigenvalue p χ P a b i ^ d) =
      (-primeThreeRootInactiveJacobiMain p χ P a b) ^ d +
        ∑ c ∈ primeInactiveRoots p χ P,
          primeActiveDeletedTerm p χ P c ^ d := by
  rw [Fin.sum_univ_succ]
  simp only [primeTwoActiveEigenvalue, Fin.cases_zero, Fin.cases_succ,
    sum_primeSingleActiveEigenvalue_pow]

/-- The exact two-active-root all-extension Frobenius system, allowing any
number of inactive roots. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_twoActiveRoots
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a b : ZMod p) (hab : a ≠ b) (hP : P.Splits)
    (hactive : primeActiveRoots p χ P = {a, b})
    (hχa : χ ^ P.rootMultiplicity a ≠ 1) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    rw [Real.one_le_sqrt]
    exact_mod_cast (Fact.out : p.Prime).one_le
  have hcard := card_primeActiveRoots_add_card_primeInactiveRoots p χ P
  have hactiveCard : (primeActiveRoots p χ P).card = 2 := by
    simp [hactive, hab]
  refine ⟨{
    rank := (primeInactiveRoots p χ P).card + 1
    eigenvalue := primeTwoActiveEigenvalue p χ P a b
    rank_le := by omega
    integral := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact (isIntegral_primeThreeRootInactiveJacobiMain p χ P a b).neg
      · exact isIntegral_primeActiveDeletedTerm p χ P _
    weight_le := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [primeTwoActiveEigenvalue] using
          norm_primeThreeRootInactiveJacobiMain_le_sqrt p χ P a b hχa
      · exact (norm_primeActiveDeletedTerm_le_one p χ P _).trans hsqrt
    trace_eq := by
      have hcorr := primeKummerExtensionCorrelation_eq_inactivePowers_of_twoActive
        p χ P a b hab hP hactive hχa 0
      rw [primeKummerExtensionCorrelation_zero] at hcorr
      have hsum := sum_primeTwoActiveEigenvalue_pow p χ P a b 1
      simp only [pow_one] at hsum
      rw [hsum]
      simpa using hcorr
    extensionTrace_eq := fun q => by
      rw [sum_primeTwoActiveEigenvalue_pow]
      exact primeKummerExtensionCorrelation_eq_inactivePowers_of_twoActive
        p χ P a b hab hP hactive hχa q }⟩

/-- Every split non-scalar-power polynomial with at most two active roots has
an unconditional all-extension Frobenius system, regardless of how many
inactive roots it has. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_card_activeRoots_le_two
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (hP : P.Splits) (hpower : ¬IsMulCharOrderScalarPower χ P)
    (hcard : (primeActiveRoots p χ P).card ≤ 2) :
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
  have hcardPos : 0 < (primeActiveRoots p χ P).card :=
    Finset.card_pos.mpr ⟨a, haActive⟩
  have hcases : (primeActiveRoots p χ P).card = 1 ∨
      (primeActiveRoots p χ P).card = 2 := by omega
  rcases hcases with hone | htwo
  · obtain ⟨u, hactive⟩ := Finset.card_eq_one.mp hone
    have huActive : u ∈ primeActiveRoots p χ P := by simp [hactive]
    have huNotCount : ¬orderOf χ ∣ P.roots.count u :=
      (Finset.mem_filter.mp huActive).2
    have huNot : ¬orderOf χ ∣ P.rootMultiplicity u := by
      intro hdvd
      exact huNotCount ((Polynomial.count_roots P).symm ▸ hdvd)
    exact exists_primeKummerIsotypicFrobeniusSystem_of_singleActiveRoot
      p χ P u hP hactive huNot
  · obtain ⟨u, v, huv, hactive⟩ := Finset.card_eq_two.mp htwo
    have huActive : u ∈ primeActiveRoots p χ P := by simp [hactive]
    have huNotCount : ¬orderOf χ ∣ P.roots.count u :=
      (Finset.mem_filter.mp huActive).2
    have huNot : ¬orderOf χ ∣ P.rootMultiplicity u := by
      intro hdvd
      exact huNotCount ((Polynomial.count_roots P).symm ▸ hdvd)
    have hχu : χ ^ P.rootMultiplicity u ≠ 1 := by
      intro heq
      exact huNot (orderOf_dvd_iff_pow_eq_one.mpr heq)
    exact exists_primeKummerIsotypicFrobeniusSystem_of_twoActiveRoots
      p χ P u v huv hP hactive hχu

/-- The genuinely geometric Kummer source, now restricted by active-root
count rather than total distinct-root count. -/
def TaoPrimeKummerIsotypicFrobeniusSystemThreeActiveRootsOrMore : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      3 ≤ (primeActiveRoots p χ P).card →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- The original three-or-more-distinct-root source is exactly equivalent to
the smaller three-or-more-active-root source. -/
theorem taoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore_iff_threeActiveRootsOrMore :
    TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore ↔
      TaoPrimeKummerIsotypicFrobeniusSystemThreeActiveRootsOrMore := by
  constructor
  · intro hfull p _ _ χ P hχ hP hpower hactive
    apply hfull p χ P hχ hP hpower
    have hsubset := Finset.card_le_card
      (primeActiveRoots_subset_roots p χ P)
    omega
  · intro hres p _ _ χ P hχ hP hpower hroots
    by_cases hcard : (primeActiveRoots p χ P).card ≤ 2
    · exact
        exists_primeKummerIsotypicFrobeniusSystem_of_card_activeRoots_le_two
          p χ P hP hpower hcard
    · exact hres p χ P hχ hP hpower (by omega)

/-- Supplying only the three-active-root geometric system now proves the full
all-extension Kummer source theorem. -/
theorem TaoPrimeKummerIsotypicFrobeniusSystemThreeActiveRootsOrMore.toFull
    (hres : TaoPrimeKummerIsotypicFrobeniusSystemThreeActiveRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSystem :=
  taoPrimeKummerIsotypicFrobeniusSystem_of_twoRoots_and_threeRootsOrMore
    taoPrimeKummerIsotypicFrobeniusSystemTwoRoots
    (taoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore_iff_threeActiveRootsOrMore.mpr
      hres)

end

end Tao2026
