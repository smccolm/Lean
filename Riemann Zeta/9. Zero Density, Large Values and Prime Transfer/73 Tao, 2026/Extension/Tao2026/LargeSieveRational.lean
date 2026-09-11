import Tao2026.LargeSieveSeparated
import Tao2026.LargeSieveTensor

/-!
# Rational circle frequencies

This file turns cyclic `ZMod` frequencies into their canonical real circle
representatives.  It proves the elementary denominator-product separation
lemma and packages cross-multiplication as the exact arithmetic input needed
by the separated-frequency large sieve.
-/

open Finset
open scoped BigOperators

namespace Tao2026

noncomputable section

/-- The canonical representative in `[0,1)` of a cyclic frequency. -/
def cyclicCircleFrequency (N : ℕ) (k : ZMod N) : ℝ :=
  (k.val : ℝ) / N

theorem standardAdditiveCharacter_cyclicCircleFrequency
    {N : ℕ} [NeZero N] (k : ZMod N) :
    standardAdditiveCharacter (cyclicCircleFrequency N k) =
      ZMod.stdAddChar k := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  unfold standardAdditiveCharacter cyclicCircleFrequency
  push_cast
  congr 1
  ring

theorem standardAdditiveCharacter_neg_nat_mul_cyclicCircleFrequency
    {N : ℕ} [NeZero N] (k : ZMod N) (n : ℕ) :
    standardAdditiveCharacter
        (-((n : ℝ) * cyclicCircleFrequency N k)) =
      ZMod.stdAddChar (-((n : ZMod N) * k)) := by
  rw [standardAdditiveCharacter_neg]
  rw [standardAdditiveCharacter_nat_mul,
    standardAdditiveCharacter_cyclicCircleFrequency]
  rw [show (n : ZMod N) * k = n • k by simp,
    AddChar.map_neg_eq_conj, AddChar.map_nsmul_eq_pow]

/-- The common-denominator numerator of a tensor frequency. -/
def tensorFrequencyNumerator :
    ∀ qs : List SieveModulus, SieveCube qs → ℕ
  | [], _ => 0
  | q :: qs, ξ => ξ.1.val * sieveModulusProduct qs +
      q.modulus * tensorFrequencyNumerator qs ξ.2

/-- Real circle frequency obtained by summing the coordinate frequencies. -/
def tensorCircleFrequency :
    ∀ qs : List SieveModulus, SieveCube qs → ℝ
  | [], _ => 0
  | q :: qs, ξ => cyclicCircleFrequency q.modulus ξ.1 +
      tensorCircleFrequency qs ξ.2

theorem tensorCircleFrequency_eq_numerator_div_product :
    ∀ (qs : List SieveModulus) (ξ : SieveCube qs),
      tensorCircleFrequency qs ξ =
        (tensorFrequencyNumerator qs ξ : ℝ) /
          sieveModulusProduct qs
  | [], ξ => by
      simp [tensorCircleFrequency, tensorFrequencyNumerator,
        sieveModulusProduct]
  | q :: qs, ξ => by
      rw [tensorCircleFrequency]
      rw [tensorCircleFrequency_eq_numerator_div_product qs ξ.2]
      rw [cyclicCircleFrequency, tensorFrequencyNumerator]
      have hq : (q.modulus : ℝ) ≠ 0 := by exact_mod_cast q.ne_zero
      have hP : (sieveModulusProduct qs : ℝ) ≠ 0 := by
        exact_mod_cast sieveModulusProduct_ne_zero qs
      have hprod : ((sieveModulusProduct (q :: qs) : ℕ) : ℝ) =
          (q.modulus : ℝ) * sieveModulusProduct qs := by
        simp [sieveModulusProduct]
      rw [hprod]
      push_cast
      field_simp

/-- The tensor character on the natural diagonal is the real character at
the summed tensor circle frequency. -/
theorem tensorDftChar_natSieveCube_eq_circle :
    ∀ (qs : List SieveModulus) (ξ : SieveCube qs) (n : ℕ),
      tensorDftChar qs ξ (natSieveCube qs n) =
        standardAdditiveCharacter
          (-((n : ℝ) * tensorCircleFrequency qs ξ))
  | [], ξ, n => by
      change (1 : ℂ) = standardAdditiveCharacter (-(n * 0))
      simp [standardAdditiveCharacter]
  | q :: qs, ξ, n => by
      rw [tensorCircleFrequency]
      simp only [tensorDftChar, natSieveCube]
      change (ZMod.stdAddChar.mulShift (-ξ.1)) (n : ZMod q.modulus) *
          tensorDftChar qs ξ.2 (natSieveCube qs n) = _
      rw [AddChar.mulShift_apply]
      rw [show -ξ.1 * (n : ZMod q.modulus) =
          -((n : ZMod q.modulus) * ξ.1) by ring]
      rw [← standardAdditiveCharacter_neg_nat_mul_cyclicCircleFrequency]
      rw [tensorDftChar_natSieveCube_eq_circle qs ξ.2 n]
      rw [← standardAdditiveCharacter_add]
      congr 1
      ring

theorem stdAddChar_neg_natCast_eq_standardAdditiveCharacter_div
    {N : ℕ} [NeZero N] (a : ℕ) :
    ZMod.stdAddChar (-(a : ZMod N)) =
      standardAdditiveCharacter (-((a : ℝ) / N)) := by
  rw [show -(a : ZMod N) = ((-(a : ℤ) : ℤ) : ZMod N) by norm_num]
  rw [ZMod.stdAddChar_coe]
  unfold standardAdditiveCharacter
  push_cast
  congr 1
  ring

/-- The abstract dual-CRT frequency is the explicit tensor numerator modulo
the modulus product. -/
theorem crtTensorFrequency_eq_numerator
    (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (ξ : SieveCube qs) :
    crtTensorFrequency qs hpair ξ =
      (tensorFrequencyNumerator qs ξ :
        ZMod (sieveModulusProduct qs)) := by
  apply neg_injective
  apply ZMod.injective_stdAddChar
  have hkernel := crtTensorFrequency_kernel qs hpair ξ
    ((1 : ℕ) : ZMod (sieveModulusProduct qs))
  rw [sieveCrtAddEquiv_natCast qs hpair 1] at hkernel
  norm_num at hkernel
  rw [hkernel]
  rw [tensorDftChar_natSieveCube_eq_circle]
  rw [tensorCircleFrequency_eq_numerator_div_product]
  symm
  simpa using
    (stdAddChar_neg_natCast_eq_standardAdditiveCharacter_div
      (N := sieveModulusProduct qs) (tensorFrequencyNumerator qs ξ))

set_option linter.unusedVariables false in
/-- Every modulus coordinate on which a tensor frequency is nonzero fails to
divide its common-denominator numerator. -/
theorem tensorFrequencyNumerator_not_dvd :
    ∀ (qs : List SieveModulus)
      (hpair : qs.Pairwise
        (Function.onFun Nat.Coprime SieveModulus.modulus))
      (ξ : SieveCube qs), TensorFrequencyNonzero ξ →
      ∀ q ∈ qs, ¬ q.modulus ∣ tensorFrequencyNumerator qs ξ
  | [], _, ξ, hfreq, q, hq => by simp at hq
  | q :: qs, hpair, ξ, hfreq, r, hr => by
      rcases List.mem_cons.mp hr with rfl | hr
      · intro hdvd
        have htail : r.modulus ∣
            r.modulus * tensorFrequencyNumerator qs ξ.2 :=
          dvd_mul_right _ _
        have hhead : r.modulus ∣
            ξ.1.val * sieveModulusProduct qs :=
          (Nat.dvd_add_iff_left htail).2 hdvd
        have hcop := pairwise_head_coprime_sieveModulusProduct hpair
        have hval : r.modulus ∣ ξ.1.val :=
          hcop.dvd_of_dvd_mul_right hhead
        have hvalZero : ξ.1.val = 0 :=
          Nat.eq_zero_of_dvd_of_lt hval (ZMod.val_lt ξ.1)
        exact hfreq.1 ((ZMod.val_eq_zero ξ.1).mp hvalZero)
      · intro hdvd
        have hrProd : r.modulus ∣ sieveModulusProduct qs := by
          exact List.dvd_prod (List.mem_map.mpr ⟨r, hr, rfl⟩)
        have hfirst : r.modulus ∣
            ξ.1.val * sieveModulusProduct qs :=
          dvd_mul_of_dvd_right hrProd _
        have htailMul : r.modulus ∣
            q.modulus * tensorFrequencyNumerator qs ξ.2 :=
          (Nat.dvd_add_iff_right hfirst).2 hdvd
        have hcop : r.modulus.Coprime q.modulus :=
          ((List.pairwise_cons.mp hpair).1 r hr).symm
        have htail : r.modulus ∣ tensorFrequencyNumerator qs ξ.2 :=
          hcop.dvd_of_dvd_mul_left htailMul
        exact (tensorFrequencyNumerator_not_dvd qs
          (List.pairwise_cons.mp hpair).2 ξ.2 hfreq.2 r hr) htail

/-- Consequently, every selected coordinate modulus fails to divide the
canonical representative of the CRT-reindexed cyclic frequency. -/
theorem crtTensorFrequency_val_not_dvd
    (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (ξ : SieveCube qs) (hfreq : TensorFrequencyNonzero ξ)
    (q : SieveModulus) (hq : q ∈ qs) :
    ¬ q.modulus ∣ (crtTensorFrequency qs hpair ξ).val := by
  intro hdvd
  have hEq := congrArg ZMod.val
    (crtTensorFrequency_eq_numerator qs hpair ξ)
  rw [ZMod.val_natCast] at hEq
  have hqProd : q.modulus ∣ sieveModulusProduct qs := by
    exact List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)
  have hdvdMod : q.modulus ∣
      tensorFrequencyNumerator qs ξ % sieveModulusProduct qs := by
    rw [← hEq]
    exact hdvd
  have hdvdNum : q.modulus ∣ tensorFrequencyNumerator qs ξ :=
    (Nat.dvd_mod_iff hqProd).mp hdvdMod
  exact (tensorFrequencyNumerator_not_dvd qs hpair ξ hfreq q hq)
    hdvdNum

/-- An exclusive coprime modulus separates a tensor frequency from every
frequency attached to the other denominator. -/
theorem crtTensorFrequency_cross_ne_of_exclusive
    (qs rs : List SieveModulus)
    (hpairqs : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (hpairs : rs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (ξ : SieveCube qs) (hξ : TensorFrequencyNonzero ξ)
    (η : SieveCube rs)
    (q : SieveModulus) (hq : q ∈ qs)
    (hqcop : ∀ r ∈ rs, q.modulus.Coprime r.modulus) :
    (crtTensorFrequency qs hpairqs ξ).val * sieveModulusProduct rs ≠
      (crtTensorFrequency rs hpairs η).val * sieveModulusProduct qs := by
  intro heq
  have hqQs : q.modulus ∣ sieveModulusProduct qs := by
    exact List.dvd_prod (List.mem_map.mpr ⟨q, hq, rfl⟩)
  have hqRight : q.modulus ∣
      (crtTensorFrequency rs hpairs η).val * sieveModulusProduct qs :=
    dvd_mul_of_dvd_right hqQs _
  have hqLeft : q.modulus ∣
      (crtTensorFrequency qs hpairqs ξ).val * sieveModulusProduct rs := by
    rw [heq]
    exact hqRight
  have hcopProd : q.modulus.Coprime (sieveModulusProduct rs) := by
    rw [sieveModulusProduct, Nat.coprime_list_prod_right_iff]
    intro m hm
    rw [List.mem_map] at hm
    rcases hm with ⟨r, hr, rfl⟩
    exact hqcop r hr
  have hqVal : q.modulus ∣ (crtTensorFrequency qs hpairqs ξ).val :=
    hcopProd.dvd_of_dvd_mul_right hqLeft
  exact (crtTensorFrequency_val_not_dvd qs hpairqs ξ hξ q hq) hqVal

/-- Distinct tensor frequencies on one modulus list also have unequal
cross-products. -/
theorem crtTensorFrequency_cross_ne_of_same_list
    (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (ξ η : SieveCube qs) (hne : ξ ≠ η) :
    (crtTensorFrequency qs hpair ξ).val * sieveModulusProduct qs ≠
      (crtTensorFrequency qs hpair η).val * sieveModulusProduct qs := by
  intro heq
  have hval : (crtTensorFrequency qs hpair ξ).val =
      (crtTensorFrequency qs hpair η).val :=
    Nat.mul_right_cancel (NeZero.pos _) heq
  have hk : crtTensorFrequency qs hpair ξ =
      crtTensorFrequency qs hpair η :=
    ZMod.val_injective _ hval
  exact hne (crtTensorFrequency_injective qs hpair hk)

/-- A nonintegral difference of rational frequencies of denominators `N`
and `M` is separated from the integers by at least `1/(N*M)`. -/
theorem rationalDifference_separated
    {a b N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hne : nearestIntegerDistance
      ((a : ℝ) / N - (b : ℝ) / M) ≠ 0) :
    1 / ((N * M : ℕ) : ℝ) ≤ nearestIntegerDistance
      ((a : ℝ) / N - (b : ℝ) / M) := by
  let theta : ℝ := (a : ℝ) / N - (b : ℝ) / M
  let r : ℤ := (a : ℤ) * M - (b : ℤ) * N -
    round theta * (N * M : ℕ)
  have hD : (0 : ℝ) < (N * M : ℕ) := by positivity
  have hrepr : theta - (round theta : ℝ) =
      (r : ℝ) / ((N * M : ℕ) : ℝ) := by
    dsimp only [theta, r]
    push_cast
    field_simp
  have hr : r ≠ 0 := by
    intro hr
    apply hne
    unfold nearestIntegerDistance
    rw [hrepr, hr]
    norm_num
  have habs : (1 : ℝ) ≤ |(r : ℝ)| := by
    exact_mod_cast Int.one_le_abs hr
  unfold nearestIntegerDistance
  rw [hrepr, abs_div, abs_of_pos hD]
  gcongr

/-- For canonical representatives, distinctness modulo one is exactly
certified by unequal cross-products. -/
theorem rationalDifference_nearestIntegerDistance_ne_zero
    {a b N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (ha : a < N) (hb : b < M) (hcross : a * M ≠ b * N) :
    nearestIntegerDistance
      ((a : ℝ) / N - (b : ℝ) / M) ≠ 0 := by
  let theta : ℝ := (a : ℝ) / N - (b : ℝ) / M
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have ha0 : (0 : ℝ) ≤ (a : ℝ) / N := by positivity
  have hb0 : (0 : ℝ) ≤ (b : ℝ) / M := by positivity
  have ha1 : (a : ℝ) / N < 1 := by
    rw [div_lt_one hNreal]
    exact_mod_cast ha
  have hb1 : (b : ℝ) / M < 1 := by
    rw [div_lt_one hMreal]
    exact_mod_cast hb
  have hthetaLower : (-1 : ℝ) < theta := by
    dsimp only [theta]
    linarith
  have hthetaUpper : theta < 1 := by
    dsimp only [theta]
    linarith
  intro hzero
  have heq : theta = (round theta : ℝ) := by
    have habs : |theta - (round theta : ℝ)| = 0 := by
      simpa only [nearestIntegerDistance] using hzero
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  have hroundLower : (-1 : ℤ) < round theta := by
    exact_mod_cast (heq ▸ hthetaLower)
  have hroundUpper : round theta < (1 : ℤ) := by
    exact_mod_cast (heq ▸ hthetaUpper)
  have hround : round theta = 0 := by omega
  have htheta : theta = 0 := by simpa [hround] using heq
  apply hcross
  dsimp only [theta] at htheta
  have hfrac : (a : ℝ) / N = (b : ℝ) / M := sub_eq_zero.mp htheta
  have hcrossReal : (a : ℝ) * M = (b : ℝ) * N :=
    (div_eq_div_iff hNreal.ne' hMreal.ne').mp hfrac
  exact_mod_cast hcrossReal

theorem rationalDifference_separated_of_cross_ne
    {a b N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (ha : a < N) (hb : b < M) (hcross : a * M ≠ b * N) :
    1 / ((N * M : ℕ) : ℝ) ≤ nearestIntegerDistance
      ((a : ℝ) / N - (b : ℝ) / M) :=
  rationalDifference_separated hN hM
    (rationalDifference_nearestIntegerDistance_ne_zero
      hN hM ha hb hcross)

theorem cyclicCircleFrequencies_pairwise_separated
    {A : Type*} {L : ℕ}
    (N : A → ℕ) (hN : ∀ a, 0 < N a)
    (k : (a : A) → ZMod (N a))
    (hdistinct : ∀ a b, a ≠ b → nearestIntegerDistance
      (cyclicCircleFrequency (N a) (k a) -
        cyclicCircleFrequency (N b) (k b)) ≠ 0)
    (hprod : ∀ a b, N a * N b ≤ L) :
    ∀ a b, a ≠ b → 1 / (L : ℝ) ≤ nearestIntegerDistance
      (cyclicCircleFrequency (N a) (k a) -
        cyclicCircleFrequency (N b) (k b)) := by
  intro a b hab
  have hD : (0 : ℝ) < (N a * N b : ℕ) := by
    exact_mod_cast Nat.mul_pos (hN a) (hN b)
  calc
    1 / (L : ℝ) ≤ 1 / ((N a * N b : ℕ) : ℝ) := by
      apply one_div_le_one_div_of_le hD
      exact_mod_cast hprod a b
    _ ≤ nearestIntegerDistance
        (cyclicCircleFrequency (N a) (k a) -
          cyclicCircleFrequency (N b) (k b)) :=
      rationalDifference_separated (hN a) (hN b)
        (hdistinct a b hab)

theorem cyclicCircleFrequencies_pairwise_separated_of_cross_ne
    {A : Type*} {L : ℕ}
    (N : A → ℕ) (hN : ∀ a, 0 < N a)
    (k : (a : A) → ZMod (N a))
    (hcross : ∀ a b, a ≠ b →
      (k a).val * N b ≠ (k b).val * N a)
    (hprod : ∀ a b, N a * N b ≤ L) :
    ∀ a b, a ≠ b → 1 / (L : ℝ) ≤ nearestIntegerDistance
      (cyclicCircleFrequency (N a) (k a) -
        cyclicCircleFrequency (N b) (k b)) := by
  apply cyclicCircleFrequencies_pairwise_separated N hN k
  · intro a b hab
    letI : NeZero (N a) := ⟨Nat.ne_of_gt (hN a)⟩
    letI : NeZero (N b) := ⟨Nat.ne_of_gt (hN b)⟩
    exact rationalDifference_nearestIntegerDistance_ne_zero
      (hN a) (hN b) (ZMod.val_lt _) (ZMod.val_lt _) (hcross a b hab)
  · exact hprod

/-- Global large-sieve upper bound for a denominator-indexed family once
distinctness modulo one and the pairwise denominator-product budget are
known. -/
theorem circleAnalysis_energy_le_of_cyclic_frequencies
    {A : Type*} [Fintype A] [DecidableEq A]
    {L : ℕ} (hL : 0 < L)
    (N : A → ℕ) (hN : ∀ a, 0 < N a)
    (k : (a : A) → ZMod (N a))
    (hdistinct : ∀ a b, a ≠ b → nearestIntegerDistance
      (cyclicCircleFrequency (N a) (k a) -
        cyclicCircleFrequency (N b) (k b)) ≠ 0)
    (hprod : ∀ a b, N a * N b ≤ L) (f : Fin L → ℂ) :
    ∑ a, Complex.normSq (finiteAnalysis
        (fun a (n : Fin L) => circleCharacterVector
          (fun a => cyclicCircleFrequency (N a) (k a)) a n) f a) ≤
      (8 * L : ℝ) * ∑ n, Complex.normSq (f n) := by
  exact circleAnalysis_energy_le_of_pairwise_separated hL
    (fun a => cyclicCircleFrequency (N a) (k a)) f
    (cyclicCircleFrequencies_pairwise_separated N hN k hdistinct hprod)

/-- Cross-product formulation of the rational global large sieve. -/
theorem circleAnalysis_energy_le_of_cyclic_frequencies_of_cross_ne
    {A : Type*} [Fintype A] [DecidableEq A]
    {L : ℕ} (hL : 0 < L)
    (N : A → ℕ) (hN : ∀ a, 0 < N a)
    (k : (a : A) → ZMod (N a))
    (hcross : ∀ a b, a ≠ b →
      (k a).val * N b ≠ (k b).val * N a)
    (hprod : ∀ a b, N a * N b ≤ L) (f : Fin L → ℂ) :
    ∑ a, Complex.normSq (finiteAnalysis
        (fun a (n : Fin L) => circleCharacterVector
          (fun a => cyclicCircleFrequency (N a) (k a)) a n) f a) ≤
      (8 * L : ℝ) * ∑ n, Complex.normSq (f n) := by
  exact circleAnalysis_energy_le_of_pairwise_separated hL
    (fun a => cyclicCircleFrequency (N a) (k a)) f
    (cyclicCircleFrequencies_pairwise_separated_of_cross_ne
      N hN k hcross hprod)

/-! ## Global families of tensor frequencies -/

/-- All coordinatewise-nonzero tensor frequencies over a finite family of
modulus lists. -/
def TensorFrequencyFamilyIndex {B : Type*}
    (qs : B → List SieveModulus) :=
  Σ i, ↥(tensorNonzeroFrequencies (qs i))

noncomputable instance tensorFrequencyFamilyIndexFintype
    {B : Type*} [Fintype B] (qs : B → List SieveModulus) :
    Fintype (TensorFrequencyFamilyIndex qs) := by
  classical
  unfold TensorFrequencyFamilyIndex
  infer_instance

def tensorFrequencyFamilyModulus {B : Type*}
    {qs : B → List SieveModulus}
    (a : TensorFrequencyFamilyIndex qs) : ℕ :=
  sieveModulusProduct (qs a.1)

def tensorFrequencyFamilyCyclic {B : Type*}
    {qs : B → List SieveModulus}
    (hpair : ∀ i, (qs i).Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (a : TensorFrequencyFamilyIndex qs) :
    ZMod (tensorFrequencyFamilyModulus a) :=
  crtTensorFrequency (qs a.1) (hpair a.1) a.2.1

/-- Cross-product distinctness for the union of all tensor frequencies.  Two
frequencies over one list are separated by CRT injectivity; two different
lists are separated by a modulus exclusive to the first list and coprime to
every modulus of the second. -/
theorem tensorFrequencyFamily_cross_ne
    {B : Type*} {qs : B → List SieveModulus}
    (hpair : ∀ i, (qs i).Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (hexclusive : ∀ i j, i ≠ j → ∃ q ∈ qs i,
      ∀ r ∈ qs j, q.modulus.Coprime r.modulus)
    (a b : TensorFrequencyFamilyIndex qs) (hab : a ≠ b) :
    (tensorFrequencyFamilyCyclic hpair a).val *
        tensorFrequencyFamilyModulus b ≠
      (tensorFrequencyFamilyCyclic hpair b).val *
        tensorFrequencyFamilyModulus a := by
  classical
  rcases a with ⟨i, ξ⟩
  rcases b with ⟨j, η⟩
  by_cases hij : i = j
  · subst j
    have hξη : ξ.1 ≠ η.1 := by
      intro h
      apply hab
      have hsub : ξ = η := Subtype.ext h
      subst η
      rfl
    exact crtTensorFrequency_cross_ne_of_same_list
      (qs i) (hpair i) ξ.1 η.1 hξη
  · rcases hexclusive i j hij with ⟨q, hqi, hqcop⟩
    exact crtTensorFrequency_cross_ne_of_exclusive
      (qs i) (qs j) (hpair i) (hpair j) ξ.1
      (Finset.mem_filter.mp ξ.2).2 η.1 q hqi hqcop

/-- Quantitative `1/L` separation of the global tensor-frequency family. -/
theorem tensorFrequencyFamily_pairwise_separated
    {B : Type*} {qs : B → List SieveModulus} {L : ℕ}
    (hpair : ∀ i, (qs i).Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (hexclusive : ∀ i j, i ≠ j → ∃ q ∈ qs i,
      ∀ r ∈ qs j, q.modulus.Coprime r.modulus)
    (hprod : ∀ i j,
      sieveModulusProduct (qs i) * sieveModulusProduct (qs j) ≤ L) :
    ∀ a b : TensorFrequencyFamilyIndex qs, a ≠ b →
      1 / (L : ℝ) ≤ nearestIntegerDistance
        (cyclicCircleFrequency (tensorFrequencyFamilyModulus a)
            (tensorFrequencyFamilyCyclic hpair a) -
          cyclicCircleFrequency (tensorFrequencyFamilyModulus b)
            (tensorFrequencyFamilyCyclic hpair b)) := by
  apply cyclicCircleFrequencies_pairwise_separated_of_cross_ne
    tensorFrequencyFamilyModulus
    (fun a => Nat.pos_of_ne_zero
      (sieveModulusProduct_ne_zero (qs a.1)))
    (tensorFrequencyFamilyCyclic hpair)
  · exact tensorFrequencyFamily_cross_ne hpair hexclusive
  · intro a b
    exact hprod a.1 b.1

/-- Loss-free global upper bound across every tensor frequency from every
selected modulus list. -/
theorem circleAnalysis_energy_le_tensorFrequencyFamily
    {B : Type*} [Fintype B]
    {qs : B → List SieveModulus} {L : ℕ} (hL : 0 < L)
    (hpair : ∀ i, (qs i).Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (hexclusive : ∀ i j, i ≠ j → ∃ q ∈ qs i,
      ∀ r ∈ qs j, q.modulus.Coprime r.modulus)
    (hprod : ∀ i j,
      sieveModulusProduct (qs i) * sieveModulusProduct (qs j) ≤ L)
    (f : Fin L → ℂ) :
    ∑ a : TensorFrequencyFamilyIndex qs,
        Complex.normSq (finiteAnalysis
          (fun a (n : Fin L) => circleCharacterVector
            (fun a => cyclicCircleFrequency
              (tensorFrequencyFamilyModulus a)
              (tensorFrequencyFamilyCyclic hpair a)) a n) f a) ≤
      (8 * L : ℝ) * ∑ n, Complex.normSq (f n) := by
  classical
  exact circleAnalysis_energy_le_of_pairwise_separated hL _ f
    (tensorFrequencyFamily_pairwise_separated hpair hexclusive hprod)

end

end Tao2026
