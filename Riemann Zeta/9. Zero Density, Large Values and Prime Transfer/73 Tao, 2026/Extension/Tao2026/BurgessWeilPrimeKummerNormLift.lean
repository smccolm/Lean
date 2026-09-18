import Tao2026.BurgessWeilPrimeKummerFrobeniusSystem

/-!
# Norm lifting multiplicative characters to finite extensions

The Kummer trace over a finite extension uses the base character composed
with the extension norm.  This file packages that operation as an injective
monoid homomorphism on multiplicative characters.  Surjectivity of the norm
then proves that nontriviality and the exact character order are preserved.

These facts are the algebraic input for constructing the elementary
one- and two-root Frobenius power-trace systems.
-/

namespace Tao2026

open Finset Complex Polynomial
open scoped BigOperators ComplexConjugate

noncomputable section

/-- Pull a complex multiplicative character on a finite field back along the
norm of a finite field extension. -/
def finiteFieldNormLiftMulChar
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite L] :
    MulChar K ℂ →* MulChar L ℂ where
  toFun χ :=
    { χ.toMonoidHom.comp (Algebra.norm K) with
      map_nonunit' := by
        intro x hx
        have hx0 : x = 0 := by
          by_contra hx0
          exact hx ((isUnit_iff_ne_zero).2 hx0)
        subst x
        simpa using MulChar.map_zero χ }
  map_one' := by
    apply MulChar.ext
    intro x
    change (1 : MulChar K ℂ) (Algebra.norm K (x : L)) =
      (1 : MulChar L ℂ) x
    rw [MulChar.one_apply (IsUnit.map (Algebra.norm K) x.isUnit),
      MulChar.one_apply_coe]
  map_mul' χ ψ := by
    apply MulChar.ext
    intro x
    change (χ * ψ) (Algebra.norm K (x : L)) =
      χ (Algebra.norm K (x : L)) * ψ (Algebra.norm K (x : L))
    rfl

@[simp]
theorem finiteFieldNormLiftMulChar_apply
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite L]
    (χ : MulChar K ℂ) (x : L) :
    finiteFieldNormLiftMulChar K L χ x = χ (Algebra.norm K x) :=
  rfl

/-- Surjectivity of the finite-field norm makes norm pullback injective on
multiplicative characters. -/
theorem finiteFieldNormLiftMulChar_injective
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite L] :
    Function.Injective (finiteFieldNormLiftMulChar K L) := by
  intro χ ψ hχψ
  apply MulChar.ext
  intro a
  obtain ⟨x, hx⟩ := FiniteField.norm_surjective K L (a : K)
  have hx0 : x ≠ 0 := by
    intro hx0
    subst x
    have ha0 : (a : K) = 0 := by simpa using hx.symm
    exact a.ne_zero ha0
  let xu : Lˣ := ((isUnit_iff_ne_zero).2 hx0).unit
  have heval := congrArg (fun η : MulChar L ℂ => η xu) hχψ
  change χ (Algebra.norm K (xu : L)) =
    ψ (Algebra.norm K (xu : L)) at heval
  simpa [xu, hx] using heval

/-- Norm lifting preserves the exact order of a finite-field character. -/
theorem orderOf_finiteFieldNormLiftMulChar
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite L]
    (χ : MulChar K ℂ) :
    orderOf (finiteFieldNormLiftMulChar K L χ) = orderOf χ :=
  orderOf_injective (finiteFieldNormLiftMulChar K L)
    (finiteFieldNormLiftMulChar_injective K L) χ

/-- A split polynomial with one distinct root remains a scalar times one
power after base change to any extension field. -/
theorem eval_map_eq_leadingCoeff_mul_pow_of_single_root
    {K L : Type*} [Field K] [DecidableEq K] [Field L] [Algebra K L]
    (P : Polynomial K) (a : K) (hP : P.Splits)
    (hroots : P.roots.toFinset = {a}) (x : L) :
    (P.map (algebraMap K L)).eval x =
      algebraMap K L P.leadingCoeff *
        (x - algebraMap K L a) ^ P.rootMultiplicity a := by
  classical
  have hrootMultiset :
      P.roots = Multiset.replicate P.roots.card a := by
    apply Multiset.eq_replicate_card.mpr
    intro b hb
    have hb' : b ∈ P.roots.toFinset := Multiset.mem_toFinset.mpr hb
    rw [hroots] at hb'
    simpa using hb'
  have hcount : P.rootMultiplicity a = P.roots.card := by
    exact (Polynomial.count_roots P).symm.trans (by
      rw [hrootMultiset, Multiset.count_replicate_self]
      simp)
  rw [hcount]
  conv_lhs => rw [Polynomial.eval_map, hP.eq_prod_roots]
  conv_lhs => rw [hrootMultiset]
  simp

/-- In particular, a nontrivial base character remains nontrivial after norm
lifting to every finite extension. -/
theorem finiteFieldNormLiftMulChar_ne_one
    (K L : Type*) [Field K] [Field L] [Algebra K L] [Finite L]
    {χ : MulChar K ℂ} (hχ : χ ≠ 1) :
    finiteFieldNormLiftMulChar K L χ ≠ 1 := by
  intro htrivial
  apply hχ
  exact (finiteFieldNormLiftMulChar_injective K L)
    (by simpa using htrivial)

/-- Every higher Kummer extension correlation is literally a polynomial
correlation for the norm-lifted character on that extension field. -/
theorem primeKummerExtensionCorrelation_succ_eq_normLift
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) (n : ℕ) :
    primeKummerExtensionCorrelation p χ P (n + 1) = by
      let E := FiniteField.Extension (ZMod p) p (n + 2)
      letI : Fintype E := Fintype.ofFinite E
      exact ∑ x : E,
        finiteFieldNormLiftMulChar (ZMod p) E χ
          ((P.map (algebraMap (ZMod p) E)).eval x) := by
  rfl

/-- A one-root split polynomial with active character exponent has zero
correlation after norm lifting to every finite extension. -/
theorem sum_finiteFieldNormLift_eval_map_eq_zero_of_single_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hroots : P.roots.toFinset = {a})
    (d : ℕ) [NeZero d] : by
      let E := FiniteField.Extension (ZMod p) p d
      letI : Fintype E := Fintype.ofFinite E
      exact ∑ x : E,
        finiteFieldNormLiftMulChar (ZMod p) E χ
          ((P.map (algebraMap (ZMod p) E)).eval x) = 0 := by
  let E := FiniteField.Extension (ZMod p) p d
  letI : Fintype E := Fintype.ofFinite E
  let χE := finiteFieldNormLiftMulChar (ZMod p) E χ
  let m := P.rootMultiplicity a
  have hm : m ≠ 0 := by
    intro hm0
    apply hnot
    rw [show P.rootMultiplicity a = 0 from hm0]
    exact dvd_zero _
  have hpow : χE ^ m ≠ 1 := by
    intro hpow
    apply hnot
    rw [← orderOf_finiteFieldNormLiftMulChar (ZMod p) E χ]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
  calc
    (∑ x : E, χE ((P.map (algebraMap (ZMod p) E)).eval x)) =
        ∑ x : E,
          χE (algebraMap (ZMod p) E P.leadingCoeff) *
            χE (x - algebraMap (ZMod p) E a) ^ m := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [eval_map_eq_leadingCoeff_mul_pow_of_single_root
        P a hP hroots x, map_mul, map_pow]
    _ = χE (algebraMap (ZMod p) E P.leadingCoeff) *
        ∑ x : E, (χE ^ m) (x - algebraMap (ZMod p) E a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [MulChar.pow_apply' χE hm]
    _ = χE (algebraMap (ZMod p) E P.leadingCoeff) *
        ∑ x : E, (χE ^ m) x := by
      congr 1
      exact Equiv.sum_comp
        (Equiv.subRight (algebraMap (ZMod p) E a))
        (fun x : E => (χE ^ m) x)
    _ = 0 := by
      rw [MulChar.sum_eq_zero_of_ne_one hpow, mul_zero]

/-- Thus all positive-degree Kummer extension correlations vanish in the
active one-root case. -/
theorem primeKummerExtensionCorrelation_eq_zero_of_single_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hroots : P.roots.toFinset = {a}) :
    ∀ n : ℕ, primeKummerExtensionCorrelation p χ P n = 0
  | 0 => by
      exact primeSplitPolynomialCorrelation_eq_zero_of_single_root
        p χ P a hP hnot hroots
  | n + 1 => by
      rw [primeKummerExtensionCorrelation_succ_eq_normLift]
      exact sum_finiteFieldNormLift_eval_map_eq_zero_of_single_root
        p χ P a hP hnot hroots (n + 2)

/-- The one-root case of the all-extension Frobenius source theorem is
constructed unconditionally: it is the empty spectrum. -/
theorem exists_primeKummerIsotypicFrobeniusSystem_of_single_root
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p))
    (a : ZMod p) (hP : P.Splits)
    (hnot : ¬orderOf χ ∣ P.rootMultiplicity a)
    (hroots : P.roots.toFinset = {a}) :
    Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P) := by
  refine ⟨{
    rank := 0
    eigenvalue := Fin.elim0
    rank_le := by simp
    integral := fun i => Fin.elim0 i
    weight_le := fun i => Fin.elim0 i
    trace_eq := by
      rw [primeSplitPolynomialCorrelation_eq_zero_of_single_root
        p χ P a hP hnot hroots]
      simp
    extensionTrace_eq := fun n => by
      rw [primeKummerExtensionCorrelation_eq_zero_of_single_root
        p χ P a hP hnot hroots n]
      simp }⟩

/-- The full all-extension Kummer Frobenius source proposition. -/
def TaoPrimeKummerIsotypicFrobeniusSystem : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- The exact two-root all-extension residual.  Its construction is the
finite-field Hasse--Davenport compatibility for the Jacobi eigenvalue. -/
def TaoPrimeKummerIsotypicFrobeniusSystemTwoRoots : Prop :=
  ∀ (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)),
    χ ≠ 1 → P.Splits → ¬IsMulCharOrderScalarPower χ P →
      P.roots.toFinset.card = 2 →
        Nonempty (PrimeKummerIsotypicFrobeniusSystem p χ P)

/-- Once the exact two-root Hasse--Davenport case and the three-or-more-root
cohomological case are supplied, the one-root construction above gives the
full Frobenius system theorem. -/
theorem taoPrimeKummerIsotypicFrobeniusSystem_of_twoRoots_and_threeRootsOrMore
    (htwo : TaoPrimeKummerIsotypicFrobeniusSystemTwoRoots)
    (hthree : TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore) :
    TaoPrimeKummerIsotypicFrobeniusSystem := by
  intro p _ _ χ P hχ hP hpower
  have hP0 : P ≠ 0 := by
    intro hzero
    subst P
    exact hpower (isMulCharOrderScalarPower_zero χ)
  obtain ⟨a, ha, hactive⟩ :=
    (not_isMulCharOrderScalarPower_iff_exists_not_dvd_rootMultiplicity
      χ P hP0 hP).mp hpower
  have hcardPos : 0 < P.roots.toFinset.card :=
    Finset.card_pos.mpr ⟨a, ha⟩
  by_cases hcardThree : 3 ≤ P.roots.toFinset.card
  · exact hthree p χ P hχ hP hpower hcardThree
  have hcardLe : P.roots.toFinset.card ≤ 2 := by omega
  rcases Nat.eq_or_lt_of_le hcardLe with hcardTwo | hcardLtTwo
  · exact htwo p χ P hχ hP hpower hcardTwo
  · have hcardOne : P.roots.toFinset.card = 1 := by omega
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hcardOne
    have hab : a = b := by simpa [hb] using ha
    subst b
    exact exists_primeKummerIsotypicFrobeniusSystem_of_single_root
      p χ P a hP hactive hb

/-- Therefore the full source proposition is exactly the conjunction of the
two-root Hasse--Davenport residual and the three-or-more-root geometric
residual; zero and one distinct roots are already unconditional. -/
theorem taoPrimeKummerIsotypicFrobeniusSystem_iff_twoRoots_and_threeRootsOrMore :
    TaoPrimeKummerIsotypicFrobeniusSystem ↔
      TaoPrimeKummerIsotypicFrobeniusSystemTwoRoots ∧
        TaoPrimeKummerIsotypicFrobeniusSystemThreeRootsOrMore := by
  constructor
  · intro hfull
    constructor
    · intro p _ _ χ P hχ hP hpower _hcard
      exact hfull p χ P hχ hP hpower
    · intro p _ _ χ P hχ hP hpower _hcard
      exact hfull p χ P hχ hP hpower
  · rintro ⟨htwo, hthree⟩
    exact taoPrimeKummerIsotypicFrobeniusSystem_of_twoRoots_and_threeRootsOrMore
      htwo hthree

/-- The full all-extension theorem forgets to the sharp base-field spectral
theorem. -/
theorem TaoPrimeKummerIsotypicFrobeniusSystem.toSpectrum
    (hsystem : TaoPrimeKummerIsotypicFrobeniusSystem) :
    TaoPrimeKummerIsotypicFrobeniusSpectrum := by
  intro p _ _ χ P hχ hP hpower
  exact (hsystem p χ P hχ hP hpower).map
    PrimeKummerIsotypicFrobeniusSystem.toSpectrum

/-- Hence the full all-extension theorem supplies the exact fixed-`r=7`
Burgess input. -/
theorem TaoPrimeKummerIsotypicFrobeniusSystem.toCompositeRSeven
    (hsystem : TaoPrimeKummerIsotypicFrobeniusSystem) :
    TaoPrimitiveCubefreeBurgessCompleteWeilBoundRSeven :=
  hsystem.toSpectrum.toCompositeRSeven

/-- Complex values of characters on arbitrary finite fields are algebraic
integers. -/
theorem isIntegral_finiteFieldMulChar_apply
    {F : Type*} [Field F] [Finite F]
    (χ : MulChar F ℂ) (x : F) : IsIntegral ℤ (χ x) := by
  letI : Fintype F := Fintype.ofFinite F
  by_cases hx : x = 0
  · subst x
    rw [MulChar.map_zero]
    exact isIntegral_zero
  · apply IsIntegral.of_pow χ.orderOf_pos
    obtain ⟨ζ, hζ, hζeq⟩ := χ.apply_mem_rootsOfUnity_orderOf hx
    rw [← hζeq, (mem_rootsOfUnity' (orderOf χ) ζ).mp hζ]
    exact isIntegral_one

/-- Consequently every norm-lifted Kummer extension correlation is an
algebraic integer. -/
theorem isIntegral_primeKummerExtensionCorrelation
    (p : ℕ) [NeZero p] [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (P : Polynomial (ZMod p)) :
    ∀ n : ℕ, IsIntegral ℤ (primeKummerExtensionCorrelation p χ P n)
  | 0 => by
      simpa using isIntegral_primePolynomialCharacterCorrelation p χ P
  | n + 1 => by
      rw [primeKummerExtensionCorrelation_succ_eq_normLift]
      let E := FiniteField.Extension (ZMod p) p (n + 2)
      letI : Fintype E := Fintype.ofFinite E
      exact IsIntegral.sum
        (fun x : E =>
          finiteFieldNormLiftMulChar (ZMod p) E χ
            ((P.map (algebraMap (ZMod p) E)).eval x))
        (fun x _hx => isIntegral_finiteFieldMulChar_apply
          (finiteFieldNormLiftMulChar (ZMod p) E χ)
          ((P.map (algebraMap (ZMod p) E)).eval x))

end

end Tao2026
