/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.ModularFormOver.Basic
import LeanModularForms.HeckeRIngs.GL2.FourierHecke
import LeanModularForms.Modularforms.LFunction
import ModularFormsMod.PInteger

/-!
# Hecke operators over coefficient rings

`HeckeOver R N` is the subring of weightwise endomorphisms of forms on `Γ₁(N)` that preserve
the trivial-character subspace and the forms in that subspace with q-expansion coefficients in
`R`. The character-space condition is needed for the available Fourier formula for `Tₙ`.
-/

open ModularForm CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup

namespace ModularFormOver

/-- The trivial complex character of the unit group of `ZMod N`. -/
def trivialChar (N : ℕ) : (ZMod N)ˣ →* ℂˣ := 1

set_option maxHeartbeats 1000000 in
-- The ring closure proof unfolds the character-space and q-expansion predicates.
/-- The ring of weightwise endomorphisms preserving the trivial-character subspace and
its forms with coefficients in `R`. -/
def HeckeOver (R : Type*) [CommRing R] [Algebra R ℂ] (N : ℕ) [NeZero N] :
    Subring (∀ k : ℤ, Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) where
  carrier := {T | ∀ k f, f ∈ HeckeRing.GL2.modFormCharSpace k (trivialChar N) →
    ModularForm.isOver R f →
    T k f ∈ HeckeRing.GL2.modFormCharSpace k (trivialChar N) ∧
      ModularForm.isOver R (T k f)}
  zero_mem' := by
    intro k f hf₁ hf₂
    exact ⟨Submodule.zero_mem _, ModularForm.isOver_zero (R := R)⟩
  one_mem' := by
    intro k f hf₁ hf₂
    exact ⟨hf₁, hf₂⟩
  add_mem' := by
    intro T S hT hS k f hf₁ hf₂
    rcases hT k f hf₁ hf₂ with ⟨hTc, hTo⟩
    rcases hS k f hf₁ hf₂ with ⟨hSc, hSo⟩
    exact ⟨Submodule.add_mem _ hTc hSc,
      ModularForm.isOver_add (F := ModularForm ((Gamma1 N).map (mapGL ℝ)) k) hTo hSo⟩
  neg_mem' := by
    intro T hT k f hf₁ hf₂
    rcases hT k f hf₁ hf₂ with ⟨hTc, hTo⟩
    exact ⟨Submodule.neg_mem _ hTc,
      ModularForm.isOver_neg (F := ModularForm ((Gamma1 N).map (mapGL ℝ)) k) hTo⟩
  mul_mem' := by
    intro T S hT hS k f hf₁ hf₂
    rcases hS k f hf₁ hf₂ with ⟨hSc, hSo⟩
    exact hT k ((S k) f) hSc hSo


/-- Forget the coefficient-preservation condition and retain the family of complex linear
endomorphisms. -/
def HeckeOver.toEnd (R : Type*) [CommRing R] [Algebra R ℂ] (N : ℕ) [NeZero N] :
    HeckeOver R N →+* (∀ k : ℤ, Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) :=
  (HeckeOver R N).subtype

/-- Include one ring of coefficient-preserving operators in another using a supplied containment. -/
def HeckeOver.inclusion {R S : Type*} [CommRing R] [Algebra R ℂ]
    [CommRing S] [Algebra S ℂ] (N : ℕ) [NeZero N]
    (h : HeckeOver R N ≤ HeckeOver S N) : HeckeOver R N →+* HeckeOver S N :=
  Subring.inclusion h

/-- Regard the same operator over `S` after proving preservation of its trivial-character forms
over `S`. -/
def HeckeOver.changeCoeff {R S : Type*} [CommRing R] [Algebra R ℂ]
    [CommRing S] [Algebra S ℂ] (N : ℕ) [NeZero N]
    (T : HeckeOver R N)
    (hchar : ∀ k f, f ∈ HeckeRing.GL2.modFormCharSpace k (trivialChar N) →
      T.1 k f ∈ HeckeRing.GL2.modFormCharSpace k (trivialChar N))
    (hT : ∀ k f, f ∈ HeckeRing.GL2.modFormCharSpace k (trivialChar N) →
      ModularForm.isOver S f → ModularForm.isOver S (T.1 k f)) : HeckeOver S N :=
  ⟨T.1, fun k f hf₁ hf₂ => ⟨hchar k f hf₁, hT k f hf₁ hf₂⟩⟩


open UpperHalfPlane
open scoped MatrixGroups PInteger

/-- The localization at a nonzero integer has its canonical algebra map to `ℂ`. -/
noncomputable instance awayComplexAlgebra (p : ℕ) [NeZero p] :
    Algebra (Localization.Away (p : ℤ)) ℂ := by
  letI : Invertible ((p : ℤ) : ℂ) :=
    invertibleOfNonzero (by exact_mod_cast (NeZero.ne p))
  exact (IsLocalization.Away.Intlift ℂ).toAlgebra


-- The Fourier coefficient formula involves large, but terminating, simplification steps.
/-- The Hecke operator `Tₙ` at level `Γ₁(N)`, on the trivial-character subspace.
The coprimality hypothesis is the one required by the Fourier coefficient formula. -/
noncomputable def T_n (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (hn : n.Coprime N := by simp) :
    HeckeOver ℚ N := by
  classical
  refine ⟨fun k => HeckeRing.GL2.heckeT_n (N := N) k n, ?_⟩
  intro k f hfχ hf
  refine ⟨HeckeRing.GL2.heckeT_n_preserves_charSpace k n hn (trivialChar N) hfχ, ?_⟩
  rw [ModularForm.isOver_iff] at hf ⊢
  intro m
  have hpre (r : ℕ) :
      ∃ a : ℚ, algebraMap ℚ ℂ a = (ModularForm.qExp f).coeff r := by
    simpa only [rangeMap, RingHom.mem_range] using (hf r)
  have hcoeff (r : ℕ) :
      algebraMap ℚ ℂ (Classical.choose (hpre r)) = (ModularForm.qExp f).coeff r :=
    Classical.choose_spec (hpre r)
  refine ⟨∑ d ∈ (Nat.gcd m n).divisors,
    (d : ℚ) ^ (k - 1) * Classical.choose (hpre (m * n / (d * d))), ?_⟩
  have hformula := HeckeRing.GL2.fourierCoeff_heckeT_n_period_one
    (N := N) k n hn (trivialChar N) hfχ m
  rw [show (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k n f)).coeff m =
      (qExpansion (1 : ℝ) (HeckeRing.GL2.heckeT_n (N := N) k n f)).coeff m by
        simp [ModularForm.qExp_def]]
  rw [hformula, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hddiv : d ∣ Nat.gcd m n := (Nat.mem_divisors.mp hd).1
  have hdN : Nat.Coprime d N := hn.coprime_dvd_left
    (dvd_trans hddiv (Nat.gcd_dvd_right m n))
  have hc := hcoeff (m * n / (d * d))
  have hc' : algebraMap ℚ ℂ (Classical.choose (hpre (m * n / (d * d)))) =
      (qExpansion (1 : ℝ) f).coeff (m * n / (d * d)) := by
    simpa only [ModularForm.qExp_def,
      ModularForms.strictWidthInfty_Gamma1_mapGL] using hc
  have hpow : algebraMap ℚ ℂ ((d : ℚ) ^ (k - 1)) = (d : ℂ) ^ (k - 1) := by
    simp
  rw [map_mul, hpow, hc']
  simp [trivialChar, hdN]

/-- The Fourier coefficient formula for `T_n` on the trivial-character subspace. -/
theorem T_n_coeff (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
    (hn : n.Coprime N := by simp) (k : ℤ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ HeckeRing.GL2.modFormCharSpace k (trivialChar N)) (m : ℕ) :
    (ModularForm.qExp ((T_n N n hn).1 k f)).coeff m =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (d : ℂ) ^ (k - 1) * (ModularForm.qExp f).coeff (m * n / (d * d)) := by
  change (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k n f)).coeff m = _
  rw [show (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k n f)).coeff m =
      (qExpansion (1 : ℝ) (HeckeRing.GL2.heckeT_n (N := N) k n f)).coeff m by
        simp [ModularForm.qExp_def]]
  rw [HeckeRing.GL2.fourierCoeff_heckeT_n_period_one
    (N := N) k n hn (trivialChar N) hf m]
  apply Finset.sum_congr rfl
  intro d hd
  have hddiv : d ∣ Nat.gcd m n := (Nat.mem_divisors.mp hd).1
  have hdN : Nat.Coprime d N := hn.coprime_dvd_left
    (dvd_trans hddiv (Nat.gcd_dvd_right m n))
  simp [trivialChar, hdN, ModularForm.qExp_def]

/-- The `T_n` coefficient formula for forms with rational coefficients. -/
theorem T_n_modularFormOver_coeff (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
    (hn : n.Coprime N := by simp) (k : ℤ)
    (f : ModularFormOver ℚ ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      HeckeRing.GL2.modFormCharSpace k (trivialChar N)) (m : ℕ) :
    ModularFormOver.coeff ℚ m
        (⟨(T_n N n hn).1 k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
          ((T_n N n hn).2 k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
            hf f.isOver').2⟩ :
          ModularFormOver ℚ ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (d : ℚ) ^ (k - 1) * ModularFormOver.coeff ℚ (m * n / (d * d)) f := by
  rw [ModularFormOver.coeff_eq_iff]
  change ((ModularForm.qExp ((T_n N n hn).1 k
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))).coeff m) = _
  rw [T_n_coeff N n hn k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) hf m]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hpow : algebraMap ℚ ℂ ((d : ℚ) ^ (k - 1)) = (d : ℂ) ^ (k - 1) := by
    simp
  rw [map_mul, hpow, ModularFormOver.map_coeff_eq_qExp]
  simp [ModularForm.qExp_def]


-- The Fourier coefficient formula involves large, but terminating, simplification steps.
/-- The prime Hecke operator `T_p` at level `Γ₁(N)`, viewed over `ℤ[1/p]`,
on the trivial-character subspace. -/
noncomputable def T_p (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    (hpN : Nat.Coprime p N) : HeckeOver (ℤ[1/(p : ℤ)]) N := by
  classical
  refine ⟨fun k => HeckeRing.GL2.heckeT_n (N := N) k p, ?_⟩
  intro k f hfχ hf
  refine ⟨HeckeRing.GL2.heckeT_n_preserves_charSpace k p hpN (trivialChar N) hfχ, ?_⟩
  rw [ModularForm.isOver_iff] at hf ⊢
  intro m
  have hpre (r : ℕ) :
      ∃ a : ℤ[1/(p : ℤ)], algebraMap _ ℂ a = (ModularForm.qExp f).coeff r := by
    simpa only [rangeMap, RingHom.mem_range] using (hf r)
  have hcoeff (r : ℕ) :
      algebraMap _ ℂ (Classical.choose (hpre r)) = (ModularForm.qExp f).coeff r :=
    Classical.choose_spec (hpre r)
  let hu : IsUnit (algebraMap ℤ (ℤ[1/(p : ℤ)]) (p : ℤ)) :=
    IsLocalization.Away.algebraMap_isUnit (p : ℤ)
  let u : (ℤ[1/(p : ℤ)])ˣ := hu.unit
  let φ : ℤ[1/(p : ℤ)] →* ℂ := (algebraMap (ℤ[1/(p : ℤ)]) ℂ).toMonoidHom
  have hu_spec : (u : ℤ[1/(p : ℤ)]) = algebraMap ℤ _ (p : ℤ) := hu.unit_spec
  have hpmap : algebraMap (ℤ[1/(p : ℤ)]) ℂ (u : ℤ[1/(p : ℤ)]) = (p : ℂ) := by
    rw [hu_spec]
    simp
  let uc : ℂˣ := Units.mk0 (p : ℂ) (by exact_mod_cast NeZero.out)
  have hmap : Units.map φ u = uc := by
    ext
    exact hpmap
  have hunitpow :
      algebraMap (ℤ[1/(p : ℤ)]) ℂ
          (((u ^ (k - 1) : (ℤ[1/(p : ℤ)])ˣ) : ℤ[1/(p : ℤ)])) =
        (p : ℂ) ^ (k - 1) := by
    change (Units.map φ (u ^ (k - 1)) : ℂ) = (p : ℂ) ^ (k - 1)
    rw [map_zpow (Units.map φ) u (k - 1), hmap]
    simp [uc]
  let localPow (d : ℕ) : ℤ[1/(p : ℤ)] :=
    if d = 1 then 1 else
      (((u ^ (k - 1) : (ℤ[1/(p : ℤ)])ˣ) : ℤ[1/(p : ℤ)]))
  have hlocalPow (d : ℕ) (hd : d ∣ p) :
      algebraMap (ℤ[1/(p : ℤ)]) ℂ (localPow d) = (d : ℂ) ^ (k - 1) := by
    rcases (Nat.dvd_prime Fact.out).mp hd with hd | hd
    · subst d
      simp [localPow]
    · subst d
      have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
      simp [localPow, hp1, hunitpow]
  have hformula := HeckeRing.GL2.fourierCoeff_heckeT_n_period_one
    (N := N) k p hpN (trivialChar N) hfχ m
  rw [show (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k p f)).coeff m =
      (qExpansion (1 : ℝ) (HeckeRing.GL2.heckeT_n (N := N) k p f)).coeff m by
        simp [ModularForm.qExp_def]]
  refine ⟨∑ d ∈ (Nat.gcd m p).divisors,
    localPow d * Classical.choose (hpre (m * p / (d * d))), ?_⟩
  rw [hformula, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hddiv : d ∣ Nat.gcd m p := (Nat.mem_divisors.mp hd).1
  have hdp : d ∣ p := dvd_trans hddiv (Nat.gcd_dvd_right m p)
  have hdN : Nat.Coprime d N := hpN.coprime_dvd_left hdp
  have hc := hcoeff (m * p / (d * d))
  have hc' : algebraMap _ ℂ (Classical.choose (hpre (m * p / (d * d)))) =
      (qExpansion (1 : ℝ) f).coeff (m * p / (d * d)) := by
    simpa only [ModularForm.qExp_def,
      ModularForms.strictWidthInfty_Gamma1_mapGL] using hc
  rw [map_mul, hlocalPow d hdp, hc']
  simp [trivialChar, hdN]

/-- The Fourier coefficient formula for `T_p` on the trivial-character subspace. -/
theorem T_p_coeff (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    (hpN : Nat.Coprime p N) (k : ℤ)
    (f : ModularForm (Gamma1 N) k)
    (hf : f ∈ HeckeRing.GL2.modFormCharSpace k (trivialChar N)) (m : ℕ) :
    (ModularForm.qExp ((T_p N p hpN).1 k f)).coeff m =
      ∑ d ∈ (Nat.gcd m p).divisors,
        (d : ℂ) ^ (k - 1) * (ModularForm.qExp f).coeff (m * p / (d * d)) := by
  change (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k p f)).coeff m = _
  rw [show (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k p f)).coeff m =
      (qExpansion (1 : ℝ) (HeckeRing.GL2.heckeT_n (N := N) k p f)).coeff m by
        simp [ModularForm.qExp_def]]
  rw [HeckeRing.GL2.fourierCoeff_heckeT_n_period_one
    (N := N) k p hpN (trivialChar N) hf m]
  apply Finset.sum_congr rfl
  intro d hd
  have hddiv : d ∣ Nat.gcd m p := (Nat.mem_divisors.mp hd).1
  have hdN : Nat.Coprime d N := hpN.coprime_dvd_left
    (dvd_trans hddiv (Nat.gcd_dvd_right m p))
  simp [trivialChar, hdN, ModularForm.qExp_def]

/-- The unit represented by `p` in the localization `ℤ[1/p]`. -/
noncomputable def T_p.localUnit (p : ℕ) [NeZero p] : (ℤ[1/(p : ℤ)])ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (p : ℤ)).unit

/-- The factor `d^(k - 1)` for divisors of `p`, represented by a power of the unit `p` in
`ℤ[1/p]`. -/
noncomputable def T_p.coeffFactor (p : ℕ) [NeZero p] (k : ℤ) (d : ℕ) : ℤ[1/(p : ℤ)] :=
  if d = 1 then 1 else
    ((T_p.localUnit p ^ (k - 1) : (ℤ[1/(p : ℤ)])ˣ) : ℤ[1/(p : ℤ)])

/-- The `T_p` coefficient formula for forms with coefficients in `ℤ[1/p]`. -/
theorem T_p_modularFormOver_coeff (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    (hpN : Nat.Coprime p N) (k : ℤ)
    (f : ModularFormOver (ℤ[1/(p : ℤ)]) ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      HeckeRing.GL2.modFormCharSpace k (trivialChar N)) (m : ℕ) :
    ModularFormOver.coeff (ℤ[1/(p : ℤ)]) m
        (⟨(T_p N p hpN).1 k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
          ((T_p N p hpN).2 k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
            hf f.isOver').2⟩ :
          ModularFormOver (ℤ[1/(p : ℤ)]) ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ d ∈ (Nat.gcd m p).divisors,
        T_p.coeffFactor p k d *
          ModularFormOver.coeff (ℤ[1/(p : ℤ)]) (m * p / (d * d)) f := by
  let L := ℤ[1/(p : ℤ)]
  let hu : IsUnit (algebraMap ℤ L (p : ℤ)) :=
    IsLocalization.Away.algebraMap_isUnit (p : ℤ)
  let u : Lˣ := T_p.localUnit p
  rw [ModularFormOver.coeff_eq_iff]
  change ((ModularForm.qExp ((T_p N p hpN).1 k
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))).coeff m) = _
  rw [T_p_coeff N p hpN k (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) hf m,
    map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hddiv : d ∣ Nat.gcd m p := (Nat.mem_divisors.mp hd).1
  have hdp : d ∣ p := dvd_trans hddiv (Nat.gcd_dvd_right m p)
  have hfactor : algebraMap L ℂ (T_p.coeffFactor p k d) = (d : ℂ) ^ (k - 1) := by
    rcases (Nat.dvd_prime Fact.out).mp hdp with hd1 | hdp
    · subst d
      simp [T_p.coeffFactor]
    · subst d
      have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
      have hu_spec : (u : L) = algebraMap ℤ L (p : ℤ) := by
        change (((IsLocalization.Away.algebraMap_isUnit (p : ℤ)).unit : Lˣ) : L) = _
        exact (IsLocalization.Away.algebraMap_isUnit (p : ℤ)).unit_spec
      have hpmap : algebraMap L ℂ (u : L) = (p : ℂ) := by
        rw [hu_spec]
        simp
      let φ : L →* ℂ := (algebraMap L ℂ).toMonoidHom
      let uc : ℂˣ := Units.mk0 (p : ℂ) (by exact_mod_cast NeZero.out)
      have hmap : Units.map φ u = uc := by
        ext
        exact hpmap
      have hunitpow : algebraMap L ℂ ((T_p.localUnit p ^ (k - 1) : Lˣ) : L) =
          (p : ℂ) ^ (k - 1) := by
        change (Units.map φ (T_p.localUnit p ^ (k - 1)) : ℂ) = (p : ℂ) ^ (k - 1)
        rw [map_zpow (Units.map φ) (T_p.localUnit p) (k - 1), hmap]
        simp [uc]
      simp [T_p.coeffFactor, hp1, hunitpow]
  rw [map_mul, hfactor, ModularFormOver.map_coeff_eq_qExp]
  simp [ModularForm.qExp_def]

/-- Coerce the distinguished `p`-th Hecke operator from its `p`-integral form to its
rational form. This coercion is specific to `Tp p`; arbitrary `p`-integral Hecke operators
need not preserve rational coefficients. -/
noncomputable instance T_p.coeToRat (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
  (hpN : Nat.Coprime p N := by simp) :
    CoeDep (HeckeOver (ℤ[1/(p : ℤ)]) N) (T_p N p hpN)
      (HeckeOver ℚ N) where
  coe := T_n N p hpN

/-- The distinguished prime Hecke operator over `ℤ[1/p]` coerces to the rational operator `T_n N
p`. -/
@[simp] theorem coe_T_p (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
  (hpN : Nat.Coprime p N := by simp) :
    ((T_p N p hpN : HeckeOver ℚ N)) = T_n N p hpN := rfl


/-- Regard the distinguished prime Hecke operator over a compatible ring containing `ℤ[1/p]`. -/
noncomputable instance Tp.coeToRing (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    {R : Type*} [CommRing R] [Algebra R ℂ]
    [Algebra (ℤ[1/(p : ℤ)]) R]
    [IsScalarTower (ℤ[1/(p : ℤ)]) R ℂ]
    (hpN : Nat.Coprime p N := by simp) :
    CoeDep (HeckeOver (ℤ[1/(p : ℤ)]) N) (T_p N p hpN) (HeckeOver R N) where
  coe := by
    classical
    refine ⟨fun k => HeckeRing.GL2.heckeT_n (N := N) k p, ?_⟩
    intro k f hfχ hf
    refine ⟨HeckeRing.GL2.heckeT_n_preserves_charSpace k p hpN (trivialChar N) hfχ, ?_⟩
    rw [ModularForm.isOver_iff] at hf ⊢
    intro m
    have hpre (r : ℕ) :
        ∃ a : R, algebraMap R ℂ a = (ModularForm.qExp f).coeff r := by
      simpa only [rangeMap, RingHom.mem_range] using (hf r)
    have hcoeff (r : ℕ) :
        algebraMap R ℂ (Classical.choose (hpre r)) = (ModularForm.qExp f).coeff r :=
      Classical.choose_spec (hpre r)
    let hu : IsUnit (algebraMap ℤ R (p : ℤ)) := by
      convert (IsLocalization.Away.algebraMap_isUnit (p : ℤ)).map
        (algebraMap (ℤ[1/(p : ℤ)]) R) using 1; simp
    let u : Rˣ := hu.unit
    have hu_spec : (u : R) = algebraMap ℤ R (p : ℤ) := hu.unit_spec
    let φ : R →* ℂ := (algebraMap R ℂ).toMonoidHom
    have hpmap : algebraMap R ℂ (u : R) = (p : ℂ) := by
      rw [hu_spec]
      simp
    let uc : ℂˣ := Units.mk0 (p : ℂ) (by exact_mod_cast NeZero.out)
    have hmap : Units.map φ u = uc := by
      ext
      exact hpmap
    have hunitpow :
        algebraMap R ℂ (((u ^ (k - 1) : Rˣ) : R)) = (p : ℂ) ^ (k - 1) := by
      change (Units.map φ (u ^ (k - 1)) : ℂ) = (p : ℂ) ^ (k - 1)
      rw [map_zpow (Units.map φ) u (k - 1), hmap]
      simp [uc]
    let localPow (d : ℕ) : R :=
      if d = 1 then 1 else (((u ^ (k - 1) : Rˣ) : R))
    have hlocalPow (d : ℕ) (hd : d ∣ p) :
        algebraMap R ℂ (localPow d) = (d : ℂ) ^ (k - 1) := by
      rcases (Nat.dvd_prime Fact.out).mp hd with hd | hd
      · subst d
        simp [localPow]
      · subst d
        have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
        simp [localPow, hp1, hunitpow]
    have hformula := HeckeRing.GL2.fourierCoeff_heckeT_n_period_one
      (N := N) k p hpN (trivialChar N) hfχ m
    rw [show (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k p f)).coeff m =
        (qExpansion (1 : ℝ) (HeckeRing.GL2.heckeT_n (N := N) k p f)).coeff m by
          simp [ModularForm.qExp_def]]
    refine ⟨∑ d ∈ (Nat.gcd m p).divisors,
      localPow d * Classical.choose (hpre (m * p / (d * d))), ?_⟩
    rw [hformula, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hddiv : d ∣ Nat.gcd m p := (Nat.mem_divisors.mp hd).1
    have hdp : d ∣ p := dvd_trans hddiv (Nat.gcd_dvd_right m p)
    have hdN : Nat.Coprime d N := hpN.coprime_dvd_left hdp
    have hc := hcoeff (m * p / (d * d))
    have hc' : algebraMap R ℂ (Classical.choose (hpre (m * p / (d * d)))) =
        (qExpansion (1 : ℝ) f).coeff (m * p / (d * d)) := by
      simpa only [ModularForm.qExp_def,
        ModularForms.strictWidthInfty_Gamma1_mapGL] using hc
    rw [map_mul, hlocalPow d hdp, hc']
    simp [trivialChar, hdN]

/-- The rational coercion of the distinguished prime Hecke operator agrees with `T_n N p`. -/
@[simp] theorem coe_Tp (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
  (hpN : Nat.Coprime p N := by simp) :
    ((T_p N p hpN : HeckeOver ℚ N)) = T_n N p hpN := rfl

/-- The rational Hecke operator `T_n` acts on forms over any characteristic-zero field
equipped with an algebra map to `ℂ`. -/
noncomputable instance Tn.coeToField (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
    (K : Type*) [Field K] [CharZero K] [Algebra K ℂ] (hn : n.Coprime N := by simp) :
    CoeDep (HeckeOver ℚ N) (T_n N n hn) (HeckeOver K N) where
  coe := by
    classical
    refine ⟨fun k => HeckeRing.GL2.heckeT_n (N := N) k n, ?_⟩
    intro k f hfχ hf
    refine ⟨HeckeRing.GL2.heckeT_n_preserves_charSpace k n hn (trivialChar N) hfχ, ?_⟩
    rw [ModularForm.isOver_iff] at hf ⊢
    intro m
    have hpre (r : ℕ) :
        ∃ a : K, algebraMap K ℂ a = (ModularForm.qExp f).coeff r := by
      simpa only [rangeMap, RingHom.mem_range] using (hf r)
    have hcoeff (r : ℕ) :
        algebraMap K ℂ (Classical.choose (hpre r)) = (ModularForm.qExp f).coeff r :=
      Classical.choose_spec (hpre r)
    refine ⟨∑ d ∈ (Nat.gcd m n).divisors,
      (d : K) ^ (k - 1) * Classical.choose (hpre (m * n / (d * d))), ?_⟩
    have hformula := HeckeRing.GL2.fourierCoeff_heckeT_n_period_one
      (N := N) k n hn (trivialChar N) hfχ m
    rw [show (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k n f)).coeff m =
        (qExpansion (1 : ℝ) (HeckeRing.GL2.heckeT_n (N := N) k n f)).coeff m by
          simp [ModularForm.qExp_def]]
    rw [hformula, map_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hddiv : d ∣ Nat.gcd m n := (Nat.mem_divisors.mp hd).1
    have hdN : Nat.Coprime d N := hn.coprime_dvd_left
      (dvd_trans hddiv (Nat.gcd_dvd_right m n))
    have hc := hcoeff (m * n / (d * d))
    have hc' : algebraMap K ℂ (Classical.choose (hpre (m * n / (d * d)))) =
        (qExpansion (1 : ℝ) f).coeff (m * n / (d * d)) := by
      simpa only [ModularForm.qExp_def,
        ModularForms.strictWidthInfty_Gamma1_mapGL] using hc
    have hpow : algebraMap K ℂ ((d : K) ^ (k - 1)) = (d : ℂ) ^ (k - 1) := by
      simp
    rw [map_mul, hpow, hc']
    simp [trivialChar, hdN]


end ModularFormOver
