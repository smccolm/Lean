/-
Copyright (c) 2026 Carter Hastings. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carter Hastings
-/

import ModularFormsMod.ModularFormMod.Operators
import ModularFormsMod.ModularFormOver.Hecke

/-!
# Hecke operators after coefficient reduction

An operator in `HeckeOver R N` preserves the trivial-character forms over `R`.
It acts on their reductions if it also preserves the coefficient congruence kernel.
The Fourier formulas prove this extra condition for `T_n` over characteristic-zero
fields, `T_nOfIsUnit` when `n` is invertible in the source ring, and `T_p`
over compatible algebras over `ℤ[1/p]`.

At general level the domain is the submodule `heckeCharSpace` of reduced forms
admitting a trivial-character lift. At level one this is the entire space.
-/

open MatrixGroups CongruenceSubgroup HeckeRing.GL2
open scoped PInteger

noncomputable section

namespace ModularFormOver

variable (R : Type) [CommRing R] [Algebra R ℂ] (N : ℕ) [NeZero N] (k : ℤ)

/-- The forms over `R` in the trivial-character subspace of level `Γ₁(N)`. -/
def heckeCharSpace : Submodule R (ModularFormOver R (Gamma1 N) k) where
  carrier := {f | f.toModularForm ∈ modFormCharSpace k (trivialChar N)}
  zero_mem' := by
    change (0 : ModularForm (Gamma1 N) k) ∈ modFormCharSpace k (trivialChar N)
    exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg
    change f.toModularForm + g.toModularForm ∈ modFormCharSpace k (trivialChar N)
    exact Submodule.add_mem _ hf hg
  smul_mem' := fun a f hf => by
    change a • f.toModularForm ∈ modFormCharSpace k (trivialChar N)
    have hsmul : a • f.toModularForm = (algebraMap R ℂ a) • f.toModularForm := by
      ext z
      simp [Algebra.smul_def]
    rw [hsmul]
    exact Submodule.smul_mem _ _ hf

namespace HeckeOver

variable {R N k}

/-- Restrict a coefficient-preserving Hecke operator to the forms it is known to preserve. -/
def onCharSpace (T : HeckeOver R N) (k : ℤ) :
    Module.End R (heckeCharSpace R N k) where
  toFun f := ⟨⟨T.1 k f.1.toModularForm, (T.2 k _ f.2 f.1.isOver').2⟩,
    (T.2 k _ f.2 f.1.isOver').1⟩
  map_add' f g := by
    apply Subtype.ext
    apply ModularFormOver.ext₂
    intro z
    exact congrArg (fun h : ModularForm (Gamma1 N) k => h z) ((T.1 k).map_add _ _)
  map_smul' a f := by
    apply Subtype.ext
    apply ModularFormOver.ext₂
    intro z
    change ((T.1 k) (a • f.1.toModularForm)) z =
      (a • (T.1 k) f.1.toModularForm) z
    have hsmul (g : ModularForm (Gamma1 N) k) : a • g = (algebraMap R ℂ a) • g := by
      ext w
      simp [Algebra.smul_def]
    rw [hsmul, hsmul]
    exact congrArg (fun h : ModularForm (Gamma1 N) k => h z)
      ((T.1 k).map_smul (algebraMap R ℂ a) f.1.toModularForm)

end HeckeOver
end ModularFormOver

namespace ModularFormMod

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] (r : R →+* S) (N : ℕ) [NeZero N] (k : ℤ)

/-- Reduction restricted to trivial-character lifts, with codomain the full reduced space. -/
def heckeReduction : ModularFormOver.heckeCharSpace R N k →ₗ[R]
    ModularFormMod r (Gamma1 N) k :=
  (ModularFormOver.ReduceLinearMap (r := r)).comp
    (ModularFormOver.heckeCharSpace R N k).subtype

/-- The reduced forms admitting a trivial-character lift. -/
def heckeCharSpace : Submodule R (ModularFormMod r (Gamma1 N) k) :=
  LinearMap.range (heckeReduction r N k)

/-- Reduce a trivial-character lift into the reduced trivial-character submodule. -/
def reduceChar : ModularFormOver.heckeCharSpace R N k →ₗ[R] heckeCharSpace r N k :=
  (heckeReduction r N k).rangeRestrict

@[simp] theorem coe_reduceChar (f : ModularFormOver.heckeCharSpace R N k) :
    (reduceChar r N k f).1 = f.1.Reduce r := rfl

/-- Membership records existence of a trivial-character lift, rather than a choice of lift. -/
theorem mem_heckeCharSpace (f : ModularFormMod r (Gamma1 N) k) :
    f ∈ heckeCharSpace r N k ↔
      ∃ g : ModularFormOver R (Gamma1 N) k,
        g.toModularForm ∈ modFormCharSpace k (ModularFormOver.trivialChar N) ∧
        g.Reduce r = f := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, g.2, hg⟩
  · rintro ⟨g, hg, hgf⟩
    exact ⟨⟨g, hg⟩, hgf⟩

/-- At level one every reduced form has a trivial-character lift. -/
theorem mem_heckeCharSpace_one (f : ModularFormMod r (Gamma1 1) k) :
    f ∈ heckeCharSpace r 1 k := by
  obtain ⟨g, rfl⟩ := f.existsReduce
  refine ⟨⟨g, ?_⟩, rfl⟩
  change g.toModularForm ∈ modFormCharSpace k (ModularFormOver.trivialChar 1)
  rw [mem_modFormCharSpace_iff]
  intro d
  have hd : d = 1 := Subsingleton.elim _ _
  simp [hd, ModularFormOver.trivialChar]

@[simp] theorem heckeCharSpace_one : heckeCharSpace r 1 k = ⊤ := by
  apply top_unique
  intro f _
  exact mem_heckeCharSpace_one _ _ _

end ModularFormMod

namespace ModularFormOver.HeckeOver

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ]
  [CommRing S] {N : ℕ} [NeZero N] {k : ℤ}

/-- The extra condition needed to reduce a general coefficient-preserving operator. -/
abbrev PreservesReduction (T : HeckeOver R N) (r : R →+* S) (k : ℤ) : Prop :=
  ∀ f : heckeCharSpace R N k, f.1.Reduce r = 0 →
    (onCharSpace T k f).1.Reduce r = 0

/-- Reduce a Hecke operator that preserves the coefficient congruence kernel. -/
def reduce (T : HeckeOver R N) (r : R →+* S) (k : ℤ)
    (hT : PreservesReduction T r k) :
    Module.End R (ModularFormMod.heckeCharSpace r N k) := by
  let L := ModularFormMod.heckeReduction r N k
  let e := L.quotKerEquivRange
  have hker : LinearMap.ker L ≤ (LinearMap.ker L).comap (onCharSpace T k) := by
    intro f hf
    exact hT f hf
  exact e.toLinearMap.comp
    (((LinearMap.ker L).mapQ (LinearMap.ker L) (onCharSpace T k) hker).comp
      e.symm.toLinearMap)

/-- The reduced operator agrees with applying the original operator before reduction. -/
@[simp] theorem reduce_reduceChar (T : HeckeOver R N) (r : R →+* S)
    (hT : PreservesReduction T r k) (f : heckeCharSpace R N k) :
    reduce T r k hT (ModularFormMod.reduceChar r N k f) =
      ModularFormMod.reduceChar r N k (onCharSpace T k f) := by
  change (ModularFormMod.heckeReduction r N k).quotKerEquivRange
    ((LinearMap.ker (ModularFormMod.heckeReduction r N k)).mapQ
      (LinearMap.ker (ModularFormMod.heckeReduction r N k)) (onCharSpace T k)
      (fun g hg => hT g hg)
      ((ModularFormMod.heckeReduction r N k).quotKerEquivRange.symm
        ((ModularFormMod.heckeReduction r N k).quotKerEquivRange
          (Submodule.Quotient.mk f)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- Apply the reduced operator to a reduced form with a trivial-character lift. -/
def reduceApply (T : HeckeOver R N) (r : R →+* S) (k : ℤ)
    (hT : PreservesReduction T r k) (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ ModularFormMod.heckeCharSpace r N k := by
      exact ModularFormMod.mem_heckeCharSpace_one _ _ _) :
    ModularFormMod r (Gamma1 N) k :=
  (reduce T r k hT ⟨f, hf⟩).1

/-- At level one the reduced operator is an endomorphism of the full reduced space. -/
def reduceLevelOne (T : HeckeOver R 1) (r : R →+* S) (k : ℤ)
    (hT : PreservesReduction T r k) : Module.End R (ModularFormMod r (Gamma1 1) k) :=
  let e := LinearEquiv.ofTop (ModularFormMod.heckeCharSpace r 1 k)
    (ModularFormMod.heckeCharSpace_one r k)
  e.toLinearMap.comp ((reduce T r k hT).comp e.symm.toLinearMap)

@[simp] theorem reduceApply_Reduce (T : HeckeOver R N) (r : R →+* S)
    (hT : PreservesReduction T r k) (f : heckeCharSpace R N k) :
    reduceApply T r k hT (f.1.Reduce r) ⟨f, rfl⟩ =
      (onCharSpace T k f).1.Reduce r := by
  exact congrArg Subtype.val (reduce_reduceChar T r hT f)

/-- A divisor-sum formula with coefficients in `R` proves preservation of reduction kernels. -/
theorem preservesReduction_of_coeff (T : HeckeOver R N) (r : R →+* S)
    (n : ℕ) (c : ℕ → R)
    (hcoeff : ∀ (f : heckeCharSpace R N k) m,
      coeff R m (onCharSpace T k f).1 =
        ∑ d ∈ (Nat.gcd m n).divisors, c d * coeff R (m * n / (d * d)) f.1) :
    PreservesReduction T r k := by
  intro f hf
  rw [Reduce_eq_zero_iff] at hf ⊢
  intro m
  simp only [hcoeff, map_sum, map_mul, hf, mul_zero, Finset.sum_const_zero]

/-- The divisor-sum formula after descent is independent of the chosen lift. -/
theorem coeff_reduceApply (T : HeckeOver R N) (r : R →+* S)
    (hT : PreservesReduction T r k) (n : ℕ) (c : ℕ → R)
    (hcoeff : ∀ (f : heckeCharSpace R N k) m,
      coeff R m (onCharSpace T k f).1 =
        ∑ d ∈ (Nat.gcd m n).divisors, c d * coeff R (m * n / (d * d)) f.1)
    (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ ModularFormMod.heckeCharSpace r N k) (m : ℕ) :
    ModularFormMod.coeff m (reduceApply T r k hT f hf) =
      ∑ d ∈ (Nat.gcd m n).divisors,
        r (c d) * ModularFormMod.coeff (m * n / (d * d)) f := by
  obtain ⟨g, rfl⟩ := hf
  change ModularFormMod.coeff m (reduceApply T r k hT (g.1.Reduce r) ⟨g, rfl⟩) =
    ∑ d ∈ (Nat.gcd m n).divisors,
      r (c d) * ModularFormMod.coeff (m * n / (d * d)) (g.1.Reduce r)
  rw [reduceApply_Reduce, coeff_Reduce, hcoeff]
  simp only [map_sum, map_mul, coeff_Reduce]

end ModularFormOver.HeckeOver

namespace ModularFormMod

open ModularFormOver.HeckeOver

section GeneralIndex

variable {K S : Type} [Field K] [CharZero K] [Algebra K ℂ] [CommRing S]
  (r : K →+* S) (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
  (hn : n.Coprime N) (k : ℤ)

/-- The divisor-sum formula over any characteristic-zero coefficient field. -/
theorem T_n_lift_coeff (f : ModularFormOver.heckeCharSpace K N k) (m : ℕ) :
    ModularFormOver.coeff K m
        (onCharSpace (ModularFormOver.T_n N n hn : ModularFormOver.HeckeOver K N) k f).1 =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (d : K) ^ (k - 1) * ModularFormOver.coeff K (m * n / (d * d)) f.1 := by
  rw [ModularFormOver.coeff_eq_iff]
  change (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k n f.1.toModularForm)).coeff m = _
  rw [show (HeckeRing.GL2.heckeT_n (N := N) k n f.1.toModularForm) =
    (ModularFormOver.T_n N n hn).1 k f.1.toModularForm from rfl,
    ModularFormOver.T_n_coeff N n hn k _ f.2 m, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hpow : algebraMap K ℂ ((d : K) ^ (k - 1)) = (d : ℂ) ^ (k - 1) := by simp
  rw [_root_.map_mul, hpow, ModularFormOver.map_coeff_eq_qExp]
  rfl

/-- The Fourier formula proves that `T_n` preserves coefficient congruences. -/
theorem T_n_preservesReduction :
    PreservesReduction (ModularFormOver.T_n N n hn : ModularFormOver.HeckeOver K N) r k :=
  preservesReduction_of_coeff _ r n (fun d => (d : K) ^ (k - 1))
    (T_n_lift_coeff N n hn k)

/-- `T_n` on reduced trivial-character forms, linear over the lifting field. -/
def T_nLinearMap : Module.End K (heckeCharSpace r N k) :=
  reduce (ModularFormOver.T_n N n hn : ModularFormOver.HeckeOver K N) r k
    (T_n_preservesReduction r N n hn k)

/-- The reduced Hecke operator `T_n`. The lifting condition is automatic at level one. -/
def T_n (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ heckeCharSpace r N k := by exact mem_heckeCharSpace_one _ _ _) :
    ModularFormMod r (Gamma1 N) k :=
  (T_nLinearMap r N n hn k ⟨f, hf⟩).1

/-- The coefficients of `T_n` are obtained by reducing the classical divisor-sum formula. -/
theorem T_n_coeff (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ heckeCharSpace r N k) (m : ℕ) :
    coeff m (T_n r N n hn k f hf) =
      ∑ d ∈ (Nat.gcd m n).divisors,
        r ((d : K) ^ (k - 1)) * coeff (m * n / (d * d)) f :=
  coeff_reduceApply _ r (T_n_preservesReduction r N n hn k) n
    (fun d => (d : K) ^ (k - 1)) (T_n_lift_coeff N n hn k) f hf m

@[simp] theorem T_n_Reduce (f : ModularFormOver.heckeCharSpace K N k) :
    T_n r N n hn k (f.1.Reduce r) ⟨f, rfl⟩ =
      (onCharSpace (ModularFormOver.T_n N n hn : ModularFormOver.HeckeOver K N) k f).1.Reduce r :=
  reduceApply_Reduce _ r _ f

/-- The first coefficient of `T_n f` is the `n`-th coefficient of `f`. -/
@[simp] theorem T_n_coeff_one (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ heckeCharSpace r N k) :
    coeff 1 (T_n r N n hn k f hf) = coeff n f := by
  simp [T_n_coeff]

/-- Applying `T_n` commutes with further reduction of coefficients. -/
theorem T_n_map {U : Type} [CommRing U] (s : S →+* U)
    (f : ModularFormMod r (Gamma1 N) k) (hf : f ∈ heckeCharSpace r N k) :
    T_n (s.comp r) N n hn k (map s f)
        (by obtain ⟨g, hg⟩ := hf; exact ⟨g, by rw [← hg]; rfl⟩) =
      map s (T_n r N n hn k f hf) := by
  apply ext_coeff
  intro m
  simp only [T_n_coeff, coeff_map, RingHom.comp_apply, map_sum, _root_.map_mul]

end GeneralIndex

section UnitIndex

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] [CommRing S]
  (r : R →+* S) (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
  (hn : n.Coprime N) (hnR : IsUnit (n : R)) (k : ℤ)

/-- A divisor of an invertible index is a unit, so its integer powers make sense in `R`. -/
def heckeCoeffFactor (d : ℕ) : R :=
  if hd : d ∣ n then
    (((isUnit_of_dvd_unit (map_dvd (Nat.castRingHom R) hd) hnR).unit ^
      (k - 1) : Rˣ) : R)
  else 0

omit [FaithfulSMul R ℂ] in
/-- The unit powers used in the divisor sum agree with the complex powers. -/
theorem map_heckeCoeffFactor (d : ℕ) (hd : d ∣ n) :
    algebraMap R ℂ (heckeCoeffFactor n hnR k d) = (d : ℂ) ^ (k - 1) := by
  let u := (isUnit_of_dvd_unit (map_dvd (Nat.castRingHom R) hd) hnR).unit
  have hu : (u : R) = (d : R) := IsUnit.unit_spec _
  let φ := (algebraMap R ℂ).toMonoidHom
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (NeZero.ne n) hd
  let uc : ℂˣ := Units.mk0 (d : ℂ) (by exact_mod_cast hd0)
  have hmap : Units.map φ u = uc := by
    ext
    change algebraMap R ℂ (u : R) = (d : ℂ)
    rw [hu, map_natCast]
  simp only [heckeCoeffFactor, dite_eq_left hd]
  change (Units.map φ (u ^ (k - 1)) : ℂ) = _
  rw [map_zpow, hmap]
  simp [uc]

/-- The classical `T_n` over any faithful coefficient ring in which `n` is invertible.
This includes localizations admitting reduction to positive characteristic. -/
def heckeOverOfIsUnit : ModularFormOver.HeckeOver R N := by
  classical
  refine ⟨fun j => HeckeRing.GL2.heckeT_n (N := N) j n, ?_⟩
  intro j f hfχ hf
  refine ⟨heckeT_n_preserves_charSpace j n hn (ModularFormOver.trivialChar N) hfχ, ?_⟩
  rw [ModularForm.isOver_iff]
  intro m
  refine ⟨∑ d ∈ (Nat.gcd m n).divisors,
    heckeCoeffFactor n hnR j d * hf.fourier.coeff (m * n / (d * d)), ?_⟩
  rw [show HeckeRing.GL2.heckeT_n (N := N) j n f =
    (ModularFormOver.T_n N n hn).1 j f from rfl,
    ModularFormOver.T_n_coeff N n hn j f hfχ m, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn : d ∣ n := dvd_trans (Nat.mem_divisors.mp hd).1 (Nat.gcd_dvd_right m n)
  rw [_root_.map_mul, map_heckeCoeffFactor n hnR j d hdn, hf.map_coeff_fourier]

theorem T_nOfIsUnit_lift_coeff (f : ModularFormOver.heckeCharSpace R N k) (m : ℕ) :
    ModularFormOver.coeff R m (onCharSpace (heckeOverOfIsUnit N n hn hnR) k f).1 =
      ∑ d ∈ (Nat.gcd m n).divisors,
        heckeCoeffFactor n hnR k d * ModularFormOver.coeff R (m * n / (d * d)) f.1 := by
  rw [ModularFormOver.coeff_eq_iff]
  change (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k n f.1.toModularForm)).coeff m = _
  rw [show HeckeRing.GL2.heckeT_n (N := N) k n f.1.toModularForm =
    (ModularFormOver.T_n N n hn).1 k f.1.toModularForm from rfl,
    ModularFormOver.T_n_coeff N n hn k _ f.2 m, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn : d ∣ n := dvd_trans (Nat.mem_divisors.mp hd).1 (Nat.gcd_dvd_right m n)
  rw [_root_.map_mul, map_heckeCoeffFactor n hnR k d hdn,
    ModularFormOver.map_coeff_eq_qExp]
  rfl

/-- `T_n` preserves congruences over rings in which its index is a unit. -/
theorem T_nOfIsUnit_preservesReduction :
    PreservesReduction (heckeOverOfIsUnit N n hn hnR) r k :=
  preservesReduction_of_coeff _ r n (heckeCoeffFactor n hnR k)
    (T_nOfIsUnit_lift_coeff N n hn hnR k)

/-- `T_n` on reductions from a ring in which `n` is invertible. -/
def T_nOfIsUnit (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ heckeCharSpace r N k := by exact mem_heckeCharSpace_one _ _ _) :
    ModularFormMod r (Gamma1 N) k :=
  reduceApply (heckeOverOfIsUnit N n hn hnR) r k
    (T_nOfIsUnit_preservesReduction r N n hn hnR k) f hf

/-- The general divisor formula over arbitrary reduction targets, including finite rings. -/
theorem T_nOfIsUnit_coeff (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ heckeCharSpace r N k) (m : ℕ) :
    coeff m (T_nOfIsUnit r N n hn hnR k f hf) =
      ∑ d ∈ (Nat.gcd m n).divisors,
        r (heckeCoeffFactor n hnR k d) * coeff (m * n / (d * d)) f :=
  coeff_reduceApply _ r (T_nOfIsUnit_preservesReduction r N n hn hnR k) n
    (heckeCoeffFactor n hnR k) (T_nOfIsUnit_lift_coeff N n hn hnR k) f hf m

/-- In weights at least one, the divisor factors are ordinary natural powers. -/
theorem T_nOfIsUnit_coeff_of_one_le (hk : 1 ≤ k)
    (f : ModularFormMod r (Gamma1 N) k) (hf : f ∈ heckeCharSpace r N k) (m : ℕ) :
    coeff m (T_nOfIsUnit r N n hn hnR k f hf) =
      ∑ d ∈ (Nat.gcd m n).divisors,
        (d : S) ^ (k - 1).toNat * coeff (m * n / (d * d)) f := by
  rw [T_nOfIsUnit_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  have hdn : d ∣ n := dvd_trans (Nat.mem_divisors.mp hd).1 (Nat.gcd_dvd_right m n)
  have hfactor : heckeCoeffFactor n hnR k d = (d : R) ^ (k - 1).toNat := by
    simp only [heckeCoeffFactor, dite_eq_left hdn]
    have hk' : k - 1 = ((k - 1).toNat : ℤ) := by omega
    conv_lhs => rw [hk', zpow_natCast]
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rfl
  rw [hfactor, _root_.map_pow, map_natCast]

/-- The unit-index construction is compatible with further coefficient reduction. -/
theorem T_nOfIsUnit_map {U : Type} [CommRing U] (s : S →+* U)
    (f : ModularFormMod r (Gamma1 N) k) (hf : f ∈ heckeCharSpace r N k) :
    T_nOfIsUnit (s.comp r) N n hn hnR k (map s f)
        (by obtain ⟨g, hg⟩ := hf; exact ⟨g, by rw [← hg]; rfl⟩) =
      map s (T_nOfIsUnit r N n hn hnR k f hf) := by
  apply ext_coeff
  intro m
  simp only [T_nOfIsUnit_coeff, coeff_map, RingHom.comp_apply, map_sum, _root_.map_mul]

end UnitIndex

section PrimeIndex

variable {R S : Type} [CommRing R] [Algebra R ℂ] [FaithfulSMul R ℂ] [CommRing S]
  (r : R →+* S) (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
  [Algebra (ℤ[1/(p : ℤ)]) R] [IsScalarTower (ℤ[1/(p : ℤ)]) R ℂ]
  (hpN : p.Coprime N) (k : ℤ)

set_option maxHeartbeats 1000000 in
-- Comparing powers in the localization and in `ℂ` unfolds the localization algebra instances.
/-- The localized factor in the prime coefficient formula maps to the complex power. -/
theorem T_p_map_coeffFactor (d : ℕ) (hd : d ∣ p) :
    algebraMap (ℤ[1/(p : ℤ)]) ℂ (ModularFormOver.T_p.coeffFactor p k d) =
      (d : ℂ) ^ (k - 1) := by
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hd with hd | hd
  · subst d
    simp [ModularFormOver.T_p.coeffFactor]
  · subst d
    have hp1 : p ≠ 1 := (Fact.out : p.Prime).ne_one
    let u := ModularFormOver.T_p.localUnit p
    let φ := (algebraMap (ℤ[1/(p : ℤ)]) ℂ).toMonoidHom
    let uc : ℂˣ := Units.mk0 (p : ℂ) (by exact_mod_cast (NeZero.ne p))
    have hmap : Units.map φ u = uc := by
      ext
      change algebraMap (ℤ[1/(p : ℤ)]) ℂ
        ((IsLocalization.Away.algebraMap_isUnit (S := ℤ[1/(p : ℤ)])
          (p : ℤ)).unit : ℤ[1/(p : ℤ)]) = _
      rw [IsUnit.unit_spec]
      simp [uc]
    simp only [ModularFormOver.T_p.coeffFactor, ite_eq_right hp1]
    change (Units.map φ (u ^ (k - 1)) : ℂ) = _
    rw [map_zpow, hmap]
    simp [uc]

/-- The prime divisor-sum formula over a compatible algebra over `ℤ[1/p]`. -/
theorem T_p_lift_coeff (f : ModularFormOver.heckeCharSpace R N k) (m : ℕ) :
    ModularFormOver.coeff R m
        (onCharSpace (ModularFormOver.T_p N p hpN : ModularFormOver.HeckeOver R N) k f).1 =
      ∑ d ∈ (Nat.gcd m p).divisors,
        algebraMap (ℤ[1/(p : ℤ)]) R (ModularFormOver.T_p.coeffFactor p k d) *
          ModularFormOver.coeff R (m * p / (d * d)) f.1 := by
  rw [ModularFormOver.coeff_eq_iff]
  change (ModularForm.qExp (HeckeRing.GL2.heckeT_n (N := N) k p f.1.toModularForm)).coeff m = _
  rw [show (HeckeRing.GL2.heckeT_n (N := N) k p f.1.toModularForm) =
    (ModularFormOver.T_p N p hpN).1 k f.1.toModularForm from rfl,
    ModularFormOver.T_p_coeff N p hpN k _ f.2 m, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp : d ∣ p := dvd_trans (Nat.mem_divisors.mp hd).1 (Nat.gcd_dvd_right m p)
  rw [_root_.map_mul, ← IsScalarTower.algebraMap_apply,
    T_p_map_coeffFactor p k d hdp, ModularFormOver.map_coeff_eq_qExp]
  rfl

/-- The prime Fourier formula proves preservation of coefficient congruences. -/
theorem T_p_preservesReduction :
    PreservesReduction (ModularFormOver.T_p N p hpN : ModularFormOver.HeckeOver R N) r k :=
  preservesReduction_of_coeff _ r p
    (fun d => algebraMap (ℤ[1/(p : ℤ)]) R (ModularFormOver.T_p.coeffFactor p k d))
    (T_p_lift_coeff N p hpN k)

/-- `T_p` on reduced trivial-character forms, linear over the lifting ring. -/
def T_pLinearMap : Module.End R (heckeCharSpace r N k) :=
  reduce (ModularFormOver.T_p N p hpN : ModularFormOver.HeckeOver R N) r k
    (T_p_preservesReduction r N p hpN k)

/-- The reduced prime Hecke operator over an algebra over `ℤ[1/p]`. -/
def T_p (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ heckeCharSpace r N k := by exact mem_heckeCharSpace_one _ _ _) :
    ModularFormMod r (Gamma1 N) k :=
  (T_pLinearMap r N p hpN k ⟨f, hf⟩).1

/-- The prime coefficient formula works over arbitrary target rings; its powers come
from the unit `p` in the lifting localization. -/
theorem T_p_coeff (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ heckeCharSpace r N k) (m : ℕ) :
    coeff m (T_p r N p hpN k f hf) =
      ∑ d ∈ (Nat.gcd m p).divisors,
        r (algebraMap (ℤ[1/(p : ℤ)]) R (ModularFormOver.T_p.coeffFactor p k d)) *
          coeff (m * p / (d * d)) f :=
  coeff_reduceApply _ r (T_p_preservesReduction r N p hpN k) p
    (fun d => algebraMap (ℤ[1/(p : ℤ)]) R (ModularFormOver.T_p.coeffFactor p k d))
    (T_p_lift_coeff N p hpN k) f hf m

/-- In weights at least one the prime formula uses ordinary powers in the target ring. -/
theorem T_p_coeff_of_one_le (hk : 1 ≤ k)
    (f : ModularFormMod r (Gamma1 N) k) (hf : f ∈ heckeCharSpace r N k) (m : ℕ) :
    coeff m (T_p r N p hpN k f hf) =
      ∑ d ∈ (Nat.gcd m p).divisors,
        (d : S) ^ (k - 1).toNat * coeff (m * p / (d * d)) f := by
  rw [T_p_coeff]
  apply Finset.sum_congr rfl
  intro d hd
  have hdp : d ∣ p := dvd_trans (Nat.mem_divisors.mp hd).1 (Nat.gcd_dvd_right m p)
  have hfactor : algebraMap (ℤ[1/(p : ℤ)]) R (ModularFormOver.T_p.coeffFactor p k d) =
      (d : R) ^ (k - 1).toNat := by
    apply FaithfulSMul.algebraMap_injective R ℂ
    rw [← IsScalarTower.algebraMap_apply, T_p_map_coeffFactor p k d hdp]
    have hk' : k - 1 = ((k - 1).toNat : ℤ) := by omega
    conv_lhs => rw [hk', zpow_natCast]
    simp only [_root_.map_pow, map_natCast]
  rw [hfactor, _root_.map_pow, map_natCast]

@[simp] theorem T_p_Reduce (f : ModularFormOver.heckeCharSpace R N k) :
    T_p r N p hpN k (f.1.Reduce r) ⟨f, rfl⟩ =
      (onCharSpace (ModularFormOver.T_p N p hpN : ModularFormOver.HeckeOver R N) k f).1.Reduce r :=
  reduceApply_Reduce _ r _ f

/-- The first coefficient of `T_p f` is the `p`-th coefficient of `f`. -/
@[simp] theorem T_p_coeff_one (f : ModularFormMod r (Gamma1 N) k)
    (hf : f ∈ heckeCharSpace r N k) :
    coeff 1 (T_p r N p hpN k f hf) = coeff p f := by
  simp [T_p_coeff, ModularFormOver.T_p.coeffFactor]

/-- Applying `T_p` commutes with further coefficient reduction. -/
theorem T_p_map {U : Type} [CommRing U] (s : S →+* U)
    (f : ModularFormMod r (Gamma1 N) k) (hf : f ∈ heckeCharSpace r N k) :
    T_p (s.comp r) N p hpN k (map s f)
        (by obtain ⟨g, hg⟩ := hf; exact ⟨g, by rw [← hg]; rfl⟩) =
      map s (T_p r N p hpN k f hf) := by
  apply ext_coeff
  intro m
  simp only [T_p_coeff, coeff_map, RingHom.comp_apply, map_sum, _root_.map_mul]

end PrimeIndex
end ModularFormMod
