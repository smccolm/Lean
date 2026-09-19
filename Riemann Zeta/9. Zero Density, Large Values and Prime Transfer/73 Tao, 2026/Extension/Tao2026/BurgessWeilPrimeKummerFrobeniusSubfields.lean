import Tao2026.BurgessWeilPrimeKummerNewtonQuinticIntegrality

/-!
# Literal Kummer correlations in a common finite field

Every smaller finite field embeds in an extension whose degree is divisible
by its degree. Its image is exactly a Frobenius fixed locus. Partial products
of Frobenius conjugates recover the smaller-field norm inside this common
ambient field, and hence recover the literal root-multiset character weight.

The resulting fixed-point trace identities are uniform in the extension
degrees. Orbit weights are integral, invariant, and compatible with repeated
periods. They supply the field-theoretic input for an Euler-product proof of
Newton integrality in all degrees.
-/

namespace Tao2026

open Finset
open scoped BigOperators

noncomputable section

theorem finiteField_pow_natCard_fixed_iff
    (K L : Type*) [Field K] [Finite K] [Field L] [Finite L]
    [Algebra K L] (x : L) :
    x ^ Nat.card K = x ↔ ∃ a : K, algebraMap K L a = x := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype L := Fintype.ofFinite L
  let σ := FiniteField.frobeniusAlgEquivOfAlgebraic K L
  have hσ : σ x = x ↔ x ^ Nat.card K = x := by
    simp [σ, Nat.card_eq_fintype_card]
  rw [← hσ]
  constructor
  · intro hx
    apply (IsGalois.mem_range_algebraMap_iff_fixed x).2
    intro g
    obtain ⟨i, rfl⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 g
    have hall (m : ℕ) : (σ ^ m) x = x := by
      induction m with
      | zero => simp
      | succ m hm =>
          rw [pow_succ', AlgEquiv.mul_apply, hm, hx]
    exact hall i.1
  · rintro ⟨a, rfl⟩
    exact σ.commutes a

abbrev primeFieldExtension (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d] :=
  FiniteField.Extension (ZMod p) p d

theorem primeFieldExtension_finrank (p d : ℕ)
    [NeZero p] [Fact p.Prime] [NeZero d] :
    Module.finrank (ZMod p) (primeFieldExtension p d) = d := by
  refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card (ZMod p)) ?_
  simp only [← Module.natCard_eq_pow_finrank, FiniteField.natCard_extension]

def primeFieldExtensionEmbedding (p d n : ℕ)
    [NeZero p] [Fact p.Prime] [NeZero d] [NeZero n]
    (h : d ∣ n) : primeFieldExtension p d →ₐ[ZMod p] primeFieldExtension p n :=
  (FiniteField.nonempty_algHom_of_finrank_dvd (by
    simpa only [primeFieldExtension_finrank] using h)).some

theorem primeFieldExtensionEmbedding_frob_pow
    (p d n : ℕ) [NeZero p] [Fact p.Prime] [NeZero d] [NeZero n]
    (φ : primeFieldExtension p d →ₐ[ZMod p] primeFieldExtension p n)
    (m : ℕ) (y : primeFieldExtension p d) :
    φ ((FiniteField.Extension.frob (ZMod p) p d ^ m) y) =
      (FiniteField.Extension.frob (ZMod p) p n ^ m) (φ y) := by
  simp only [FiniteField.Extension.frob_iterate_apply, map_pow]

theorem primeFieldExtensionEmbedding_fixed_iff
    (p d n : ℕ) [NeZero p] [Fact p.Prime] [NeZero d] [NeZero n]
    (φ : primeFieldExtension p d →ₐ[ZMod p] primeFieldExtension p n)
    (x : primeFieldExtension p n) :
    (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x ↔
      ∃ y : primeFieldExtension p d, φ y = x := by
  letI : Algebra (primeFieldExtension p d) (primeFieldExtension p n) :=
    φ.toRingHom.toAlgebra
  rw [FiniteField.Extension.frob_iterate_apply]
  rw [← FiniteField.natCard_extension (ZMod p) p d]
  exact finiteField_pow_natCard_fixed_iff
    (primeFieldExtension p d) (primeFieldExtension p n) x

theorem primeFieldExtensionEmbedding_norm
    (p d n : ℕ) [NeZero p] [Fact p.Prime] [NeZero d] [NeZero n]
    (φ : primeFieldExtension p d →ₐ[ZMod p] primeFieldExtension p n)
    (y : primeFieldExtension p d) :
    Algebra.norm (ZMod p) (φ y) =
      Algebra.norm (ZMod p) y ^ (n / d) := by
  letI : Algebra (primeFieldExtension p d) (primeFieldExtension p n) :=
    φ.toRingHom.toAlgebra
  letI : IsScalarTower (ZMod p) (primeFieldExtension p d)
      (primeFieldExtension p n) := IsScalarTower.of_algHom φ
  have hrel : Module.finrank (primeFieldExtension p d)
      (primeFieldExtension p n) = n / d := by
    have hmul := Module.finrank_mul_finrank (ZMod p)
      (primeFieldExtension p d) (primeFieldExtension p n)
    rw [primeFieldExtension_finrank, primeFieldExtension_finrank] at hmul
    simpa only [Nat.mul_div_cancel_left _ (NeZero.pos d)] using
      congrArg (fun k : ℕ => k / d) hmul
  rw [← Algebra.norm_norm (R := ZMod p) (S := primeFieldExtension p d)
    (A := primeFieldExtension p n) (a := φ y)]
  rw [show φ y = algebraMap (primeFieldExtension p d)
    (primeFieldExtension p n) y by rfl]
  rw [Algebra.norm_algebraMap, hrel, map_pow]

/-- Product of the first `d` Frobenius conjugates in a common ambient field. -/
def primeFieldFrobeniusProduct (p n d : ℕ)
    [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) : primeFieldExtension p n :=
  ∏ i ∈ Finset.range d, (FiniteField.Extension.frob (ZMod p) p n ^ i) x

theorem primeFieldFrobeniusProduct_fixed
    (p n d : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    FiniteField.Extension.frob (ZMod p) p n
        (primeFieldFrobeniusProduct p n d x) =
      primeFieldFrobeniusProduct p n d x := by
  let σ := FiniteField.Extension.frob (ZMod p) p n
  change σ (∏ i ∈ Finset.range d, (σ ^ i) x) =
    ∏ i ∈ Finset.range d, (σ ^ i) x
  rw [map_prod]
  have hstep (i : ℕ) : σ ((σ ^ i) x) = (σ ^ (i + 1)) x := by
    rw [pow_succ']
    rfl
  simp_rw [hstep]
  cases d with
  | zero => simp
  | succ d =>
      rw [Finset.prod_range_succ, hx, Finset.prod_range_succ']
      simp

theorem primeFieldFrobeniusProduct_mem_base
    (p n d : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    ∃ a : ZMod p, algebraMap (ZMod p) (primeFieldExtension p n) a =
      primeFieldFrobeniusProduct p n d x := by
  apply (finiteField_pow_natCard_fixed_iff (ZMod p) (primeFieldExtension p n) _).1
  simpa only [FiniteField.Extension.frob_apply] using
    primeFieldFrobeniusProduct_fixed p n d x hx

/-- The base-field value of the partial Frobenius norm when it descends;
zero otherwise. All uses of the norm below prove descent explicitly. -/
def primeFieldFrobeniusNorm (p n d : ℕ)
    [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) : ZMod p := by
  classical
  exact if h : ∃ a : ZMod p, algebraMap (ZMod p) (primeFieldExtension p n) a =
      primeFieldFrobeniusProduct p n d x then h.choose else 0

theorem primeFieldFrobeniusNorm_spec
    (p n d : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    algebraMap (ZMod p) (primeFieldExtension p n)
        (primeFieldFrobeniusNorm p n d x) =
      primeFieldFrobeniusProduct p n d x := by
  rw [primeFieldFrobeniusNorm, dif_pos (primeFieldFrobeniusProduct_mem_base p n d x hx)]
  exact (primeFieldFrobeniusProduct_mem_base p n d x hx).choose_spec

theorem primeFieldFrobeniusProduct_embedding
    (p d n m : ℕ) [NeZero p] [Fact p.Prime] [NeZero d] [NeZero n]
    (φ : primeFieldExtension p d →ₐ[ZMod p] primeFieldExtension p n)
    (y : primeFieldExtension p d) :
    primeFieldFrobeniusProduct p n m (φ y) =
      φ (primeFieldFrobeniusProduct p d m y) := by
  simp only [primeFieldFrobeniusProduct, map_prod,
    primeFieldExtensionEmbedding_frob_pow]

theorem primeFieldFrobeniusProduct_full
    (p d : ℕ) [NeZero p] [Fact p.Prime] [NeZero d]
    (y : primeFieldExtension p d) :
    primeFieldFrobeniusProduct p d d y =
      algebraMap (ZMod p) (primeFieldExtension p d) (Algebra.norm (ZMod p) y) := by
  rw [FiniteField.algebraMap_norm_eq_prod_pow, primeFieldExtension_finrank]
  simp only [primeFieldFrobeniusProduct, FiniteField.Extension.frob_iterate_apply]

theorem primeFieldFrobeniusNorm_embedding
    (p d n : ℕ) [NeZero p] [Fact p.Prime] [NeZero d] [NeZero n]
    (φ : primeFieldExtension p d →ₐ[ZMod p] primeFieldExtension p n)
    (y : primeFieldExtension p d) :
    primeFieldFrobeniusNorm p n d (φ y) = Algebra.norm (ZMod p) y := by
  apply (algebraMap (ZMod p) (primeFieldExtension p n)).injective
  rw [primeFieldFrobeniusNorm_spec p n d (φ y)
    ((primeFieldExtensionEmbedding_fixed_iff p d n φ (φ y)).2 ⟨y, rfl⟩)]
  rw [primeFieldFrobeniusProduct_embedding, primeFieldFrobeniusProduct_full,
    φ.commutes]

theorem primeFieldFrob_pow_mul_apply_eq_self
    (p n d k : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    (FiniteField.Extension.frob (ZMod p) p n ^ (d * k)) x = x := by
  let σ := FiniteField.Extension.frob (ZMod p) p n
  change (σ ^ (d * k)) x = x
  rw [pow_mul]
  induction k with
  | zero => simp
  | succ k hk =>
      rw [pow_succ']
      change (σ ^ d) (((σ ^ d) ^ k) x) = x
      rw [hk, hx]

theorem primeFieldFrobeniusProduct_mul
    (p n d k : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    primeFieldFrobeniusProduct p n (d * k) x =
      primeFieldFrobeniusProduct p n d x ^ k := by
  let σ := FiniteField.Extension.frob (ZMod p) p n
  have hfix (j : ℕ) : (σ ^ (d * j)) x = x :=
    primeFieldFrob_pow_mul_apply_eq_self p n d j x hx
  have hshift (j i : ℕ) : (σ ^ (d * j + i)) x = (σ ^ i) x := by
    rw [Nat.add_comm, pow_add]
    change (σ ^ i) ((σ ^ (d * j)) x) = (σ ^ i) x
    rw [hfix]
  change (∏ i ∈ Finset.range (d * k), (σ ^ i) x) =
    (∏ i ∈ Finset.range d, (σ ^ i) x) ^ k
  induction k with
  | zero => simp
  | succ k hk =>
      rw [Nat.mul_succ, Finset.prod_range_add, hk, pow_succ]
      simp only [hshift]

theorem primeFieldFrobeniusNorm_mul
    (p n d k : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    primeFieldFrobeniusNorm p n (d * k) x =
      primeFieldFrobeniusNorm p n d x ^ k := by
  apply (algebraMap (ZMod p) (primeFieldExtension p n)).injective
  rw [map_pow, primeFieldFrobeniusNorm_spec p n d x hx,
    primeFieldFrobeniusNorm_spec p n (d * k) x
      (primeFieldFrob_pow_mul_apply_eq_self p n d k x hx),
    primeFieldFrobeniusProduct_mul]
  exact hx

theorem primeFieldFrob_pow_sub_base
    (p n d : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) (r : ZMod p) :
    (FiniteField.Extension.frob (ZMod p) p n ^ d)
        (x - algebraMap (ZMod p) (primeFieldExtension p n) r) =
      (FiniteField.Extension.frob (ZMod p) p n ^ d) x -
        algebraMap (ZMod p) (primeFieldExtension p n) r := by
  simp only [map_sub, FiniteField.Extension.frob_iterate_apply,
    Nat.card_zmod, ← map_pow, ZMod.pow_card_pow]

/-- The literal root-multiset weight using the norm of a `d`-periodic point
inside one ambient extension. -/
def primeFieldFrobeniusWeight (p n d : ℕ)
    [NeZero p] [Fact p.Prime] [NeZero n]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (x : primeFieldExtension p n) : ℂ :=
  ∏ r ∈ R.toFinset, (χ ^ R.count r)
    (primeFieldFrobeniusNorm p n d
      (x - algebraMap (ZMod p) (primeFieldExtension p n) r))

theorem primeFieldFrobeniusWeight_integral
    (p n d : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (x : primeFieldExtension p n) :
    IsIntegral ℤ (primeFieldFrobeniusWeight p n d χ R x) := by
  unfold primeFieldFrobeniusWeight
  exact IsIntegral.prod _ (fun r _ => isIntegral_finiteFieldMulChar_apply _ _)

theorem primeFieldFrobeniusWeight_embedding
    (p d n : ℕ) [NeZero p] [Fact p.Prime] [NeZero d] [NeZero n]
    (φ : primeFieldExtension p d →ₐ[ZMod p] primeFieldExtension p n)
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (y : primeFieldExtension p d) :
    primeFieldFrobeniusWeight p n d χ R (φ y) =
      ∏ r ∈ R.toFinset,
        (finiteFieldNormLiftMulChar (ZMod p) (primeFieldExtension p d) χ ^
          R.count r) (y - algebraMap (ZMod p) (primeFieldExtension p d) r) := by
  unfold primeFieldFrobeniusWeight
  apply Finset.prod_congr rfl
  intro r _
  rw [show φ y - algebraMap (ZMod p) (primeFieldExtension p n) r =
      φ (y - algebraMap (ZMod p) (primeFieldExtension p d) r) by
    rw [map_sub, φ.commutes]]
  rw [primeFieldFrobeniusNorm_embedding,
    ← map_pow (finiteFieldNormLiftMulChar (ZMod p) (primeFieldExtension p d)),
    finiteFieldNormLiftMulChar_apply]

theorem primeFieldFrobeniusWeight_mul
    (p n d k : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    primeFieldFrobeniusWeight p n (d * k) χ R x =
      primeFieldFrobeniusWeight p n d χ R x ^ k := by
  unfold primeFieldFrobeniusWeight
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro r _
  rw [primeFieldFrobeniusNorm_mul p n d k _ (by
    rw [primeFieldFrob_pow_sub_base, hx]), map_pow]

theorem primeFieldFrobeniusWeight_fixed_sum
    (p d n : ℕ) [NeZero p] [Fact p.Prime] [NeZero d] [NeZero n]
    (hd : d ∣ n) (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    letI : Fintype (primeFieldExtension p d) := Fintype.ofFinite _
    letI : Fintype (primeFieldExtension p n) := Fintype.ofFinite _
    letI : DecidableEq (primeFieldExtension p n) := Classical.decEq _
    (∑ x ∈ Finset.univ.filter
        (fun x : primeFieldExtension p n =>
          (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x),
        primeFieldFrobeniusWeight p n d χ R x) =
      finiteFieldRootMultisetCorrelation (ZMod p) (primeFieldExtension p d)
        (finiteFieldNormLiftMulChar (ZMod p) (primeFieldExtension p d) χ) R := by
  classical
  letI : Fintype (primeFieldExtension p n) := Fintype.ofFinite _
  letI : Fintype (primeFieldExtension p d) := Fintype.ofFinite _
  let φ := primeFieldExtensionEmbedding p d n hd
  unfold finiteFieldRootMultisetCorrelation
  symm
  refine Finset.sum_bij (fun y _ => φ y) ?_ ?_ ?_ ?_
  · intro y _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (primeFieldExtensionEmbedding_fixed_iff p d n φ (φ y)).2 ⟨y, rfl⟩
  · intro y₁ _ y₂ _ h
    exact φ.injective h
  · intro x hx
    obtain ⟨y, hy⟩ := (primeFieldExtensionEmbedding_fixed_iff p d n φ x).1
      (Finset.mem_filter.mp hx).2
    exact ⟨y, Finset.mem_univ _, hy⟩
  · intro y _
    exact (primeFieldFrobeniusWeight_embedding p d n φ χ R y).symm

theorem primeFieldFrob_pow_commute
    (p n d : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n) :
    (FiniteField.Extension.frob (ZMod p) p n ^ d)
        (FiniteField.Extension.frob (ZMod p) p n x) =
      FiniteField.Extension.frob (ZMod p) p n
        ((FiniteField.Extension.frob (ZMod p) p n ^ d) x) := by
  simp only [FiniteField.Extension.frob_iterate_apply,
    FiniteField.Extension.frob_apply, ← pow_mul, Nat.mul_comm]

theorem primeFieldFrobeniusNorm_frob
    (p n d : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    primeFieldFrobeniusNorm p n d
        (FiniteField.Extension.frob (ZMod p) p n x) =
      primeFieldFrobeniusNorm p n d x := by
  have hfix : (FiniteField.Extension.frob (ZMod p) p n ^ d)
      (FiniteField.Extension.frob (ZMod p) p n x) =
        FiniteField.Extension.frob (ZMod p) p n x := by
    rw [primeFieldFrob_pow_commute, hx]
  apply (algebraMap (ZMod p) (primeFieldExtension p n)).injective
  rw [primeFieldFrobeniusNorm_spec p n d _ hfix,
    primeFieldFrobeniusNorm_spec p n d x hx]
  calc
    primeFieldFrobeniusProduct p n d
        (FiniteField.Extension.frob (ZMod p) p n x) =
      FiniteField.Extension.frob (ZMod p) p n
        (primeFieldFrobeniusProduct p n d x) := by
      simp only [primeFieldFrobeniusProduct, map_prod, primeFieldFrob_pow_commute]
    _ = _ := primeFieldFrobeniusProduct_fixed p n d x hx

theorem primeFieldFrobeniusWeight_frob
    (p n d : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p))
    (x : primeFieldExtension p n)
    (hx : (FiniteField.Extension.frob (ZMod p) p n ^ d) x = x) :
    primeFieldFrobeniusWeight p n d χ R
        (FiniteField.Extension.frob (ZMod p) p n x) =
      primeFieldFrobeniusWeight p n d χ R x := by
  unfold primeFieldFrobeniusWeight
  apply Finset.prod_congr rfl
  intro r _
  have hsub := primeFieldFrob_pow_sub_base p n 1 x r
  simp only [pow_one] at hsub
  rw [← hsub, primeFieldFrobeniusNorm_frob p n d _ (by
    rw [primeFieldFrob_pow_sub_base, hx])]

theorem primeFieldFrobeniusNorm_one_algebraMap
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n] (a : ZMod p) :
    primeFieldFrobeniusNorm p n 1
        (algebraMap (ZMod p) (primeFieldExtension p n) a) = a := by
  apply (algebraMap (ZMod p) (primeFieldExtension p n)).injective
  rw [primeFieldFrobeniusNorm_spec p n 1 _ (by
    simp only [FiniteField.Extension.frob_iterate_apply, Nat.card_zmod,
      ← map_pow, ZMod.pow_card_pow])]
  simp only [primeFieldFrobeniusProduct, Finset.prod_range_one,
    pow_zero, AlgEquiv.one_apply]

theorem primeFieldFrobeniusWeight_one_algebraMap
    (p n : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) (a : ZMod p) :
    primeFieldFrobeniusWeight p n 1 χ R
        (algebraMap (ZMod p) (primeFieldExtension p n) a) =
      ∏ r ∈ R.toFinset, (χ ^ R.count r) (a - r) := by
  simp only [primeFieldFrobeniusWeight, ← map_sub,
    primeFieldFrobeniusNorm_one_algebraMap]

theorem primeRootMultisetExtensionCorrelation_eq_fixed_sum
    (p n q : ℕ) [NeZero p] [Fact p.Prime] [NeZero n]
    (hd : q + 1 ∣ n) (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    letI : Fintype (primeFieldExtension p n) := Fintype.ofFinite _
    letI : DecidableEq (primeFieldExtension p n) := Classical.decEq _
    primeRootMultisetExtensionCorrelation p χ R q =
      ∑ x ∈ Finset.univ.filter
        (fun x : primeFieldExtension p n =>
          (FiniteField.Extension.frob (ZMod p) p n ^ (q + 1)) x = x),
        primeFieldFrobeniusWeight p n (q + 1) χ R x := by
  classical
  letI : Fintype (primeFieldExtension p n) := Fintype.ofFinite _
  cases q with
  | zero =>
      unfold primeRootMultisetExtensionCorrelation finiteFieldRootMultisetCorrelation
      refine Finset.sum_bij
        (fun a _ => algebraMap (ZMod p) (primeFieldExtension p n) a) ?_ ?_ ?_ ?_
      · intro a _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp only [FiniteField.Extension.frob_iterate_apply, Nat.card_zmod,
          ← map_pow, ZMod.pow_card_pow]
      · intro a _ b _ hab
        exact (algebraMap (ZMod p) (primeFieldExtension p n)).injective hab
      · intro x hx
        have hfix := (Finset.mem_filter.mp hx).2
        simp only [Nat.zero_add, pow_one, FiniteField.Extension.frob_apply] at hfix
        obtain ⟨a, ha⟩ := (finiteField_pow_natCard_fixed_iff
          (ZMod p) (primeFieldExtension p n) x).1 hfix
        exact ⟨a, Finset.mem_univ _, ha⟩
      · intro a _
        exact (primeFieldFrobeniusWeight_one_algebraMap p n χ R a).symm
  | succ q =>
      exact (primeFieldFrobeniusWeight_fixed_sum p (q + 2) n hd χ R).symm

/-- One factorial-degree ambient field realizes every correlation needed for
the first `m` Newton identities. -/
theorem primeRootMultisetExtensionCorrelation_eq_factorial_fixed_sum
    (p m q : ℕ) [NeZero p] [Fact p.Prime] (hq : q < m)
    (χ : MulChar (ZMod p) ℂ) (R : Multiset (ZMod p)) :
    letI : NeZero m.factorial := ⟨Nat.factorial_ne_zero m⟩
    letI : Fintype (primeFieldExtension p m.factorial) := Fintype.ofFinite _
    letI : DecidableEq (primeFieldExtension p m.factorial) := Classical.decEq _
    primeRootMultisetExtensionCorrelation p χ R q =
      ∑ x ∈ Finset.univ.filter
        (fun x : primeFieldExtension p m.factorial =>
          (FiniteField.Extension.frob (ZMod p) p m.factorial ^ (q + 1)) x = x),
        primeFieldFrobeniusWeight p m.factorial (q + 1) χ R x := by
  letI : NeZero m.factorial := ⟨Nat.factorial_ne_zero m⟩
  exact primeRootMultisetExtensionCorrelation_eq_fixed_sum p m.factorial q
    (Nat.dvd_factorial (Nat.succ_pos q) hq) χ R

end
end Tao2026
