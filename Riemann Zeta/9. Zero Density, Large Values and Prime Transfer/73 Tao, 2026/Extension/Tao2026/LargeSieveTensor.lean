import Tao2026.LargeSieve
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Algebra.Ring.PUnit

/-!
# Tensor Montgomery uncertainty

This file tensorizes the one-modulus uncertainty inequality over an arbitrary
finite list of nonzero moduli.  The resulting Fourier energy is restricted to
frequencies whose coordinate is nonzero for every modulus, and the lower
bound is the product of the removed/allowed residue ratios.  This is the
analytic heart of Tao's Lemma 2.6, stated on the CRT product cube; the
pairwise-coprime CRT reindexing to one cyclic denominator is kept as the next
separate arithmetic layer.
-/

open Finset
open scoped BigOperators

namespace Tao2026

/-- A natural modulus packaged with the nonzero hypothesis required by its
finite `ZMod` residue space. -/
structure SieveModulus where
  modulus : ℕ
  ne_zero : modulus ≠ 0

instance (q : SieveModulus) : NeZero q.modulus := ⟨q.ne_zero⟩

/-- Product residue space associated to a list of moduli. -/
def SieveCube : List SieveModulus → Type
  | [] => PUnit
  | q :: qs => ZMod q.modulus × SieveCube qs

instance sieveCubeFintype : ∀ qs, Fintype (SieveCube qs)
  | [] => by change Fintype PUnit; infer_instance
  | _ :: qs => by
      change Fintype (ZMod _ × SieveCube qs)
      letI := sieveCubeFintype qs
      infer_instance

noncomputable instance sieveCubeDecidableEq :
    ∀ qs, DecidableEq (SieveCube qs)
  | [] => by change DecidableEq PUnit; infer_instance
  | _ :: qs => by
      change DecidableEq (ZMod _ × SieveCube qs)
      letI := sieveCubeDecidableEq qs
      infer_instance

instance sieveCubeAddCommGroup : ∀ qs, AddCommGroup (SieveCube qs)
  | [] => by change AddCommGroup PUnit; infer_instance
  | _ :: qs => by
      change AddCommGroup (ZMod _ × SieveCube qs)
      letI := sieveCubeAddCommGroup qs
      infer_instance

/-- One finite set of removed residue classes for every modulus. -/
def SieveRestrictions : List SieveModulus → Type
  | [] => PUnit
  | q :: qs => Finset (ZMod q.modulus) × SieveRestrictions qs

/-- A residue tuple avoids every removed set. -/
def SieveAvoids : ∀ {qs}, SieveRestrictions qs → SieveCube qs → Prop
  | [], _, _ => True
  | _ :: _, R, x => x.1 ∉ R.1 ∧ SieveAvoids R.2 x.2

/-- Every removed set is a proper subset of its residue space. -/
def SieveRestrictionsProper : ∀ {qs}, SieveRestrictions qs → Prop
  | [], _ => True
  | q :: _, R => R.1.card < q.modulus ∧ SieveRestrictionsProper R.2

/-- Product of the removed/allowed cardinality ratios. -/
noncomputable def sieveRestrictionRatio :
    ∀ {qs}, SieveRestrictions qs → ℝ
  | [], _ => 1
  | _ :: _, R =>
      (R.1.card : ℝ) / (R.1ᶜ.card : ℝ) * sieveRestrictionRatio R.2

/-- Iterated unnormalised DFT on a product residue cube. -/
noncomputable def tensorDft :
    ∀ qs, (SieveCube qs → ℂ) → SieveCube qs → ℂ
  | [], Φ, _ => Φ PUnit.unit
  | _q :: qs, Φ, ξ =>
      tensorDft qs (fun y => ZMod.dft (fun x => Φ (x, y)) ξ.1) ξ.2

/-- A tensor frequency is admissible when every coordinate is nonzero. -/
def TensorFrequencyNonzero : ∀ {qs}, SieveCube qs → Prop
  | [], _ => True
  | _ :: _, ξ => ξ.1 ≠ 0 ∧ TensorFrequencyNonzero ξ.2

/-- Finite set of tensor frequencies nonzero in every coordinate. -/
noncomputable def tensorNonzeroFrequencies
    (qs : List SieveModulus) : Finset (SieveCube qs) := by
  classical
  exact Finset.univ.filter TensorFrequencyNonzero

/-! ## Pairwise-coprime CRT reindexing -/

/-- Product of a list of packaged moduli. -/
def sieveModulusProduct (qs : List SieveModulus) : ℕ :=
  (qs.map SieveModulus.modulus).prod

theorem sieveModulusProduct_ne_zero :
    ∀ qs, sieveModulusProduct qs ≠ 0
  | [] => by simp [sieveModulusProduct]
  | q :: qs => by
      rw [sieveModulusProduct]
      simp only [List.map_cons, List.prod_cons]
      exact Nat.mul_ne_zero q.ne_zero (sieveModulusProduct_ne_zero qs)

instance sieveModulusProductNeZero (qs : List SieveModulus) :
    NeZero (sieveModulusProduct qs) :=
  ⟨sieveModulusProduct_ne_zero qs⟩

theorem pairwise_head_coprime_sieveModulusProduct
    {q : SieveModulus} {qs : List SieveModulus}
    (hpair : (q :: qs).Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus)) :
    q.modulus.Coprime (sieveModulusProduct qs) := by
  rw [sieveModulusProduct, Nat.coprime_list_prod_right_iff]
  intro m hm
  rw [List.mem_map] at hm
  rcases hm with ⟨r, hr, rfl⟩
  exact (List.pairwise_cons.mp hpair).1 r hr

/-- Iterated Chinese-remainder equivalence from the cyclic residue space
modulo the product to the tensor residue cube. -/
noncomputable def sieveCrtEquiv :
    ∀ (qs : List SieveModulus),
      qs.Pairwise (Function.onFun Nat.Coprime SieveModulus.modulus) →
      ZMod (sieveModulusProduct qs) ≃ SieveCube qs
  | [], _ => by
      change ZMod 1 ≃ PUnit
      exact Equiv.ofUnique _ _
  | q :: qs, hpair => by
      have hhead : q.modulus.Coprime (sieveModulusProduct qs) := by
        rw [sieveModulusProduct, Nat.coprime_list_prod_right_iff]
        intro n hn
        rw [List.mem_map] at hn
        rcases hn with ⟨r, hr, rfl⟩
        exact (List.pairwise_cons.mp hpair).1 r hr
      exact (ZMod.chineseRemainder hhead).toEquiv.trans
        (Equiv.prodCongr (Equiv.refl _)
          (sieveCrtEquiv qs (List.pairwise_cons.mp hpair).2))

/-- Additive form of the iterated Chinese-remainder equivalence. -/
noncomputable def sieveCrtAddEquiv :
    ∀ (qs : List SieveModulus),
      qs.Pairwise (Function.onFun Nat.Coprime SieveModulus.modulus) →
      ZMod (sieveModulusProduct qs) ≃+ SieveCube qs
  | [], _ => by
      change ZMod 1 ≃+ PUnit
      exact
        { toFun := fun _ => PUnit.unit
          invFun := fun _ => 0
          left_inv := fun _ => Subsingleton.elim _ _
          right_inv := fun _ => Subsingleton.elim _ _
          map_add' := fun _ _ => Subsingleton.elim _ _ }
  | q :: qs, hpair =>
      (ZMod.chineseRemainder
          (pairwise_head_coprime_sieveModulusProduct hpair)).toAddEquiv.trans
        (AddEquiv.prodCongr (AddEquiv.refl _)
          (sieveCrtAddEquiv qs (List.pairwise_cons.mp hpair).2))

/-- Nonzero tensor frequencies split as the product of the nonzero head
frequencies and the nonzero tail frequencies. -/
theorem tensorNonzeroFrequencies_cons
    (q : SieveModulus) (qs : List SieveModulus) :
    tensorNonzeroFrequencies (q :: qs) =
      (Finset.univ.erase (0 : ZMod q.modulus)).product
        (tensorNonzeroFrequencies qs) := by
  classical
  ext ξ
  simp only [tensorNonzeroFrequencies, TensorFrequencyNonzero,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact Finset.mem_product.mpr
      ⟨Finset.mem_erase.mpr ⟨h.1, Finset.mem_univ _⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩⟩
  · intro h
    have hp := Finset.mem_product.mp h
    exact ⟨(Finset.mem_erase.mp hp.1).1,
      (Finset.mem_filter.mp hp.2).2⟩

/-- A head-coordinate DFT commutes with summation over an arbitrary finite
tail space. -/
theorem sum_headDft
    {q : SieveModulus} {β : Type*} [Fintype β]
    (Φ : ZMod q.modulus → β → ℂ) (k : ZMod q.modulus) :
    ∑ y : β, ZMod.dft (fun x => Φ x y) k =
      ZMod.dft (fun x => ∑ y : β, Φ x y) k := by
  simp only [ZMod.dft_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]

/-- Every tensor restriction ratio is nonnegative. -/
theorem sieveRestrictionRatio_nonneg :
    ∀ (qs : List SieveModulus) (R : SieveRestrictions qs),
      0 ≤ sieveRestrictionRatio R
  | [], R => by rcases R with ⟨⟩; simp [sieveRestrictionRatio]
  | _ :: qs, R => by
      change 0 ≤ (R.1.card : ℝ) / (R.1ᶜ.card : ℝ) *
        sieveRestrictionRatio R.2
      exact mul_nonneg
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (sieveRestrictionRatio_nonneg qs R.2)

/-- Arbitrary finite tensor form of Montgomery's uncertainty principle.
If `Φ` vanishes outside the tuples avoiding all removed classes, the Fourier
energy where every coordinate is nonzero dominates the zero-frequency mass
by the product of all removed/allowed ratios. -/
theorem montgomery_uncertainty_tensor :
    ∀ (qs : List SieveModulus) (R : SieveRestrictions qs)
      (Φ : SieveCube qs → ℂ),
      SieveRestrictionsProper R →
      (∀ x, ¬ SieveAvoids R x → Φ x = 0) →
      sieveRestrictionRatio R *
          Complex.normSq (∑ x : SieveCube qs, Φ x) ≤
        ∑ ξ ∈ tensorNonzeroFrequencies qs,
          Complex.normSq (tensorDft qs Φ ξ)
  | [], R, Φ, _hproper, _hzero => by
      rcases R with ⟨⟩
      have hsum : (∑ x : SieveCube [], Φ x) = Φ PUnit.unit := by
        change (∑ x : PUnit, Φ x) = Φ PUnit.unit
        simp
      have hfreq : tensorNonzeroFrequencies [] =
          ({(show SieveCube [] from PUnit.unit)} : Finset (SieveCube [])) := by
        ext x
        cases x
        simp [tensorNonzeroFrequencies, TensorFrequencyNonzero]
      rw [hsum, hfreq, Finset.sum_singleton]
      change 1 * Complex.normSq (Φ PUnit.unit) ≤
        Complex.normSq (Φ PUnit.unit)
      simp
  | q :: qs, R, Φ, hproper, hzero => by
      let G : ZMod q.modulus → SieveCube qs → ℂ := fun k y =>
        ZMod.dft (fun x => Φ (x, y)) k
      have hheadZero :
          ∀ x ∈ R.1, (∑ y : SieveCube qs, Φ (x, y)) = 0 := by
        intro x hx
        exact Finset.sum_eq_zero fun y _ => hzero (x, y) (by
          intro havoid
          exact havoid.1 hx)
      have hhead := montgomery_uncertainty_one R.1
        (fun x => ∑ y : SieveCube qs, Φ (x, y)) hproper.1 hheadZero
      have htail (k : ZMod q.modulus) :
          sieveRestrictionRatio R.2 *
              Complex.normSq (∑ y : SieveCube qs, G k y) ≤
            ∑ ξ ∈ tensorNonzeroFrequencies qs,
              Complex.normSq (tensorDft qs (G k) ξ) := by
        apply montgomery_uncertainty_tensor qs R.2 (G k) hproper.2
        intro y hy
        unfold G
        simp only [ZMod.dft_apply, smul_eq_mul]
        exact Finset.sum_eq_zero fun x _ => by
          rw [hzero (x, y) (by
            intro havoid
            exact hy havoid.2), mul_zero]
      have hsumTail :
          sieveRestrictionRatio R.2 *
              (∑ k ∈ (Finset.univ.erase (0 : ZMod q.modulus)),
                Complex.normSq (∑ y : SieveCube qs, G k y)) ≤
            ∑ k ∈ (Finset.univ.erase (0 : ZMod q.modulus)),
              ∑ ξ ∈ tensorNonzeroFrequencies qs,
                Complex.normSq (tensorDft qs (G k) ξ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun k _ => htail k
      have hratioTail : 0 ≤ sieveRestrictionRatio R.2 :=
        sieveRestrictionRatio_nonneg qs R.2
      change
        ((R.1.card : ℝ) / (R.1ᶜ.card : ℝ) *
            sieveRestrictionRatio R.2) *
            Complex.normSq
              (∑ x : ZMod q.modulus × SieveCube qs, Φ x) ≤ _
      rw [Fintype.sum_prod_type]
      calc
        ((R.1.card : ℝ) / (R.1ᶜ.card : ℝ) *
            sieveRestrictionRatio R.2) *
            Complex.normSq
              (∑ x : ZMod q.modulus,
                ∑ y : SieveCube qs, Φ (x, y)) =
          sieveRestrictionRatio R.2 *
            (((R.1.card : ℝ) / (R.1ᶜ.card : ℝ)) *
              Complex.normSq
                (∑ x : ZMod q.modulus,
                  ∑ y : SieveCube qs, Φ (x, y))) := by ring
        _ ≤ sieveRestrictionRatio R.2 *
            (∑ k ∈ (Finset.univ.erase (0 : ZMod q.modulus)),
              Complex.normSq (∑ y : SieveCube qs, G k y)) := by
          apply mul_le_mul_of_nonneg_left
          · simpa only [G, sum_headDft] using hhead
          · exact hratioTail
        _ ≤ ∑ k ∈ (Finset.univ.erase (0 : ZMod q.modulus)),
              ∑ ξ ∈ tensorNonzeroFrequencies qs,
                Complex.normSq (tensorDft qs (G k) ξ) := hsumTail
        _ = ∑ ξ ∈ tensorNonzeroFrequencies (q :: qs),
              Complex.normSq (tensorDft (q :: qs) Φ ξ) := by
          rw [tensorNonzeroFrequencies_cons]
          symm
          calc
            ∑ ξ ∈ (Finset.univ.erase (0 : ZMod q.modulus)).product
                (tensorNonzeroFrequencies qs),
                Complex.normSq (tensorDft (q :: qs) Φ ξ) =
              ∑ k ∈ (Finset.univ.erase (0 : ZMod q.modulus)),
                ∑ ξ ∈ tensorNonzeroFrequencies qs,
                  Complex.normSq
                    (tensorDft (q :: qs) Φ (k, ξ)) :=
              Finset.sum_product _ _ _
            _ = _ := rfl

/-- The simultaneous residue-class coordinate of a natural number. -/
def natSieveCube : ∀ (qs : List SieveModulus), ℕ → SieveCube qs
  | [], _ => PUnit.unit
  | q :: qs, n => ((n : ZMod q.modulus), natSieveCube qs n)

/-- Aggregate a finitely supported sequence over simultaneous residue classes. -/
noncomputable def tensorResidueClassSum (qs : List SieveModulus)
    (s : Finset ℕ) (f : ℕ → ℂ) (x : SieveCube qs) : ℂ :=
  (s.filter fun n => natSieveCube qs n = x).sum f

theorem sum_tensorResidueClassSum (qs : List SieveModulus)
    (s : Finset ℕ) (f : ℕ → ℂ) :
    ∑ x : SieveCube qs, tensorResidueClassSum qs s f x =
      ∑ n ∈ s, f n := by
  unfold tensorResidueClassSum
  exact Finset.sum_fiberwise_of_maps_to
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) f

theorem tensorResidueClassSum_eq_zero
    {qs : List SieveModulus} {R : SieveRestrictions qs}
    {s : Finset ℕ} {f : ℕ → ℂ}
    (hzero : ∀ n ∈ s, ¬ SieveAvoids R (natSieveCube qs n) → f n = 0) :
    ∀ x, ¬ SieveAvoids R x → tensorResidueClassSum qs s f x = 0 := by
  intro x hx
  unfold tensorResidueClassSum
  apply Finset.sum_eq_zero
  intro n hn
  apply hzero n (Finset.mem_filter.mp hn).1
  intro hnAvoid
  apply hx
  simpa only [(Finset.mem_filter.mp hn).2] using hnAvoid

/-- Finite-support tensor form of Montgomery's uncertainty inequality. -/
theorem montgomery_uncertainty_tensor_finite
    (qs : List SieveModulus) (R : SieveRestrictions qs)
    (s : Finset ℕ) (f : ℕ → ℂ)
    (hproper : SieveRestrictionsProper R)
    (hzero : ∀ n ∈ s, ¬ SieveAvoids R (natSieveCube qs n) → f n = 0) :
    sieveRestrictionRatio R * Complex.normSq (∑ n ∈ s, f n) ≤
      ∑ ξ ∈ tensorNonzeroFrequencies qs,
        Complex.normSq
          (tensorDft qs (tensorResidueClassSum qs s f) ξ) := by
  simpa only [sum_tensorResidueClassSum] using
    montgomery_uncertainty_tensor qs R (tensorResidueClassSum qs s f)
      hproper (tensorResidueClassSum_eq_zero hzero)

/-! ## CRT reindexing of the tensor Fourier energy -/

/-- The additive CRT map sends a natural number to its simultaneous residue
tuple. -/
theorem sieveCrtAddEquiv_natCast :
    ∀ (qs : List SieveModulus)
      (hpair : qs.Pairwise
        (Function.onFun Nat.Coprime SieveModulus.modulus)) (n : ℕ),
      sieveCrtAddEquiv qs hpair (n : ZMod (sieveModulusProduct qs)) =
        natSieveCube qs n
  | [], _, n => by change PUnit.unit = PUnit.unit; rfl
  | q :: qs, hpair, n => by
      rw [show sieveCrtAddEquiv (q :: qs) hpair =
          (ZMod.chineseRemainder
            (pairwise_head_coprime_sieveModulusProduct hpair)).toAddEquiv.trans
            (AddEquiv.prodCongr (AddEquiv.refl _)
              (sieveCrtAddEquiv qs (List.pairwise_cons.mp hpair).2)) by rfl]
      change
        (AddEquiv.prodCongr (AddEquiv.refl (ZMod q.modulus))
          (sieveCrtAddEquiv qs (List.pairwise_cons.mp hpair).2))
            ((ZMod.chineseRemainder
              (pairwise_head_coprime_sieveModulusProduct hpair))
                (n : ZMod (q.modulus * sieveModulusProduct qs))) =
          ((n : ZMod q.modulus), natSieveCube qs n)
      have hnat :
          (ZMod.chineseRemainder
            (pairwise_head_coprime_sieveModulusProduct hpair))
              (n : ZMod (q.modulus * sieveModulusProduct qs)) =
            ((n : ZMod q.modulus),
              (n : ZMod (sieveModulusProduct qs))) := by
        exact map_natCast _ n
      rw [hnat]
      change ((n : ZMod q.modulus),
          sieveCrtAddEquiv qs (List.pairwise_cons.mp hpair).2
            (n : ZMod (sieveModulusProduct qs))) =
        ((n : ZMod q.modulus), natSieveCube qs n)
      rw [sieveCrtAddEquiv_natCast]

/-- The additive character occurring in the tensor DFT at a given tensor
frequency. -/
noncomputable def tensorDftChar :
    ∀ (qs : List SieveModulus), SieveCube qs → AddChar (SieveCube qs) ℂ
  | [], _ => 1
  | q :: qs, ξ =>
      ((ZMod.stdAddChar.mulShift (-ξ.1)).compAddMonoidHom
        (AddMonoidHom.fst (ZMod q.modulus) (SieveCube qs))) *
      ((tensorDftChar qs ξ.2).compAddMonoidHom
        (AddMonoidHom.snd (ZMod q.modulus) (SieveCube qs)))

/-- Expansion of the iterated DFT against its tensor additive character. -/
theorem tensorDft_eq_sum_char :
    ∀ (qs : List SieveModulus) (Φ : SieveCube qs → ℂ)
      (ξ : SieveCube qs),
      tensorDft qs Φ ξ =
        ∑ x : SieveCube qs, tensorDftChar qs ξ x * Φ x
  | [], Φ, ξ => by
      change Φ PUnit.unit = ∑ x : PUnit, (1 : ℂ) * Φ x
      simp
  | q :: qs, Φ, ξ => by
      rw [tensorDft]
      rw [tensorDft_eq_sum_char]
      simp only [ZMod.dft_apply, smul_eq_mul]
      simp only [tensorDftChar]
      change
        (∑ y : SieveCube qs, (tensorDftChar qs ξ.2) y *
          ∑ x : ZMod q.modulus,
            ZMod.stdAddChar (-(x * ξ.1)) * Φ (x, y)) =
        ∑ z : ZMod q.modulus × SieveCube qs,
          ((ZMod.stdAddChar.mulShift (-ξ.1)) z.1 *
            (tensorDftChar qs ξ.2) z.2) * Φ z
      rw [Fintype.sum_prod_type]
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      rw [AddChar.mulShift_apply]
      ring_nf

theorem tensorDftChar_injective :
    ∀ qs, Function.Injective (tensorDftChar qs)
  | [] => by
      intro ξ η _
      change PUnit at ξ η
      exact Subsingleton.elim ξ η
  | q :: qs => by
      rintro ξ η h
      apply Prod.ext
      · have hchar : ZMod.stdAddChar.mulShift (-ξ.1) =
            ZMod.stdAddChar.mulShift (-η.1) := by
          ext x
          have hx := DFunLike.congr_fun h (x, (0 : SieveCube qs))
          change
            (ZMod.stdAddChar.mulShift (-ξ.1)) x *
                (tensorDftChar qs ξ.2) 0 =
              (ZMod.stdAddChar.mulShift (-η.1)) x *
                (tensorDftChar qs η.2) 0 at hx
          simpa using hx
        have hneg :=
          AddChar.to_mulShift_inj_of_isPrimitive
            (ZMod.isPrimitive_stdAddChar q.modulus) hchar
        exact neg_injective hneg
      · apply tensorDftChar_injective qs
        ext y
        have hy := DFunLike.congr_fun h ((0 : ZMod q.modulus), y)
        change
          (ZMod.stdAddChar.mulShift (-ξ.1)) 0 *
                (tensorDftChar qs ξ.2) y =
            (ZMod.stdAddChar.mulShift (-η.1)) 0 *
                (tensorDftChar qs η.2) y at hy
        simpa using hy

/-- Tensor frequencies index every additive character of the tensor cube
exactly once. -/
noncomputable def tensorDftCharEquiv (qs : List SieveModulus) :
    SieveCube qs ≃ AddChar (SieveCube qs) ℂ :=
  Equiv.ofBijective (tensorDftChar qs)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨tensorDftChar_injective qs, by rw [AddChar.card_eq]⟩)

/-- Cyclic DFT frequencies index every additive character of `ZMod N`
exactly once. -/
noncomputable def cyclicDftCharEquiv (N : ℕ) [NeZero N] :
    ZMod N ≃ AddChar (ZMod N) ℂ :=
  Equiv.ofBijective (fun k => ZMod.stdAddChar.mulShift (-k))
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨by
      intro k l h
      exact neg_injective
        (AddChar.to_mulShift_inj_of_isPrimitive
          (ZMod.isPrimitive_stdAddChar N) h),
      by rw [AddChar.card_eq]⟩)

/-- The cyclic frequency corresponding to a tensor frequency under CRT. -/
noncomputable def crtTensorFrequency (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus)) :
    SieveCube qs → ZMod (sieveModulusProduct qs) := fun ξ =>
  (cyclicDftCharEquiv (sieveModulusProduct qs)).symm
    ((tensorDftChar qs ξ).compAddMonoidHom
      (sieveCrtAddEquiv qs hpair).toAddMonoidHom)

theorem crtTensorFrequency_injective (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus)) :
    Function.Injective (crtTensorFrequency qs hpair) := by
  intro ξ η hfreq
  apply tensorDftChar_injective qs
  apply AddChar.compAddMonoidHom_injective_left
    (sieveCrtAddEquiv qs hpair).toAddMonoidHom
    (sieveCrtAddEquiv qs hpair).surjective
  apply (cyclicDftCharEquiv
    (sieveModulusProduct qs)).symm.injective
  exact hfreq

/-- The CRT frequency has exactly the same additive kernel as its tensor
frequency. -/
theorem crtTensorFrequency_kernel (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (ξ : SieveCube qs) (j : ZMod (sieveModulusProduct qs)) :
    ZMod.stdAddChar (-(j * crtTensorFrequency qs hpair ξ)) =
      tensorDftChar qs ξ (sieveCrtAddEquiv qs hpair j) := by
  have hchar :=
    (cyclicDftCharEquiv (sieveModulusProduct qs)).apply_symm_apply
      ((tensorDftChar qs ξ).compAddMonoidHom
        (sieveCrtAddEquiv qs hpair).toAddMonoidHom)
  change ZMod.stdAddChar.mulShift
      (-crtTensorFrequency qs hpair ξ) =
    (tensorDftChar qs ξ).compAddMonoidHom
      (sieveCrtAddEquiv qs hpair).toAddMonoidHom at hchar
  have h := DFunLike.congr_fun hchar j
  simpa only [AddChar.mulShift_apply, AddChar.compAddMonoidHom_apply,
    neg_mul, mul_neg, mul_comm] using h

/-- The DFT of simultaneous residue aggregation at a tensor frequency equals
the ordinary cyclic DFT modulo the product at its CRT-reindexed frequency. -/
theorem tensorDft_residueClassSum_eq_cyclicDft
    (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (s : Finset ℕ) (f : ℕ → ℂ) (ξ : SieveCube qs) :
    tensorDft qs (tensorResidueClassSum qs s f) ξ =
      ZMod.dft (residueClassSum s f)
        (crtTensorFrequency qs hpair ξ) := by
  rw [tensorDft_eq_sum_char, ZMod.dft_apply]
  simp only [smul_eq_mul]
  rw [show (∑ x : SieveCube qs,
      tensorDftChar qs ξ x * tensorResidueClassSum qs s f x) =
        ∑ n ∈ s, tensorDftChar qs ξ (natSieveCube qs n) * f n by
    unfold tensorResidueClassSum
    calc
      ∑ x : SieveCube qs,
          tensorDftChar qs ξ x *
            (s.filter fun n => natSieveCube qs n = x).sum f =
        ∑ x : SieveCube qs,
          (s.filter fun n => natSieveCube qs n = x).sum
            (fun n => tensorDftChar qs ξ x * f n) := by
          apply sum_congr rfl
          intro x _
          rw [mul_sum]
      _ = ∑ x : SieveCube qs,
          (s.filter fun n => natSieveCube qs n = x).sum
            (fun n => tensorDftChar qs ξ (natSieveCube qs n) * f n) := by
          apply sum_congr rfl
          intro x _
          apply sum_congr rfl
          intro n hn
          rw [(Finset.mem_filter.mp hn).2]
      _ = _ := Finset.sum_fiberwise_of_maps_to
        (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
        (fun n => tensorDftChar qs ξ (natSieveCube qs n) * f n)]
  rw [show (∑ j : ZMod (sieveModulusProduct qs),
      ZMod.stdAddChar (-(j * crtTensorFrequency qs hpair ξ)) *
        residueClassSum s f j) =
      ∑ n ∈ s,
        ZMod.stdAddChar
          (-((n : ZMod (sieveModulusProduct qs)) *
            crtTensorFrequency qs hpair ξ)) * f n by
    exact dft_residueClassSum s f (crtTensorFrequency qs hpair ξ)]
  apply sum_congr rfl
  intro n hn
  rw [← sieveCrtAddEquiv_natCast qs hpair n]
  rw [← crtTensorFrequency_kernel qs hpair ξ]

/-- Image of the tensor frequencies nonzero in every coordinate inside the
single cyclic frequency space modulo the product. -/
noncomputable def crtTensorFrequencies (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus)) :
    Finset (ZMod (sieveModulusProduct qs)) :=
  (tensorNonzeroFrequencies qs).image
    (crtTensorFrequency qs hpair)

theorem card_crtTensorFrequencies (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus)) :
    (crtTensorFrequencies qs hpair).card =
      (tensorNonzeroFrequencies qs).card := by
  exact Finset.card_image_iff.mpr
    (crtTensorFrequency_injective qs hpair).injOn

/-- Exact reindexing of the nonzero tensor Fourier energy as ordinary cyclic
DFT energy modulo the product. -/
theorem sum_tensorDft_nonzero_eq_sum_cyclicDft
    (qs : List SieveModulus)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (s : Finset ℕ) (f : ℕ → ℂ) :
    ∑ ξ ∈ tensorNonzeroFrequencies qs,
        Complex.normSq
          (tensorDft qs (tensorResidueClassSum qs s f) ξ) =
      ∑ k ∈ crtTensorFrequencies qs hpair,
        Complex.normSq (ZMod.dft (residueClassSum s f) k) := by
  rw [crtTensorFrequencies, Finset.sum_image]
  · apply sum_congr rfl
    intro ξ hξ
    rw [tensorDft_residueClassSum_eq_cyclicDft]
  · exact (crtTensorFrequency_injective qs hpair).injOn

/-- CRT-reindexed finite-support Montgomery uncertainty.  This is the lower
inequality in the single cyclic denominator required by Tao's Lemma 2.6. -/
theorem montgomery_uncertainty_crt_finite
    (qs : List SieveModulus) (R : SieveRestrictions qs)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    (s : Finset ℕ) (f : ℕ → ℂ)
    (hproper : SieveRestrictionsProper R)
    (hzero : ∀ n ∈ s, ¬ SieveAvoids R (natSieveCube qs n) → f n = 0) :
    sieveRestrictionRatio R * Complex.normSq (∑ n ∈ s, f n) ≤
      ∑ k ∈ crtTensorFrequencies qs hpair,
        Complex.normSq (ZMod.dft (residueClassSum s f) k) := by
  rw [← sum_tensorDft_nonzero_eq_sum_cyclicDft qs hpair s f]
  exact montgomery_uncertainty_tensor_finite qs R s f hproper hzero

/-- Combining the CRT-reindexed Montgomery lower bound with the interval DFT
upper bound gives the squared finite survivor estimate. -/
theorem montgomery_largeSieve_card_sq_le
    (qs : List SieveModulus) (R : SieveRestrictions qs)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    {s : Finset ℕ} {x : ℕ}
    (hsupport : s ⊆ Finset.Icc 0 x)
    (hproper : SieveRestrictionsProper R)
    (havoid : ∀ n ∈ s, SieveAvoids R (natSieveCube qs n)) :
    sieveRestrictionRatio R * (s.card : ℝ) ^ 2 ≤
      ((sieveModulusProduct qs *
        ((x + 1) / sieveModulusProduct qs + 1) : ℕ) : ℝ) * s.card := by
  let f : ℕ → ℂ := fun _ => 1
  have hlower := montgomery_uncertainty_crt_finite qs R hpair s f hproper (by
    intro n hn hnot
    exact (hnot (havoid n hn)).elim)
  have hupper := dft_subset_energy_le_interval
    (N := sieveModulusProduct qs) hsupport f
      (crtTensorFrequencies qs hpair)
  have h := hlower.trans hupper
  simpa only [f, sum_const, card_attach, nsmul_eq_mul, mul_one,
    Complex.normSq_natCast, Complex.normSq_one, sum_const_zero,
    Nat.cast_ofNat, Nat.cast_mul, pow_two] using h

/-- Linear finite survivor estimate obtained by cancelling the survivor
cardinality (with the empty case handled separately). -/
theorem montgomery_largeSieve_card_le
    (qs : List SieveModulus) (R : SieveRestrictions qs)
    (hpair : qs.Pairwise
      (Function.onFun Nat.Coprime SieveModulus.modulus))
    {s : Finset ℕ} {x : ℕ}
    (hsupport : s ⊆ Finset.Icc 0 x)
    (hproper : SieveRestrictionsProper R)
    (havoid : ∀ n ∈ s, SieveAvoids R (natSieveCube qs n)) :
    sieveRestrictionRatio R * (s.card : ℝ) ≤
      (sieveModulusProduct qs *
        ((x + 1) / sieveModulusProduct qs + 1) : ℕ) := by
  by_cases hcard : s.card = 0
  · simp only [hcard, Nat.cast_zero, mul_zero]
    positivity
  · have hcardPos : (0 : ℝ) < s.card := by positivity
    have hsq := montgomery_largeSieve_card_sq_le
      qs R hpair hsupport hproper havoid
    apply le_of_mul_le_mul_right _ hcardPos
    simpa only [pow_two, Nat.cast_mul, mul_assoc] using hsq

end Tao2026
