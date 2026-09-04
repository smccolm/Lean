import GafniTao.WooleySourceAffine
import GafniTao.WooleySourceBox

/-!
# Boxing an arbitrary finitely supported Wooley sequence

The source permits coefficients on all of `ℤ`, while the finite congruence
lemmas developed earlier use `Fin Q`.  This file proves an exact bridge: after
one integral translation, every finitely supported source sequence is the
box embedding of a coefficient family on `1,...,Q`.  No coefficient is
discarded and the polynomial system is translated in tandem.
-/

open Finset Polynomial
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A deliberately simple radius dominating the absolute value of every
index in the finite support. -/
def wooleySourceRadius (gamma : WooleySourceSequence) : ℕ :=
  ∑ n ∈ gamma.support, n.natAbs

theorem wooleySource_natAbs_le_radius
    (gamma : WooleySourceSequence) {n : ℤ} (hn : n ∈ gamma.support) :
    n.natAbs ≤ wooleySourceRadius gamma := by
  unfold wooleySourceRadius
  exact Finset.single_le_sum (fun m _ => Nat.zero_le m.natAbs) hn

theorem wooleySource_neg_radius_le
    (gamma : WooleySourceSequence) {n : ℤ} (hn : n ∈ gamma.support) :
    -(wooleySourceRadius gamma : ℤ) ≤ n := by
  have habs := wooleySource_natAbs_le_radius gamma hn
  have hcast : (n.natAbs : ℤ) ≤ (wooleySourceRadius gamma : ℤ) := by
    exact_mod_cast habs
  have hnabs : -(n.natAbs : ℤ) ≤ n := by
    by_cases hn0 : 0 ≤ n
    · exact (neg_nonpos.mpr (by positivity)).trans hn0
    · have hnonpos : n ≤ 0 := le_of_not_ge hn0
      rw [Int.ofNat_natAbs_of_nonpos hnonpos]
      simp
  exact (neg_le_neg hcast).trans hnabs

theorem wooleySource_le_radius
    (gamma : WooleySourceSequence) {n : ℤ} (hn : n ∈ gamma.support) :
    n ≤ (wooleySourceRadius gamma : ℤ) := by
  exact (Int.le_natAbs (a := n)).trans (by
    exact_mod_cast wooleySource_natAbs_le_radius gamma hn)

/-- The box embedding has image exactly the integer interval `[1,Q]`. -/
theorem mem_range_wooleyBoxIndexEmbedding_iff
    (Q : ℕ) (y : ℤ) :
    y ∈ Set.range (wooleyBoxIndexEmbedding Q) ↔
      (1 : ℤ) ≤ y ∧ y ≤ (Q : ℤ) := by
  constructor
  · rintro ⟨n, rfl⟩
    constructor
    · norm_num
    · change ((((n : ℕ) + 1 : ℕ) : ℕ) : ℤ) ≤ (Q : ℤ)
      exact_mod_cast (Nat.succ_le_iff.mpr n.isLt)
  · rintro ⟨hy1, hyQ⟩
    have hy0 : 0 ≤ y - 1 := by omega
    have hylt : y - 1 < (Q : ℤ) := by omega
    let n : Fin Q := ⟨(y - 1).toNat,
      (Int.toNat_lt hy0).mpr hylt⟩
    refine ⟨n, ?_⟩
    change ((((y - 1).toNat + 1 : ℕ) : ℕ) : ℤ) = y
    rw [Nat.cast_add, Nat.cast_one, Int.toNat_of_nonneg hy0]
    omega

/-- The translation used to move the support into positive indices. -/
def wooleyBoxedSourceSequence (gamma : WooleySourceSequence) :
    WooleySourceSequence :=
  wooleyAffinePullback gamma 1 (by norm_num)
    (-((wooleySourceRadius gamma + 1 : ℕ) : ℤ))

/-- The length of the symmetric box containing the translated support. -/
def wooleySourceBoxLength (gamma : WooleySourceSequence) : ℕ :=
  2 * wooleySourceRadius gamma + 1

/-- The exact finite coefficient family obtained from the translated source
sequence. -/
def wooleySourceBoxCoefficients (gamma : WooleySourceSequence) :
    Fin (wooleySourceBoxLength gamma) → ℂ :=
  fun n => wooleyBoxedSourceSequence gamma (wooleyBoxIndexEmbedding _ n)

theorem wooleyBoxedSourceSequence_support_subset
    (gamma : WooleySourceSequence) :
    (↑(wooleyBoxedSourceSequence gamma).support : Set ℤ) ⊆
      Set.range (wooleyBoxIndexEmbedding (wooleySourceBoxLength gamma)) := by
  intro y hy
  have hyne : wooleyBoxedSourceSequence gamma y ≠ 0 :=
    Finsupp.mem_support_iff.mp hy
  have hnmem :
      y - ((wooleySourceRadius gamma + 1 : ℕ) : ℤ) ∈ gamma.support := by
    apply Finsupp.mem_support_iff.mpr
    rw [wooleyBoxedSourceSequence, wooleyAffinePullback_apply] at hyne
    norm_num at hyne
    have harg :
        y + (-1 + -(wooleySourceRadius gamma : ℤ)) =
          y - ((wooleySourceRadius gamma + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [harg] at hyne
    exact hyne
  have hlo := wooleySource_neg_radius_le gamma hnmem
  have hhi := wooleySource_le_radius gamma hnmem
  rw [mem_range_wooleyBoxIndexEmbedding_iff]
  unfold wooleySourceBoxLength
  constructor <;> omega

/-- Exact recovery of the translated source sequence from its finite box. -/
theorem wooleyBoxSourceSequence_boxCoefficients
    (gamma : WooleySourceSequence) :
    wooleyBoxSourceSequence (wooleySourceBoxCoefficients gamma) =
      wooleyBoxedSourceSequence gamma := by
  let f := wooleyBoxIndexEmbedding (wooleySourceBoxLength gamma)
  let beta := wooleyBoxedSourceSequence gamma
  have hsupp : (↑beta.support : Set ℤ) ⊆ Set.range f := by
    exact wooleyBoxedSourceSequence_support_subset gamma
  have hrecover := Finsupp.embDomain_comapDomain (f := f) (g := beta) hsupp
  have hcoeff :
      Finsupp.comapDomain f beta f.injective.injOn =
        Finsupp.equivFunOnFinite.symm (wooleySourceBoxCoefficients gamma) := by
    apply Finsupp.ext
    intro n
    simp [wooleySourceBoxCoefficients, f, beta]
  unfold wooleyBoxSourceSequence
  rw [← hcoeff]
  exact hrecover

/-- The original source sequence is recovered by undoing the translation. -/
theorem wooleyBoxedSourceSequence_apply_shift
    (gamma : WooleySourceSequence) (n : ℤ) :
    wooleyBoxedSourceSequence gamma
        (n + ((wooleySourceRadius gamma + 1 : ℕ) : ℤ)) = gamma n := by
  rw [wooleyBoxedSourceSequence, wooleyAffinePullback_apply]
  congr 1
  push_cast
  ring

/-- Translate the polynomial system by the same amount used to box the
coefficient sequence. -/
def wooleyBoxedPolynomialSystem {k : ℕ}
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) :
    WooleyPolynomialSystem k :=
  wooleyAffinePolynomialSystem phi 1
    (-((wooleySourceRadius gamma + 1 : ℕ) : ℤ))

/-- Translation preserves the normalized global exponential sum exactly. -/
theorem wooleySourceNormalizedPolynomialSum_boxing_translation
    {k q : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) (alpha : Fin k → ZMod q) :
    wooleySourceNormalizedPolynomialSum
        (wooleyBoxedPolynomialSystem phi gamma)
        (wooleyBoxedSourceSequence gamma) alpha =
      wooleySourceNormalizedPolynomialSum phi gamma alpha := by
  have h := wooleySourceNormalizedPolynomialSum_affinePullback
    (q := 1) (qB := q) (by norm_num) phi gamma alpha
      (-((wooleySourceRadius gamma + 1 : ℕ) : ℤ))
  rw [wooleySourceNormalizedPolynomialResidueSum_mod_one] at h
  exact h

/-- Hence the full source mean is unchanged by the boxing translation. -/
theorem wooleySourcePolynomialMean_boxing_translation
    {k q s : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMean s q
        (wooleyBoxedPolynomialSystem phi gamma)
        (wooleyBoxedSourceSequence gamma) =
      wooleySourcePolynomialMean s q phi gamma := by
  unfold wooleySourcePolynomialMean
  simp_rw [wooleySourceNormalizedPolynomialSum_boxing_translation]

/-- Every source mean is exactly a finite-box polynomial mean after the
proved translation of both coefficients and polynomials. -/
theorem wooleySourcePolynomialMean_eq_boxed
    {k q s : ℕ} [NeZero q] (phi : WooleyPolynomialSystem k)
    (gamma : WooleySourceSequence) :
    wooleySourcePolynomialMean s q phi gamma =
      wooleyPolynomialWeightedGridMean
        (wooleyBoxedPolynomialSystem phi gamma) s q
        (wooleySourceBoxCoefficients gamma) := by
  calc
    wooleySourcePolynomialMean s q phi gamma =
        wooleySourcePolynomialMean s q
          (wooleyBoxedPolynomialSystem phi gamma)
          (wooleyBoxedSourceSequence gamma) :=
      (wooleySourcePolynomialMean_boxing_translation phi gamma).symm
    _ = wooleySourcePolynomialMean s q
          (wooleyBoxedPolynomialSystem phi gamma)
          (wooleyBoxSourceSequence (wooleySourceBoxCoefficients gamma)) := by
      rw [wooleyBoxSourceSequence_boxCoefficients]
    _ = _ := wooleySourcePolynomialMean_box _ _

/-- The conditioned source mean is also unchanged by the boxing
translation; the proof uses the exact residue-class permutation. -/
theorem wooleySourcePolynomialConditionedMean_boxing_translation
    {k q qH s : ℕ} [NeZero q] [NeZero qH]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) :
    wooleySourcePolynomialConditionedMean s q qH
        (wooleyBoxedPolynomialSystem phi gamma)
        (wooleyBoxedSourceSequence gamma) =
      wooleySourcePolynomialConditionedMean s q qH phi gamma := by
  exact wooleySourcePolynomialConditionedMean_affinePullback_one
    phi gamma (-((wooleySourceRadius gamma + 1 : ℕ) : ℤ))

/-- Every conditioned source mean is exactly its finite-box polynomial
realization after the same translation. -/
theorem wooleySourcePolynomialConditionedMean_eq_boxed
    {k q qH s : ℕ} [NeZero q] [NeZero qH]
    (phi : WooleyPolynomialSystem k) (gamma : WooleySourceSequence) :
    wooleySourcePolynomialConditionedMean s q qH phi gamma =
      wooleyPolynomialConditionedGridMean
        (wooleyBoxedPolynomialSystem phi gamma) s q qH
        (wooleySourceBoxCoefficients gamma) := by
  calc
    wooleySourcePolynomialConditionedMean s q qH phi gamma =
        wooleySourcePolynomialConditionedMean s q qH
          (wooleyBoxedPolynomialSystem phi gamma)
          (wooleyBoxedSourceSequence gamma) :=
      (wooleySourcePolynomialConditionedMean_boxing_translation
        phi gamma).symm
    _ = wooleySourcePolynomialConditionedMean s q qH
          (wooleyBoxedPolynomialSystem phi gamma)
          (wooleyBoxSourceSequence (wooleySourceBoxCoefficients gamma)) := by
      rw [wooleyBoxSourceSequence_boxCoefficients]
    _ = _ := wooleySourcePolynomialConditionedMean_box _ _

theorem WooleySourceSequence.Admissible.boxCoefficients
    {gamma : WooleySourceSequence} (hgamma : gamma.Admissible) :
    ∀ n : Fin (wooleySourceBoxLength gamma),
      ‖wooleySourceBoxCoefficients gamma n‖ ≤ 1 := by
  intro n
  unfold wooleySourceBoxCoefficients
  exact hgamma.affinePullback 1 (by norm_num) _ _

#print axioms wooleySource_natAbs_le_radius
#print axioms wooleySource_neg_radius_le
#print axioms wooleySource_le_radius
#print axioms mem_range_wooleyBoxIndexEmbedding_iff
#print axioms wooleyBoxedSourceSequence_support_subset
#print axioms wooleyBoxSourceSequence_boxCoefficients
#print axioms wooleyBoxedSourceSequence_apply_shift
#print axioms wooleySourceNormalizedPolynomialSum_boxing_translation
#print axioms wooleySourcePolynomialMean_boxing_translation
#print axioms wooleySourcePolynomialMean_eq_boxed
#print axioms wooleySourcePolynomialConditionedMean_boxing_translation
#print axioms wooleySourcePolynomialConditionedMean_eq_boxed
#print axioms WooleySourceSequence.Admissible.boxCoefficients

end

end GafniTao
