import GafniTao.WooleyMixedMean
import GafniTao.WooleyResidueRefinement

/-!
# Wooley Lemma 6.3: refinement of the initial mixed mean

This file formalizes the two applications of Lemma 6.2 in the proof of
Wooley's Lemma 6.3.  The key statement is kept pointwise on the complete
finite frequency grid.  Both refined residue classes are explicit and the
separation condition modulo `p^nu` is preserved.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- A refinement of a residue class modulo `p^theta` has the original least
residue modulo `p^nu`. -/
theorem wooley_refinement_val_mod
    {p nu theta : ℕ} [NeZero p] (hnu : nu ≤ theta)
    (xi : ZMod (p ^ nu))
    {z : ZMod (p ^ theta)}
    (hz : z ∈ wooleyResidueRefinementFiber p nu theta hnu xi) :
    z.val % (p ^ nu) = xi.val := by
  have hcast :
      ZMod.castHom (pow_dvd_pow p hnu) (ZMod (p ^ nu)) z = xi := by
    simpa [wooleyResidueRefinementFiber] using hz
  have hpnu : 0 < p ^ nu := pow_pos (NeZero.pos p) nu
  have hxiVal : xi.val < p ^ nu := ZMod.val_lt xi
  have hzval :
      (z.val : ZMod (p ^ nu)) = xi := by
    simpa only [ZMod.castHom_apply, ZMod.cast_eq_val] using hcast
  have hval := congrArg ZMod.val hzval
  simpa only [ZMod.val_natCast] using hval

/-- Separation modulo `p^nu` survives simultaneous refinement to depth
`theta`. -/
theorem wooley_refinements_separated
    {p nu theta : ℕ} [NeZero p] (hnu : nu ≤ theta)
    {xi eta : ZMod (p ^ nu)}
    (hsep : wooleyResiduesSeparated nu xi eta)
    {xi' eta' : ZMod (p ^ theta)}
    (hxi : xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi)
    (heta : eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta) :
    wooleyResiduesSeparated nu xi' eta' := by
  unfold wooleyResiduesSeparated at hsep ⊢
  rw [wooley_refinement_val_mod hnu xi hxi,
    wooley_refinement_val_mod hnu eta heta]
  simpa [Nat.mod_eq_of_lt (ZMod.val_lt xi),
    Nat.mod_eq_of_lt (ZMod.val_lt eta)] using hsep

/-- Summing over a separated coarse pair and then over both refinement
fibres is exactly summation over separated refined pairs. -/
theorem wooley_sum_refinement_pairs
    {p nu theta : ℕ} [NeZero p] (hnu : nu ≤ theta)
    (F : ZMod (p ^ theta) → ZMod (p ^ theta) → ℝ) :
    ∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
            ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
              F xi' eta' =
      ∑ xi' : ZMod (p ^ theta),
        ∑ eta' : ZMod (p ^ theta) with
          wooleyResiduesSeparated nu xi' eta', F xi' eta' := by
  classical
  let red : ZMod (p ^ theta) → ZMod (p ^ nu) :=
    ZMod.castHom (pow_dvd_pow p hnu) (ZMod (p ^ nu))
  let coarsePairs : Finset (ZMod (p ^ nu) × ZMod (p ^ nu)) :=
    (Finset.univ.product Finset.univ).filter fun xy =>
      wooleyResiduesSeparated nu xy.1 xy.2
  let finePairs : Finset (ZMod (p ^ theta) × ZMod (p ^ theta)) :=
    (Finset.univ.product Finset.univ).filter fun zw =>
      wooleyResiduesSeparated nu zw.1 zw.2
  let redPair : ZMod (p ^ theta) × ZMod (p ^ theta) →
      ZMod (p ^ nu) × ZMod (p ^ nu) := fun zw => (red zw.1, red zw.2)
  let pairFiber (xy : ZMod (p ^ nu) × ZMod (p ^ nu)) :=
    (wooleyResidueRefinementFiber p nu theta hnu xy.1).product
      (wooleyResidueRefinementFiber p nu theta hnu xy.2)
  have href (z : ZMod (p ^ theta)) (xi : ZMod (p ^ nu)) :
      z ∈ wooleyResidueRefinementFiber p nu theta hnu xi ↔ red z = xi := by
    simp [wooleyResidueRefinementFiber, red]
  have hsep (z w : ZMod (p ^ theta)) :
      wooleyResiduesSeparated nu (red z) (red w) ↔
        wooleyResiduesSeparated nu z w := by
    constructor
    · intro h
      exact wooley_refinements_separated hnu h
        ((href z (red z)).2 rfl) ((href w (red w)).2 rfl)
    · intro h
      unfold wooleyResiduesSeparated at h ⊢
      have hz := wooley_refinement_val_mod hnu (red z)
        ((href z (red z)).2 rfl)
      have hw := wooley_refinement_val_mod hnu (red w)
        ((href w (red w)).2 rfl)
      rw [hz, hw] at h
      simpa [Nat.mod_eq_of_lt (ZMod.val_lt (red z)),
        Nat.mod_eq_of_lt (ZMod.val_lt (red w))] using h
  have hfiber (xy : ZMod (p ^ nu) × ZMod (p ^ nu))
      (hxy : wooleyResiduesSeparated nu xy.1 xy.2) :
      finePairs.filter (fun zw => redPair zw = xy) = pairFiber xy := by
    ext zw
    simp only [Finset.mem_filter]
    dsimp [finePairs, redPair, pairFiber]
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨hfine, hred⟩
      have hz : red zw.1 = xy.1 := congrArg Prod.fst hred
      have hw : red zw.2 = xy.2 := congrArg Prod.snd hred
      exact ⟨(href zw.1 xy.1).2 hz, (href zw.2 xy.2).2 hw⟩
    · rintro ⟨hz, hw⟩
      have hzred := (href zw.1 xy.1).1 hz
      have hwred := (href zw.2 xy.2).1 hw
      exact ⟨wooley_refinements_separated hnu hxy hz hw,
        Prod.ext hzred hwred⟩
  have hfiber_empty (xy : ZMod (p ^ nu) × ZMod (p ^ nu))
      (hxy : ¬ wooleyResiduesSeparated nu xy.1 xy.2) :
      finePairs.filter (fun zw => redPair zw = xy) = ∅ := by
    ext zw
    simp only [Finset.mem_filter]
    dsimp [finePairs, redPair]
    simp only [Finset.mem_filter, Finset.mem_univ,
      true_and]
    have hempty : zw ∈ (∅ : Finset
        (ZMod (p ^ theta) × ZMod (p ^ theta))) ↔ False := by simp
    rw [hempty]
    constructor
    · rintro ⟨hfine, hred⟩
      have hz : red zw.1 = xy.1 := congrArg Prod.fst hred
      have hw : red zw.2 = xy.2 := congrArg Prod.snd hred
      apply hxy
      have : wooleyResiduesSeparated nu (red zw.1) (red zw.2) :=
        (hsep zw.1 zw.2).2 hfine
      simpa [hz, hw] using this
    · exact False.elim
  have hinter (xy : ZMod (p ^ nu) × ZMod (p ^ nu)) :
      ∑ zw ∈ finePairs with redPair zw = xy, F zw.1 zw.2 =
        if wooleyResiduesSeparated nu xy.1 xy.2 then
          ∑ zw ∈ pairFiber xy, F zw.1 zw.2
        else 0 := by
    by_cases hxy : wooleyResiduesSeparated nu xy.1 xy.2
    · rw [if_pos hxy, hfiber xy hxy]
    · rw [if_neg hxy, hfiber_empty xy hxy]
      simp
  have hgroup := Finset.sum_fiberwise finePairs redPair
    (fun zw => F zw.1 zw.2)
  have hflat :
      ∑ xy ∈ coarsePairs,
          ∑ zw ∈ pairFiber xy, F zw.1 zw.2 =
        ∑ zw ∈ finePairs, F zw.1 zw.2 := by
    rw [← hgroup]
    simp_rw [hinter]
    simp [coarsePairs, Finset.sum_filter]
  calc
    (∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
            ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
              F xi' eta') =
        ∑ xy ∈ coarsePairs,
          ∑ zw ∈ pairFiber xy, F zw.1 zw.2 := by
      simp only [coarsePairs, pairFiber, Finset.sum_filter]
      simp
      simpa [Finset.sum_product] using (Finset.sum_product
        (Finset.univ : Finset (ZMod (p ^ nu)))
        (Finset.univ : Finset (ZMod (p ^ nu)))
        (fun xy => if wooleyResiduesSeparated nu xy.1 xy.2 then
          ∑ zw ∈
            (wooleyResidueRefinementFiber p nu theta hnu xy.1).product
              (wooleyResidueRefinementFiber p nu theta hnu xy.2),
            F zw.1 zw.2 else 0)).symm
    _ = ∑ zw ∈ finePairs, F zw.1 zw.2 := hflat
    _ = ∑ xi' : ZMod (p ^ theta),
        ∑ eta' : ZMod (p ^ theta) with
          wooleyResiduesSeparated nu xi' eta', F xi' eta' := by
      simp only [finePairs, Finset.sum_filter]
      simp
      simpa using Finset.sum_product
        (Finset.univ : Finset (ZMod (p ^ theta)))
        (Finset.univ : Finset (ZMod (p ^ theta)))
        (fun zw => if wooleyResiduesSeparated nu zw.1 zw.2 then
          F zw.1 zw.2 else 0)

/-- The pointwise two-factor refinement used in Wooley Lemma 6.3. -/
theorem wooley_mixed_one_point_refinement
    {Q p nu theta qB k s : ℕ} [NeZero p] [NeZero qB]
    (hnu : nu ≤ theta) (hs : 2 ≤ s)
    (gamma : Fin Q → ℂ) (alpha : Fin k → ZMod qB)
    (xi eta : ZMod (p ^ nu)) :
    wooleyWeightedResidueMassSq gamma xi *
        wooleyWeightedResidueMassSq gamma eta *
        (‖wooleyWeightedNormalizedResidueGridSum
            qB k gamma alpha xi‖ ^ 2 *
          ‖wooleyWeightedNormalizedResidueGridSum
            qB k gamma alpha eta‖ ^ (2 * (s - 1))) ≤
      (p ^ (theta - nu) : ℝ) ^ s *
        ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
          ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
            wooleyWeightedResidueMassSq gamma xi' *
              wooleyWeightedResidueMassSq gamma eta' *
              (‖wooleyWeightedNormalizedResidueGridSum
                  qB k gamma alpha xi'‖ ^ 2 *
                ‖wooleyWeightedNormalizedResidueGridSum
                  qB k gamma alpha eta'‖ ^ (2 * (s - 1))) := by
  let A : ℝ := wooleyWeightedResidueMassSq gamma xi *
    ‖wooleyWeightedNormalizedResidueGridSum qB k gamma alpha xi‖ ^ 2
  let B : ℝ := wooleyWeightedResidueMassSq gamma eta *
    ‖wooleyWeightedNormalizedResidueGridSum qB k gamma alpha eta‖ ^
      (2 * (s - 1))
  let AR : ℝ := ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
    wooleyWeightedResidueMassSq gamma xi' *
      ‖wooleyWeightedNormalizedResidueGridSum
        qB k gamma alpha xi'‖ ^ 2
  let BR : ℝ := ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
    wooleyWeightedResidueMassSq gamma eta' *
      ‖wooleyWeightedNormalizedResidueGridSum
        qB k gamma alpha eta'‖ ^ (2 * (s - 1))
  have hs1 : 1 ≤ s - 1 := by omega
  have hA : A ≤ (p ^ (theta - nu) : ℝ) * AR := by
    simpa only [A, AR, one_mul, pow_one, Nat.mul_one] using
      (wooley_lemma_6_2 (qB := qB) (k := k) (w := 1)
        hnu (by omega) gamma alpha xi)
  have hB : B ≤ (p ^ (theta - nu) : ℝ) ^ (s - 1) * BR := by
    simpa only [B, BR] using
      (wooley_lemma_6_2 (qB := qB) (k := k) (w := s - 1)
        hnu hs1 gamma alpha eta)
  have hAnonneg : 0 ≤ A := mul_nonneg
    (wooleyWeightedResidueMassSq_nonneg gamma xi) (by positivity)
  have hBnonneg : 0 ≤ B := mul_nonneg
    (wooleyWeightedResidueMassSq_nonneg gamma eta) (by positivity)
  have hARnonneg : 0 ≤ AR := by
    dsimp [AR]
    exact Finset.sum_nonneg fun xi' hxi' => mul_nonneg
      (wooleyWeightedResidueMassSq_nonneg gamma xi') (by positivity)
  have hBRnonneg : 0 ≤ BR := by
    dsimp [BR]
    exact Finset.sum_nonneg fun eta' heta' => mul_nonneg
      (wooleyWeightedResidueMassSq_nonneg gamma eta') (by positivity)
  have hmul : A * B ≤
      ((p ^ (theta - nu) : ℝ) * AR) *
        ((p ^ (theta - nu) : ℝ) ^ (s - 1) * BR) :=
    mul_le_mul hA hB hBnonneg
      (mul_nonneg (by positivity) hARnonneg)
  dsimp [A, B, AR, BR] at hmul
  have hpow :
      (p ^ (theta - nu) : ℝ) *
          (p ^ (theta - nu) : ℝ) ^ (s - 1) =
        (p ^ (theta - nu) : ℝ) ^ s := by
    rw [← pow_succ']
    congr
    omega
  calc
    wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta *
          (‖wooleyWeightedNormalizedResidueGridSum
              qB k gamma alpha xi‖ ^ 2 *
            ‖wooleyWeightedNormalizedResidueGridSum
              qB k gamma alpha eta‖ ^ (2 * (s - 1))) =
        (wooleyWeightedResidueMassSq gamma xi *
            ‖wooleyWeightedNormalizedResidueGridSum
              qB k gamma alpha xi‖ ^ 2) *
          (wooleyWeightedResidueMassSq gamma eta *
            ‖wooleyWeightedNormalizedResidueGridSum
              qB k gamma alpha eta‖ ^ (2 * (s - 1))) := by ring
    _ ≤ ((p ^ (theta - nu) : ℝ) *
          ∑ xi' ∈ wooleyResidueRefinementFiber p nu theta hnu xi,
            wooleyWeightedResidueMassSq gamma xi' *
              ‖wooleyWeightedNormalizedResidueGridSum
                qB k gamma alpha xi'‖ ^ 2) *
        ((p ^ (theta - nu) : ℝ) ^ (s - 1) *
          ∑ eta' ∈ wooleyResidueRefinementFiber p nu theta hnu eta,
            wooleyWeightedResidueMassSq gamma eta' *
              ‖wooleyWeightedNormalizedResidueGridSum
                qB k gamma alpha eta'‖ ^ (2 * (s - 1))) := hmul
    _ = _ := by
      rw [← hpow]
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro xi' hxi'
      apply Finset.sum_congr rfl
      intro eta' heta'
      ring

/-- The two applications of Lemma 6.2 assembled at the level of the exact
mixed mean `K^1`.  This is the refinement estimate in the proof of Wooley
Lemma 6.3. -/
theorem wooley_mixed_one_refinement
    {Q p nu theta B k s : ℕ} [NeZero p] [NeZero (p ^ B)]
    (hnu : nu ≤ theta) (hs : 2 ≤ s) (gamma : Fin Q → ℂ) :
    wooleyMixedGridMean s k 1 p B nu nu nu gamma ≤
      (p ^ (theta - nu) : ℝ) ^ s *
        wooleyMixedGridMean s k 1 p B theta theta nu gamma := by
  let V (d : ℕ) (xi eta : ZMod (p ^ d))
      (alpha : Fin k → ZMod (p ^ B)) : ℝ :=
    wooleyWeightedResidueMassSq gamma xi *
      wooleyWeightedResidueMassSq gamma eta *
      (‖wooleyWeightedNormalizedResidueGridSum
          (p ^ B) k gamma alpha xi‖ ^ 2 *
        ‖wooleyWeightedNormalizedResidueGridSum
          (p ^ B) k gamma alpha eta‖ ^ (2 * (s - 1)))
  let P (d : ℕ) : ℝ :=
    ∑ alpha : Fin k → ZMod (p ^ B),
      ∑ xi : ZMod (p ^ d),
        ∑ eta : ZMod (p ^ d) with wooleyResiduesSeparated nu xi eta,
          V d xi eta alpha
  let gridScale : ℝ := (((p ^ B) ^ k : ℕ) : ℝ)⁻¹
  have haggregate (d : ℕ) :
      ∑ xi : ZMod (p ^ d),
        ∑ eta : ZMod (p ^ d) with wooleyResiduesSeparated nu xi eta,
          wooleyWeightedResidueMassSq gamma xi *
            wooleyWeightedResidueMassSq gamma eta *
              wooleyMixedResidueGridMoment
                s k 1 p B d d gamma xi eta =
        gridScale * P d := by
    dsimp [gridScale, P, V]
    simp only [wooleyMixedResidueGridMoment, wooleyTriangular_one,
      Nat.mul_one]
    have hlocal (xi eta : ZMod (p ^ d)) :
        wooleyWeightedResidueMassSq gamma xi *
            wooleyWeightedResidueMassSq gamma eta *
              (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                ∑ alpha : Fin k → ZMod (p ^ B),
                  ‖wooleyWeightedNormalizedResidueGridSum
                    (p ^ B) k gamma alpha xi‖ ^ 2 *
                  ‖wooleyWeightedNormalizedResidueGridSum
                    (p ^ B) k gamma alpha eta‖ ^ (2 * (s - 1))) =
          ∑ alpha : Fin k → ZMod (p ^ B),
            ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
              (wooleyWeightedResidueMassSq gamma xi *
                wooleyWeightedResidueMassSq gamma eta *
                (‖wooleyWeightedNormalizedResidueGridSum
                    (p ^ B) k gamma alpha xi‖ ^ 2 *
                  ‖wooleyWeightedNormalizedResidueGridSum
                    (p ^ B) k gamma alpha eta‖ ^ (2 * (s - 1)))) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro alpha halpha
      ring
    simp_rw [hlocal]
    rw [show
      (∑ xi : ZMod (p ^ d),
        ∑ eta : ZMod (p ^ d) with wooleyResiduesSeparated nu xi eta,
          ∑ alpha : Fin k → ZMod (p ^ B),
            ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ * V d xi eta alpha) =
      ∑ xi : ZMod (p ^ d),
        ∑ alpha : Fin k → ZMod (p ^ B),
          ∑ eta : ZMod (p ^ d) with wooleyResiduesSeparated nu xi eta,
            ((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ * V d xi eta alpha by
      apply Finset.sum_congr rfl
      intro xi hxi
      rw [Finset.sum_comm]]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro alpha halpha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro xi hxi
    rw [Finset.mul_sum]
  have hpoint (alpha : Fin k → ZMod (p ^ B)) :
      (∑ xi : ZMod (p ^ nu),
        ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
          V nu xi eta alpha) ≤
        (p ^ (theta - nu) : ℝ) ^ s *
          ∑ xi : ZMod (p ^ theta),
            ∑ eta : ZMod (p ^ theta) with
              wooleyResiduesSeparated nu xi eta,
                V theta xi eta alpha := by
    calc
      (∑ xi : ZMod (p ^ nu),
          ∑ eta : ZMod (p ^ nu) with wooleyResiduesSeparated nu xi eta,
            V nu xi eta alpha) ≤
          ∑ xi : ZMod (p ^ nu),
            ∑ eta : ZMod (p ^ nu) with
              wooleyResiduesSeparated nu xi eta,
                (p ^ (theta - nu) : ℝ) ^ s *
                  ∑ xi' ∈
                    wooleyResidueRefinementFiber p nu theta hnu xi,
                    ∑ eta' ∈
                      wooleyResidueRefinementFiber p nu theta hnu eta,
                      V theta xi' eta' alpha := by
        apply Finset.sum_le_sum
        intro xi hxi
        apply Finset.sum_le_sum
        intro eta heta
        simpa only [V] using
          (wooley_mixed_one_point_refinement
            (qB := p ^ B) (k := k) hnu hs gamma alpha xi eta)
      _ = (p ^ (theta - nu) : ℝ) ^ s *
          ∑ xi : ZMod (p ^ theta),
            ∑ eta : ZMod (p ^ theta) with
              wooleyResiduesSeparated nu xi eta,
                V theta xi eta alpha := by
        rw [← wooley_sum_refinement_pairs hnu
          (fun xi eta => V theta xi eta alpha)]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro xi hxi
        rw [Finset.mul_sum]
  have hP : P nu ≤ (p ^ (theta - nu) : ℝ) ^ s * P theta := by
    dsimp [P]
    calc
      (∑ alpha : Fin k → ZMod (p ^ B),
          ∑ xi : ZMod (p ^ nu),
            ∑ eta : ZMod (p ^ nu) with
              wooleyResiduesSeparated nu xi eta,
                V nu xi eta alpha) ≤
          ∑ alpha : Fin k → ZMod (p ^ B),
            (p ^ (theta - nu) : ℝ) ^ s *
              ∑ xi : ZMod (p ^ theta),
                ∑ eta : ZMod (p ^ theta) with
                  wooleyResiduesSeparated nu xi eta,
                    V theta xi eta alpha :=
        Finset.sum_le_sum fun alpha _ => hpoint alpha
      _ = (p ^ (theta - nu) : ℝ) ^ s *
          ∑ alpha : Fin k → ZMod (p ^ B),
            ∑ xi : ZMod (p ^ theta),
              ∑ eta : ZMod (p ^ theta) with
                wooleyResiduesSeparated nu xi eta,
                  V theta xi eta alpha := by rw [Finset.mul_sum]
  unfold wooleyMixedGridMean
  split_ifs with hmass
  · simp
  · rw [haggregate nu, haggregate theta]
    have hscale : 0 ≤ gridScale := by
      dsimp [gridScale]
      positivity
    have hinv : 0 ≤ (wooleyWeightedMassSq gamma)⁻¹ ^ 2 := sq_nonneg _
    calc
      (wooleyWeightedMassSq gamma)⁻¹ ^ 2 * (gridScale * P nu) ≤
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            (gridScale * ((p ^ (theta - nu) : ℝ) ^ s * P theta)) := by
        gcongr
      _ = (p ^ (theta - nu) : ℝ) ^ s *
          ((wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            (gridScale * P theta)) := by ring

/-- Wooley Lemma 6.3 as the exact consumer of Lemma 6.1 and the mixed-mean
refinement above.  The constant from the source `≪` relation is retained. -/
theorem wooley_lemma_6_3_of_initial_conditioning
    {Q p nu theta B k s : ℕ} [NeZero p] [NeZero (p ^ B)]
    {C : ℝ} (hC : 0 ≤ C) (hnu : nu ≤ theta) (hs : 2 ≤ s)
    (gamma : Fin Q → ℂ)
    (hinitial :
      wooleyWeightedGridMean s k (p ^ B) gamma ≤
        C * (p ^ nu : ℝ) ^ s *
          wooleyMixedGridMean s k 1 p B nu nu nu gamma) :
    wooleyWeightedGridMean s k (p ^ B) gamma ≤
      C * (p ^ theta : ℝ) ^ s *
        wooleyMixedGridMean s k 1 p B theta theta nu gamma := by
  have hrefine := wooley_mixed_one_refinement
    (Q := Q) (p := p) (nu := nu) (theta := theta)
      (B := B) (k := k) (s := s) hnu hs gamma
  have hKnonneg := wooleyMixedGridMean_nonneg
    s k 1 p B theta theta nu gamma
  calc
    wooleyWeightedGridMean s k (p ^ B) gamma ≤
        C * (p ^ nu : ℝ) ^ s *
          wooleyMixedGridMean s k 1 p B nu nu nu gamma := hinitial
    _ ≤ C * (p ^ nu : ℝ) ^ s *
        ((p ^ (theta - nu) : ℝ) ^ s *
          wooleyMixedGridMean s k 1 p B theta theta nu gamma) := by
      gcongr
    _ = C * (p ^ theta : ℝ) ^ s *
          wooleyMixedGridMean s k 1 p B theta theta nu gamma := by
      have hpowers : (p : ℝ) ^ nu * (p : ℝ) ^ (theta - nu) =
          (p : ℝ) ^ theta := by
        rw [← pow_add, Nat.add_sub_of_le hnu]
      calc
        C * ((p : ℝ) ^ nu) ^ s *
            (((p : ℝ) ^ (theta - nu)) ^ s *
              wooleyMixedGridMean s k 1 p B theta theta nu gamma) =
          C * (((p : ℝ) ^ nu) *
            ((p : ℝ) ^ (theta - nu))) ^ s *
              wooleyMixedGridMean s k 1 p B theta theta nu gamma := by
            rw [mul_pow]
            ring
        _ = C * ((p : ℝ) ^ theta) ^ s *
              wooleyMixedGridMean s k 1 p B theta theta nu gamma := by
            rw [hpowers]

#print axioms wooley_refinement_val_mod
#print axioms wooley_refinements_separated
#print axioms wooley_mixed_one_point_refinement
#print axioms wooley_mixed_one_refinement
#print axioms wooley_lemma_6_3_of_initial_conditioning

end

end GafniTao
