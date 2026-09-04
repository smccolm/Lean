import GafniTao.WooleyPadicSeparation

/-!
# The easy branch of Wooley Lemma 7.1

This file handles the branch `B' <= nu` of Section 7.  It proves the exact
one-sided refinement of the mixed mean before applying the source's ceiling
and triangular-number exponent estimates.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooley_refinement_val_mod_of_le
    {p nu a a' : ℕ} [NeZero p] (hnua : nu ≤ a) (haa' : a ≤ a')
    (xi : ZMod (p ^ a)) {z : ZMod (p ^ a')}
    (hz : z ∈ wooleyResidueRefinementFiber p a a' haa' xi) :
    z.val % (p ^ nu) = xi.val % (p ^ nu) := by
  have ha := wooley_refinement_val_mod haa' xi hz
  have hdiv : p ^ nu ∣ p ^ a := pow_dvd_pow p hnua
  calc
    z.val % (p ^ nu) = (z.val % (p ^ a)) % (p ^ nu) :=
      (Nat.mod_mod_of_dvd z.val hdiv).symm
    _ = xi.val % (p ^ nu) := by rw [ha]

theorem wooley_refinement_left_separated_iff
    {p nu a a' b : ℕ} [NeZero p] (hnua : nu ≤ a) (haa' : a ≤ a')
    (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b))
    {z : ZMod (p ^ a')}
    (hz : z ∈ wooleyResidueRefinementFiber p a a' haa' xi) :
    wooleyResiduesSeparated nu z eta ↔
      wooleyResiduesSeparated nu xi eta := by
  unfold wooleyResiduesSeparated
  rw [wooley_refinement_val_mod_of_le hnua haa' xi hz]

/-- A heterogeneous, one-sided version of the refinement-fibre identity.
The second residue remains at depth `b`, exactly as in the easy branch of
Wooley Lemma 7.1. -/
theorem wooley_sum_left_refinement
    {p nu a a' b : ℕ} [NeZero p] (hnua : nu ≤ a) (haa' : a ≤ a')
    (F : ZMod (p ^ a') → ZMod (p ^ b) → ℝ) :
    ∑ xi : ZMod (p ^ a),
        ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
          ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi, F z eta =
      ∑ z : ZMod (p ^ a'),
        ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu z eta,
          F z eta := by
  classical
  let red : ZMod (p ^ a') → ZMod (p ^ a) :=
    ZMod.castHom (pow_dvd_pow p haa') (ZMod (p ^ a))
  have href (z : ZMod (p ^ a')) (xi : ZMod (p ^ a)) :
      z ∈ wooleyResidueRefinementFiber p a a' haa' xi ↔ red z = xi := by
    simp [wooleyResidueRefinementFiber, red]
  have hsep (z : ZMod (p ^ a')) (eta : ZMod (p ^ b)) :
      wooleyResiduesSeparated nu (red z) eta ↔
        wooleyResiduesSeparated nu z eta := by
    exact (wooley_refinement_left_separated_iff hnua haa'
      (red z) eta ((href z (red z)).2 rfl)).symm
  have hfixed (eta : ZMod (p ^ b)) :
      (∑ xi : ZMod (p ^ a),
          if wooleyResiduesSeparated nu xi eta then
            ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
              F z eta else 0) =
        ∑ z : ZMod (p ^ a'),
          if wooleyResiduesSeparated nu z eta then F z eta else 0 := by
    let fine : Finset (ZMod (p ^ a')) :=
      Finset.univ.filter fun z => wooleyResiduesSeparated nu z eta
    have hfiber (xi : ZMod (p ^ a)) :
        fine.filter (fun z => red z = xi) =
          if wooleyResiduesSeparated nu xi eta then
            wooleyResidueRefinementFiber p a a' haa' xi else ∅ := by
      ext z
      simp only [Finset.mem_filter]
      dsimp [fine]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hxi : wooleyResiduesSeparated nu xi eta
      · rw [if_pos hxi]
        constructor
        · rintro ⟨hzsep, hzred⟩
          exact (href z xi).2 hzred
        · intro hz
          have hzred := (href z xi).1 hz
          exact ⟨(hsep z eta |>.1 (by simpa only [hzred] using hxi)), hzred⟩
      · rw [if_neg hxi]
        simp only [Finset.notMem_empty, iff_false]
        rintro ⟨hzsep, hzred⟩
        apply hxi
        have hzcoarse := (hsep z eta).2 hzsep
        simpa only [hzred] using hzcoarse
    have hgroup := Finset.sum_fiberwise fine red (fun z => F z eta)
    calc
      _ = ∑ xi : ZMod (p ^ a),
          ∑ z ∈ fine with red z = xi, F z eta := by
            simp_rw [hfiber]
            apply Finset.sum_congr rfl
            intro xi hxiMem
            by_cases hxi : wooleyResiduesSeparated nu xi eta
            · simp only [hxi, if_true]
            · simp only [hxi, if_false, Finset.sum_empty]
      _ = ∑ z ∈ fine, F z eta := hgroup
      _ = _ := by simp [fine, Finset.sum_filter]
  simp_rw [Finset.sum_filter]
  calc
    (∑ xi : ZMod (p ^ a),
        ∑ eta : ZMod (p ^ b),
          if wooleyResiduesSeparated nu xi eta then
            ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
              F z eta else 0) =
        ∑ eta : ZMod (p ^ b),
          ∑ xi : ZMod (p ^ a),
            if wooleyResiduesSeparated nu xi eta then
              ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
                F z eta else 0 := Finset.sum_comm
    _ = ∑ eta : ZMod (p ^ b),
        ∑ z : ZMod (p ^ a'),
          if wooleyResiduesSeparated nu z eta then F z eta else 0 := by
            exact Finset.sum_congr rfl fun eta _ => hfixed eta
    _ = ∑ z : ZMod (p ^ a'),
        ∑ eta : ZMod (p ^ b),
          if wooleyResiduesSeparated nu z eta then F z eta else 0 :=
      Finset.sum_comm

theorem wooleyPolynomial_mixed_left_point_refinement
    {Q p a a' b B k s r : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (haa' : a ≤ a')
    (hR : 1 ≤ wooleyTriangular r)
    (gamma : Fin Q → ℂ) (xi : ZMod (p ^ a))
    (eta : ZMod (p ^ b)) :
    wooleyWeightedResidueMassSq gamma xi *
        wooleyWeightedResidueMassSq gamma eta *
          wooleyPolynomialMixedResidueGridMoment
            phi s r p B a b gamma xi eta ≤
      (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
        ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
          wooleyWeightedResidueMassSq gamma z *
            wooleyWeightedResidueMassSq gamma eta *
              wooleyPolynomialMixedResidueGridMoment
                phi s r p B a' b gamma z eta := by
  let scale : ℝ := (((p ^ B) ^ k : ℕ) : ℝ)⁻¹
  unfold wooleyPolynomialMixedResidueGridMoment
  have hper (alpha : Fin k → ZMod (p ^ B)) :
      wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta *
          (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
            (‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha xi‖ ^ (2 * wooleyTriangular r) *
              ‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha eta‖ ^
                (2 * (s - wooleyTriangular r)))) ≤
        (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
          ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
            wooleyWeightedResidueMassSq gamma z *
              wooleyWeightedResidueMassSq gamma eta *
                (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                  (‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha z‖ ^
                        (2 * wooleyTriangular r) *
                    ‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha eta‖ ^
                        (2 * (s - wooleyTriangular r)))) := by
    have hpoint := wooleyPolynomial_lemma_6_2
      (Q := Q) (p := p) (a := a) (b := a') (qB := p ^ B)
      (k := k) (w := wooleyTriangular r) phi haa' hR gamma alpha xi
    have hv : 0 ≤ wooleyWeightedResidueMassSq gamma eta *
        ‖wooleyPolynomialNormalizedResidueGridSum
          phi (p ^ B) gamma alpha eta‖ ^
            (2 * (s - wooleyTriangular r)) := by
      exact mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma eta)
        (by positivity)
    have hs : 0 ≤ scale := by dsimp [scale]; positivity
    have hm := mul_le_mul_of_nonneg_right hpoint hv
    have hsm := mul_le_mul_of_nonneg_left hm hs
    dsimp [scale] at hsm
    calc
      wooleyWeightedResidueMassSq gamma xi *
            wooleyWeightedResidueMassSq gamma eta *
            (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
              (‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha xi‖ ^ (2 * wooleyTriangular r) *
                ‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha eta‖ ^
                  (2 * (s - wooleyTriangular r)))) =
        (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
          ((wooleyWeightedResidueMassSq gamma xi *
            ‖wooleyPolynomialNormalizedResidueGridSum
              phi (p ^ B) gamma alpha xi‖ ^ (2 * wooleyTriangular r)) *
            (wooleyWeightedResidueMassSq gamma eta *
              ‖wooleyPolynomialNormalizedResidueGridSum
                phi (p ^ B) gamma alpha eta‖ ^
                    (2 * (s - wooleyTriangular r))))) := by ring
      _ ≤ (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
        (((p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
          ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
            wooleyWeightedResidueMassSq gamma z *
              ‖wooleyPolynomialNormalizedResidueGridSum
                phi (p ^ B) gamma alpha z‖ ^ (2 * wooleyTriangular r)) *
          (wooleyWeightedResidueMassSq gamma eta *
            ‖wooleyPolynomialNormalizedResidueGridSum
              phi (p ^ B) gamma alpha eta‖ ^
                  (2 * (s - wooleyTriangular r))))) := hsm
      _ = (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
        ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
          wooleyWeightedResidueMassSq gamma z *
            wooleyWeightedResidueMassSq gamma eta *
              (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                (‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha z‖ ^
                      (2 * wooleyTriangular r) *
                  ‖wooleyPolynomialNormalizedResidueGridSum
                    phi (p ^ B) gamma alpha eta‖ ^
                        (2 * (s - wooleyTriangular r)))) := by
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
  simp_rw [Finset.mul_sum]
  calc
    ∑ alpha : Fin k → ZMod (p ^ B),
        wooleyWeightedResidueMassSq gamma xi *
          wooleyWeightedResidueMassSq gamma eta *
            (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
              (‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha xi‖ ^ (2 * wooleyTriangular r) *
                ‖wooleyPolynomialNormalizedResidueGridSum
                  phi (p ^ B) gamma alpha eta‖ ^
                    (2 * (s - wooleyTriangular r)))) ≤
      ∑ alpha : Fin k → ZMod (p ^ B),
        (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
          ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
            wooleyWeightedResidueMassSq gamma z *
              wooleyWeightedResidueMassSq gamma eta *
                (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                  (‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha z‖ ^
                        (2 * wooleyTriangular r) *
                    ‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha eta‖ ^
                        (2 * (s - wooleyTriangular r)))) :=
      Finset.sum_le_sum fun alpha _ => hper alpha
    _ = ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
        ∑ alpha : Fin k → ZMod (p ^ B),
          (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
            (wooleyWeightedResidueMassSq gamma z *
              wooleyWeightedResidueMassSq gamma eta *
                (((((p ^ B) ^ k : ℕ) : ℝ))⁻¹ *
                  (‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha z‖ ^
                        (2 * wooleyTriangular r) *
                    ‖wooleyPolynomialNormalizedResidueGridSum
                      phi (p ^ B) gamma alpha eta‖ ^
                        (2 * (s - wooleyTriangular r))))) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

/-- The exact easy-branch refinement preceding the final estimate in
Wooley Lemma 7.1. -/
theorem wooleyPolynomial_section7_easy_refinement
    {Q p nu a a' b B k s r : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (hnua : nu ≤ a) (haa' : a ≤ a')
    (hR : 1 ≤ wooleyTriangular r) (gamma : Fin Q → ℂ) :
    wooleyPolynomialMixedGridMean phi s r p B a b nu gamma ≤
      (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
        wooleyPolynomialMixedGridMean phi s r p B a' b nu gamma := by
  unfold wooleyPolynomialMixedGridMean
  split_ifs with hmass
  · simp
  · have hlocal (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) :=
      wooleyPolynomial_mixed_left_point_refinement
        (Q := Q) (p := p) (a := a) (a' := a')
        (b := b) (B := B) (k := k) (s := s) (r := r)
        phi haa' hR gamma xi eta
    have hsum :
        (∑ xi : ZMod (p ^ a),
          ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
            wooleyWeightedResidueMassSq gamma xi *
              wooleyWeightedResidueMassSq gamma eta *
                wooleyPolynomialMixedResidueGridMoment
                  phi s r p B a b gamma xi eta) ≤
          (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
            ∑ z : ZMod (p ^ a'),
              ∑ eta : ZMod (p ^ b) with
                wooleyResiduesSeparated nu z eta,
                  wooleyWeightedResidueMassSq gamma z *
                    wooleyWeightedResidueMassSq gamma eta *
                      wooleyPolynomialMixedResidueGridMoment
                        phi s r p B a' b gamma z eta := by
      calc
        _ ≤ ∑ xi : ZMod (p ^ a),
            ∑ eta : ZMod (p ^ b) with wooleyResiduesSeparated nu xi eta,
              (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
                ∑ z ∈ wooleyResidueRefinementFiber p a a' haa' xi,
                  wooleyWeightedResidueMassSq gamma z *
                    wooleyWeightedResidueMassSq gamma eta *
                      wooleyPolynomialMixedResidueGridMoment
                        phi s r p B a' b gamma z eta := by
              exact Finset.sum_le_sum fun xi _ =>
                Finset.sum_le_sum fun eta _ => hlocal xi eta
        _ = _ := by
          rw [← wooley_sum_left_refinement hnua haa'
            (fun z eta =>
              wooleyWeightedResidueMassSq gamma z *
                wooleyWeightedResidueMassSq gamma eta *
                  wooleyPolynomialMixedResidueGridMoment
                    phi s r p B a' b gamma z eta)]
          simp_rw [Finset.mul_sum]
    have hinv : 0 ≤ (wooleyWeightedMassSq gamma)⁻¹ ^ 2 := sq_nonneg _
    calc
      (wooleyWeightedMassSq gamma)⁻¹ ^ 2 * _ ≤
          (wooleyWeightedMassSq gamma)⁻¹ ^ 2 *
            ((p ^ (a' - a) : ℝ) ^ wooleyTriangular r * _) := by
        exact mul_le_mul_of_nonneg_left hsum hinv
      _ = (p ^ (a' - a) : ℝ) ^ wooleyTriangular r *
          ((wooleyWeightedMassSq gamma)⁻¹ ^ 2 * _) := by ring

theorem wooley_section7_easy_exponent_nat
    {k r a b gamma nu : ℕ}
    (hr : 1 ≤ r) (hrk : r < k) (hnu : 1 ≤ nu)
    (haa' : a ≤ wooleySection7NextB k r b)
    (hgamma : gamma < nu)
    (hBPrime : wooleySection7BPrimeInt k r a b gamma ≤ (nu : ℤ)) :
    (wooleySection7NextB k r b - a) * wooleyTriangular r ≤
      k ^ 2 * nu := by
  let n : ℕ := (k - r + 1) * b
  let d : ℕ := wooleySection7NextB k r b - a
  have hnInt :
      (n : ℤ) - (r : ℤ) * (a : ℤ) -
          ((k - r : ℕ) : ℤ) * (gamma : ℤ) ≤ (nu : ℤ) := by
    simpa [wooleySection7BPrimeInt, n, Nat.cast_mul] using hBPrime
  have hnNat : n ≤ r * a + (k - r) * gamma + nu := by
    exact_mod_cast (show (n : ℤ) ≤
      (r * a + (k - r) * gamma + nu : ℕ) by omega)
  have htail : (k - r) * gamma + nu ≤ k * nu := by
    have hkr1 : k - r + 1 ≤ k := by omega
    calc
      (k - r) * gamma + nu ≤ (k - r) * nu + nu := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left (k - r) hgamma.le) nu
      _ = (k - r + 1) * nu := by rw [Nat.add_mul, one_mul]
      _ ≤ k * nu := Nat.mul_le_mul_right nu hkr1
  have hceil := wooley_section7_nextB_mul_upper
    (k := k) (r := r) (b := b) hr
  have hrd : r * d ≤ k * nu + r := by
    have htotal :
        r * wooleySection7NextB k r b ≤ r * a + k * nu + r := by
      calc
        r * wooleySection7NextB k r b ≤ n + r := by simpa [n] using hceil
        _ ≤ (r * a + (k - r) * gamma + nu) + r :=
          Nat.add_le_add_right hnNat r
        _ ≤ r * a + k * nu + r := by omega
    have hbdecomp : a + d = wooleySection7NextB k r b := by
      exact Nat.add_sub_of_le haa'
    have hmuldecomp :
        r * wooleySection7NextB k r b = r * a + r * d := by
      rw [← hbdecomp, Nat.mul_add]
    omega
  have hRtwo : 2 * wooleyTriangular r ≤ r * k := by
    calc
      2 * wooleyTriangular r ≤ r * (r + 1) := by
        simp only [wooleyTriangular]
        exact Nat.mul_div_le _ _
      _ ≤ r * k := Nat.mul_le_mul_left r hrk
  have htwice :
      2 * (d * wooleyTriangular r) ≤ d * r * k := by
    calc
      2 * (d * wooleyTriangular r) = d * (2 * wooleyTriangular r) := by ring
      _ ≤ d * (r * k) := Nat.mul_le_mul_left d hRtwo
      _ = d * r * k := by ring
  have hmiddle : d * r * k ≤ (k * nu + r) * k := by
    have := Nat.mul_le_mul_right k hrd
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using this
  have hkk : k * k ≤ k * nu * k := by
    have hknu : k ≤ k * nu := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hnu
    exact Nat.mul_le_mul_right k hknu
  have hlast : (k * nu + r) * k ≤ 2 * (k ^ 2 * nu) := by
    calc
      (k * nu + r) * k = k * nu * k + r * k := by ring
      _ ≤ k * nu * k + k * k := by
        exact Nat.add_le_add_left (Nat.mul_le_mul_right k hrk.le) _
      _ ≤ k * nu * k + k * nu * k := Nat.add_le_add_left hkk _
      _ = 2 * (k ^ 2 * nu) := by ring
  have htwo : 2 * (d * wooleyTriangular r) ≤
      2 * (k ^ 2 * nu) := htwice.trans (hmiddle.trans hlast)
  exact le_of_mul_le_mul_left htwo (by norm_num)

theorem wooleyPolynomialMixedGridMean_nonneg
    {Q p B k s r a b nu : ℕ} [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (gamma : Fin Q → ℂ) :
    0 ≤ wooleyPolynomialMixedGridMean phi s r p B a b nu gamma := by
  unfold wooleyPolynomialMixedGridMean
  split_ifs
  · simp
  · apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intro xi hxi
    apply Finset.sum_nonneg
    intro eta heta
    exact mul_nonneg
      (mul_nonneg (wooleyWeightedResidueMassSq_nonneg gamma xi)
        (wooleyWeightedResidueMassSq_nonneg gamma eta))
      (by unfold wooleyPolynomialMixedResidueGridMoment; positivity)

/-- Wooley Lemma 7.1 in the branch `B' <= nu`.  The conclusion is the
literal source majorant, not merely the preceding refinement factor. -/
theorem wooleyPolynomial_section7_easy
    {Q p nu a b B k s r gammaVal : ℕ}
    [NeZero p] [NeZero (p ^ B)]
    (phi : WooleyPolynomialSystem k) (hp : 2 ≤ p)
    (hr : 1 ≤ r) (hrk : r < k) (hnu : 1 ≤ nu)
    (hnua : nu ≤ a)
    (haa' : a ≤ wooleySection7NextB k r b)
    (hgamma : gammaVal < nu)
    (hBPrime : wooleySection7BPrimeInt k r a b gammaVal ≤ (nu : ℤ))
    (gamma : Fin Q → ℂ) :
    wooleyPolynomialMixedGridMean phi s r p B a b nu gamma ≤
      (p : ℝ) ^ (k ^ 2 * nu) *
        wooleyPolynomialMixedGridMean
          phi s r p B (wooleySection7NextB k r b) b nu gamma := by
  have hR : 1 ≤ wooleyTriangular r := by
    simp only [wooleyTriangular]
    have : 2 ≤ r * (r + 1) := by nlinarith
    omega
  have hrefine := wooleyPolynomial_section7_easy_refinement
    (Q := Q) (p := p) (nu := nu) (a := a)
    (a' := wooleySection7NextB k r b) (b := b) (B := B)
    (k := k) (s := s) (r := r) phi hnua haa' hR gamma
  have hexpNat := wooley_section7_easy_exponent_nat
    hr hrk hnu haa' hgamma hBPrime
  have hpReal : 1 ≤ (p : ℝ) := by
    exact_mod_cast (show 1 ≤ p by omega)
  have hpow :
      ((p : ℝ) ^ (wooleySection7NextB k r b - a)) ^
          wooleyTriangular r ≤
        (p : ℝ) ^ (k ^ 2 * nu) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hpReal hexpNat
  have hmean : 0 ≤ wooleyPolynomialMixedGridMean
      phi s r p B (wooleySection7NextB k r b) b nu gamma :=
    wooleyPolynomialMixedGridMean_nonneg phi gamma
  exact hrefine.trans (mul_le_mul_of_nonneg_right hpow hmean)

#print axioms wooley_refinement_val_mod_of_le
#print axioms wooley_sum_left_refinement
#print axioms wooleyPolynomial_mixed_left_point_refinement
#print axioms wooleyPolynomial_section7_easy_refinement
#print axioms wooley_section7_easy_exponent_nat
#print axioms wooleyPolynomialMixedGridMean_nonneg
#print axioms wooleyPolynomial_section7_easy

end

end GafniTao
