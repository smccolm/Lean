import GafniTao.HeathBrownAtkinsonGramExplicit

/-!
# Exact separated-family Atkinson Gram ledger

This is the finite form of Ivić (7.17) before equation (7.19) is inserted.
The diagonal contribution and the literal, orientation-free off-diagonal
majorant are kept as distinct terms.  In particular, no uniform substitute
for the physical height gaps is assumed.
-/

open Complex Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- The complete ordered off-diagonal mass of the explicit Atkinson
pair-majorant. -/
def heathBrownAtkinsonOffDiagonalMajorantSum
    (K : Nat) (W : Finset Real) : Real :=
  ∑ t ∈ W, ∑ u ∈ W,
    if u = t then 0
    else heathBrownAtkinsonSymmetricGramGapMajorant K t u

theorem heathBrownAtkinsonOffDiagonalMajorantSum_nonneg
    (K : Nat) (W : Finset Real) :
    0 ≤ heathBrownAtkinsonOffDiagonalMajorantSum K W := by
  unfold heathBrownAtkinsonOffDiagonalMajorantSum
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.sum_nonneg
  intro u hu
  split_ifs
  · exact le_rfl
  · exact heathBrownAtkinsonSymmetricGramGapMajorant_nonneg K t u

/-- Exact diagonal/off-diagonal decomposition of the pointwise Gram
majorant on a common dyadic height block. -/
theorem sum_norm_heathBrownAtkinsonGram_le_explicit_offDiagonal
    {K : Nat} {T : Real} (W : Finset Real)
    (hT : 0 < T) (hK : 0 < K)
    (hblock : ((2 * K + 2 : Nat) : Real) ≤ T / 2)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T) :
    (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
      (W.card : Real) * (K : Real) +
        heathBrownAtkinsonOffDiagonalMajorantSum K W := by
  have hpoint : ∀ t ∈ W, ∀ u ∈ W,
      ‖heathBrownAtkinsonGram K t u‖ ≤
        if u = t then (K : Real)
        else heathBrownAtkinsonSymmetricGramGapMajorant K t u := by
    intro t ht u hu
    by_cases hut : u = t
    · subst u
      rw [if_pos rfl, norm_heathBrownAtkinsonGram_self]
    · rw [if_neg hut]
      exact norm_heathBrownAtkinsonGram_le_symmetricGapMajorant
        hT hK hblock (hRange t ht) (hRange u hu) (Ne.symm hut)
  calc
    (∑ t ∈ W, ∑ u ∈ W, ‖heathBrownAtkinsonGram K t u‖) ≤
        ∑ t ∈ W, ∑ u ∈ W,
          (if u = t then (K : Real)
            else heathBrownAtkinsonSymmetricGramGapMajorant K t u) := by
      exact Finset.sum_le_sum fun t ht =>
        Finset.sum_le_sum fun u hu => hpoint t ht u hu
    _ = (W.card : Real) * (K : Real) +
        heathBrownAtkinsonOffDiagonalMajorantSum K W := by
      unfold heathBrownAtkinsonOffDiagonalMajorantSum
      have hrow : ∀ t ∈ W,
          (∑ u ∈ W,
              if u = t then (K : Real)
              else heathBrownAtkinsonSymmetricGramGapMajorant K t u) =
            (K : Real) +
              ∑ u ∈ W,
                if u = t then 0
                else heathBrownAtkinsonSymmetricGramGapMajorant K t u := by
        intro t ht
        calc
          (∑ u ∈ W,
              if u = t then (K : Real)
              else heathBrownAtkinsonSymmetricGramGapMajorant K t u) =
              ∑ u ∈ W,
                ((if u = t then (K : Real) else 0) +
                  if u = t then 0
                  else heathBrownAtkinsonSymmetricGramGapMajorant K t u) := by
            apply Finset.sum_congr rfl
            intro u hu
            by_cases hut : u = t <;> simp [hut]
          _ = (K : Real) +
              ∑ u ∈ W,
                if u = t then 0
                else heathBrownAtkinsonSymmetricGramGapMajorant K t u := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos ht]
      rw [Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul]

/-- Bombieri--Halász with the exact diagonal and explicit off-diagonal gap
ledger.  This is the source-facing finite precursor to Ivić (7.17)--(7.19). -/
theorem heathBrownAtkinson_largeValues_explicit_offDiagonal
    {K : Nat} {T V : Real} {W : Finset Real}
    (hT : 0 < T) (hK : 0 < K) (hV : 0 ≤ V)
    (hblock : ((2 * K + 2 : Nat) : Real) ≤ T / 2)
    (hRange : ∀ t ∈ W, t ∈ Set.Icc (T / 2) T)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖heathBrownAtkinsonSum (K : Real) K t‖) :
    ((W.card : Real) * V) ^ (2 : Nat) ≤
      heathBrownAtkinsonEnergy K *
        ((W.card : Real) * (K : Real) +
          heathBrownAtkinsonOffDiagonalMajorantSum K W) := by
  have hGram := heathBrownAtkinson_halasz_gram hV hLarge
  have hsum := sum_norm_heathBrownAtkinsonGram_le_explicit_offDiagonal
    W hT hK hblock hRange
  have henergy : 0 ≤ heathBrownAtkinsonEnergy K :=
    heathBrownAtkinsonEnergy_nonneg K
  exact hGram.trans (mul_le_mul_of_nonneg_left hsum henergy)


end

end GafniTao
