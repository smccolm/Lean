import Tao2026.NormalizedBadIntervals

/-!
# Finite maximal-function reduction for bad intervals

This module places the normalized-subinterval theorem into the finite-union
form used immediately after Tao's Lemma 6.2.  It proves the pointwise density
certificate behind the Hardy--Littlewood maximal-function step.  The remaining
analytic/combinatorial input is only the discrete weak `(1,1)` inequality for
these interval averages.
-/

namespace Tao2026

/-- A natural interval enlarged by `R` points on both sides (with truncation at
zero on the left). -/
def expandedConsecutiveInterval (N H R : ℕ) : Finset ℕ :=
  Finset.Icc (N - R) (N + H + R)

theorem card_expandedConsecutiveInterval_le (N H R : ℕ) :
    (expandedConsecutiveInterval N H R).card ≤ H + 2 * R + 1 := by
  simp only [expandedConsecutiveInterval, Nat.card_Icc]
  omega

theorem consecutiveInterval_subset_expandedConsecutiveInterval
    (N H R : ℕ) :
    consecutiveInterval N H ⊆ expandedConsecutiveInterval N H R := by
  intro n hn
  simp only [consecutiveInterval, expandedConsecutiveInterval,
    Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
  omega

/-- If a subinterval has more than one quarter of its parent's length, the
whole parent lies in the four-radius enlargement of the child. -/
theorem consecutiveInterval_subset_four_mul_expanded_of_large_subinterval
    {N H N' H' : ℕ}
    (hsub : consecutiveInterval N' H' ⊆ consecutiveInterval N H)
    (hlarge : H < 4 * H') :
    consecutiveInterval N H ⊆
      expandedConsecutiveInterval N' H' (4 * H') := by
  have hfirst : N' + 1 ∈ consecutiveInterval N' H' := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  have hlast : N' + H' ∈ consecutiveInterval N' H' := by
    simp only [consecutiveInterval, Finset.mem_Ioc]
    omega
  have hfirstParent := hsub hfirst
  have hlastParent := hsub hlast
  simp only [consecutiveInterval, Finset.mem_Ioc] at hfirstParent hlastParent
  intro n hn
  simp only [consecutiveInterval, expandedConsecutiveInterval,
    Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
  omega

/-- Bounded parameter set for the admissible intervals at dyadic parameter
`x`.  Lemma 6.1 proves that every admissible pair occurs in this box. -/
noncomputable def admissibleBadIntervalIndices (x : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range x).product (Finset.range x)).filter fun NH =>
    IsAdmissibleBadInterval x NH.1 NH.2

theorem mem_admissibleBadIntervalIndices {x N H : ℕ} :
    (N, H) ∈ admissibleBadIntervalIndices x ↔
      N < x ∧ H < x ∧ IsAdmissibleBadInterval x N H := by
  classical
  simp [admissibleBadIntervalIndices, and_assoc]

/-- The finite union of all admissible intervals at parameter `x`. -/
noncomputable def admissibleBadIntervalUnion (x : ℕ) : Finset ℕ := by
  classical
  exact (admissibleBadIntervalIndices x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem mem_admissibleBadIntervalUnion {x n : ℕ} :
    n ∈ admissibleBadIntervalUnion x ↔
      ∃ N H : ℕ, N < x ∧ H < x ∧
        IsAdmissibleBadInterval x N H ∧
        n ∈ consecutiveInterval N H := by
  classical
  simp only [admissibleBadIntervalUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨NH, hNH, hn⟩
    obtain ⟨hN, hH, hadm⟩ := mem_admissibleBadIntervalIndices.mp hNH
    exact ⟨NH.1, NH.2, hN, hH, hadm, hn⟩
  · rintro ⟨N, H, hN, hH, hadm, hn⟩
    exact ⟨(N, H), mem_admissibleBadIntervalIndices.mpr
      ⟨hN, hH, hadm⟩, hn⟩

/-- A normalized interval at a scale comparable with `x`, using the exact
replacement bounds furnished by the corrected Lemma 6.2. -/
def IsScaleNormalizedBadInterval (x N H : ℕ) : Prop :=
  ∃ p k m : ℕ, IsNormalizedBadInterval N H p k m ∧
    x ≤ 4 * N + 1 ∧ N + H ≤ 2 * x

/-- Bounded parameter set for comparable-scale normalized intervals. -/
noncomputable def scaleNormalizedBadIntervalIndices (x : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (2 * x)).product (Finset.range x)).filter fun NH =>
    IsScaleNormalizedBadInterval x NH.1 NH.2

theorem mem_scaleNormalizedBadIntervalIndices {x N H : ℕ} :
    (N, H) ∈ scaleNormalizedBadIntervalIndices x ↔
      N < 2 * x ∧ H < x ∧ IsScaleNormalizedBadInterval x N H := by
  classical
  simp [scaleNormalizedBadIntervalIndices, and_assoc]

/-- The finite union of all comparable-scale normalized bad intervals. -/
noncomputable def scaleNormalizedBadIntervalUnion (x : ℕ) : Finset ℕ := by
  classical
  exact (scaleNormalizedBadIntervalIndices x).biUnion fun NH =>
    consecutiveInterval NH.1 NH.2

theorem consecutiveInterval_subset_scaleNormalizedBadIntervalUnion
    {x N H : ℕ} (hNH : (N, H) ∈ scaleNormalizedBadIntervalIndices x) :
    consecutiveInterval N H ⊆ scaleNormalizedBadIntervalUnion x := by
  classical
  intro n hn
  exact Finset.mem_biUnion.mpr ⟨(N, H), hNH, hn⟩

/-- Exact pointwise precursor to the discrete Hardy--Littlewood maximal
inequality.  Every point of the admissible union has an interval around it on
which the normalized union occupies at least one tenth of the lattice points,
expressed without division as `#I ≤ 10 #(`normalized union` ∩ I)`.

The only arithmetic input is the isolated Sylvester--Schur conclusion already
used in Lemma 6.1. -/
theorem exists_expanded_normalized_density_of_mem_admissibleBadIntervalUnion
    (hSS : SylvesterSchurConclusion) {x n : ℕ}
    (hn : n ∈ admissibleBadIntervalUnion x) :
    ∃ N' H' : ℕ,
      (N', H') ∈ scaleNormalizedBadIntervalIndices x ∧
      n ∈ expandedConsecutiveInterval N' H' (4 * H') ∧
      (expandedConsecutiveInterval N' H' (4 * H')).card ≤
        10 * ((scaleNormalizedBadIntervalUnion x) ∩
          expandedConsecutiveInterval N' H' (4 * H')).card := by
  obtain ⟨N, H, hNltx, hHltx, hadm, hnParent⟩ :=
    mem_admissibleBadIntervalUnion.mp hn
  obtain ⟨N', H', p, k, m, hnorm, hsub, hH'leH, hHfour,
      hxLower, hxUpper⟩ :=
    exists_large_normalized_bad_subinterval_of_sylvesterSchur hSS hadm
  have hN'lt : N' < 2 * x := by
    have hH'pos : 0 < H' := by omega
    omega
  have hH'ltx : H' < x := hH'leH.trans_lt hHltx
  have hindex : (N', H') ∈ scaleNormalizedBadIntervalIndices x := by
    apply mem_scaleNormalizedBadIntervalIndices.mpr
    exact ⟨hN'lt, hH'ltx, p, k, m, hnorm, hxLower, hxUpper⟩
  have hnExpanded : n ∈ expandedConsecutiveInterval N' H' (4 * H') :=
    consecutiveInterval_subset_four_mul_expanded_of_large_subinterval
      hsub hHfour hnParent
  have hchildUnion :
      consecutiveInterval N' H' ⊆ scaleNormalizedBadIntervalUnion x :=
    consecutiveInterval_subset_scaleNormalizedBadIntervalUnion hindex
  have hchildExpanded :
      consecutiveInterval N' H' ⊆
        expandedConsecutiveInterval N' H' (4 * H') :=
    consecutiveInterval_subset_expandedConsecutiveInterval N' H' (4 * H')
  have hchildInter :
      consecutiveInterval N' H' ⊆
        (scaleNormalizedBadIntervalUnion x) ∩
          expandedConsecutiveInterval N' H' (4 * H') := by
    intro j hj
    exact Finset.mem_inter.mpr ⟨hchildUnion hj, hchildExpanded hj⟩
  have hchildCard : (consecutiveInterval N' H').card = H' := by
    simp [consecutiveInterval]
  have hinterLower : H' ≤
      ((scaleNormalizedBadIntervalUnion x) ∩
        expandedConsecutiveInterval N' H' (4 * H')).card := by
    calc
      H' = (consecutiveInterval N' H').card := hchildCard.symm
      _ ≤ _ := Finset.card_le_card hchildInter
  have hexpandedUpper :
      (expandedConsecutiveInterval N' H' (4 * H')).card ≤ 9 * H' + 1 := by
    refine (card_expandedConsecutiveInterval_le N' H' (4 * H')).trans ?_
    omega
  refine ⟨N', H', hindex, hnExpanded, ?_⟩
  have hH'pos : 1 ≤ H' := by omega
  omega

/-! ## A finite one-dimensional covering lemma -/

/-- A closed natural interval indexed by its two endpoints. -/
def closedNatInterval (ab : ℕ × ℕ) : Finset ℕ :=
  Finset.Icc ab.1 ab.2

/-- Its natural endpoint length.  This agrees with the cardinality when the
endpoints are ordered. -/
def closedNatIntervalLength (ab : ℕ × ℕ) : ℕ :=
  ab.2 + 1 - ab.1

/-- The threefold enlargement used in the greedy one-dimensional covering
argument. -/
def tripleClosedNatInterval (ab : ℕ × ℕ) : Finset ℕ :=
  Finset.Icc (ab.1 - closedNatIntervalLength ab)
    (ab.2 + closedNatIntervalLength ab)

theorem card_closedNatInterval (ab : ℕ × ℕ) :
    (closedNatInterval ab).card = closedNatIntervalLength ab := by
  simp [closedNatInterval, closedNatIntervalLength, Nat.card_Icc]

theorem card_tripleClosedNatInterval_le {ab : ℕ × ℕ}
    (hab : ab.1 ≤ ab.2) :
    (tripleClosedNatInterval ab).card ≤
      3 * closedNatIntervalLength ab := by
  simp only [tripleClosedNatInterval, Nat.card_Icc,
    closedNatIntervalLength]
  omega

theorem closedNatInterval_subset_tripleClosedNatInterval (ab : ℕ × ℕ) :
    closedNatInterval ab ⊆ tripleClosedNatInterval ab := by
  intro n hn
  simp only [closedNatInterval, Finset.mem_Icc] at hn
  simp only [tripleClosedNatInterval, Finset.mem_Icc]
  exact ⟨(Nat.sub_le _ _).trans hn.1, hn.2.trans (Nat.le_add_right _ _)⟩

/-- Any no-longer interval meeting `ab` is contained in the threefold
enlargement of `ab`. -/
theorem closedNatInterval_subset_triple_of_not_disjoint
    {ab cd : ℕ × ℕ} (hab : ab.1 ≤ ab.2) (hcd : cd.1 ≤ cd.2)
    (hlen : closedNatIntervalLength cd ≤ closedNatIntervalLength ab)
    (hinter : ¬Disjoint (closedNatInterval ab) (closedNatInterval cd)) :
    closedNatInterval cd ⊆ tripleClosedNatInterval ab := by
  rw [Finset.not_disjoint_iff] at hinter
  obtain ⟨z, hzab, hzcd⟩ := hinter
  have hLab : ab.1 + closedNatIntervalLength ab = ab.2 + 1 := by
    rw [closedNatIntervalLength, Nat.add_sub_of_le]
    omega
  have hLcd : cd.1 + closedNatIntervalLength cd = cd.2 + 1 := by
    rw [closedNatIntervalLength, Nat.add_sub_of_le]
    omega
  intro n hn
  simp only [closedNatInterval, Finset.mem_Icc] at hzab hzcd hn
  simp only [tripleClosedNatInterval, Finset.mem_Icc,
    closedNatIntervalLength]
  omega

/-- Finite greedy interval selection: from any finite family of valid closed
natural intervals, select pairwise disjoint members whose threefold
enlargements cover the original union. -/
theorem exists_disjoint_closedIntervals_cover_by_triples
    (f : Finset (ℕ × ℕ)) (hvalid : ∀ ab ∈ f, ab.1 ≤ ab.2) :
    ∃ g : Finset (ℕ × ℕ),
      g ⊆ f ∧
      (∀ ab ∈ g, ∀ cd ∈ g, ab ≠ cd →
        Disjoint (closedNatInterval ab) (closedNatInterval cd)) ∧
      f.biUnion closedNatInterval ⊆
        g.biUnion tripleClosedNatInterval := by
  classical
  induction f using Finset.strongInductionOn with
  | _ f ih =>
      by_cases hf : f = ∅
      · subst f
        exact ⟨∅, by simp, by simp, by simp⟩
      · have hfne : f.Nonempty := Finset.nonempty_iff_ne_empty.mpr hf
        obtain ⟨ab, habf, habMax⟩ :=
          f.exists_max_image closedNatIntervalLength hfne
        let rest := (f.erase ab).filter fun cd =>
          Disjoint (closedNatInterval ab) (closedNatInterval cd)
        have hrestSub : rest ⊆ f := by
          intro cd hcd
          exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hcd).1
        have habNotRest : ab ∉ rest := by
          simp [rest]
        have hrestProper : rest ⊂ f := by
          apply Finset.ssubset_iff_subset_ne.mpr
          refine ⟨hrestSub, ?_⟩
          intro heq
          exact habNotRest (heq ▸ habf)
        have hvalidRest : ∀ cd ∈ rest, cd.1 ≤ cd.2 := by
          intro cd hcd
          exact hvalid cd (hrestSub hcd)
        obtain ⟨g, hgSub, hgPairwise, hgCover⟩ :=
          ih rest hrestProper hvalidRest
        refine ⟨insert ab g, Finset.insert_subset habf
          (hgSub.trans hrestSub), ?_, ?_⟩
        · intro cd hcd ef hef hcdene
          simp only [Finset.mem_insert] at hcd hef
          rcases hcd with rfl | hcd
          · rcases hef with rfl | hef
            · exact (hcdene rfl).elim
            · have hefRest := hgSub hef
              exact (Finset.mem_filter.mp hefRest).2
          · rcases hef with rfl | hef
            · have hcdRest := hgSub hcd
              exact (Finset.mem_filter.mp hcdRest).2.symm
            · exact hgPairwise cd hcd ef hef hcdene
        · intro n hn
          obtain ⟨cd, hcdf, hncd⟩ := Finset.mem_biUnion.mp hn
          by_cases hcdab : cd = ab
          · subst cd
            exact Finset.mem_biUnion.mpr ⟨ab, Finset.mem_insert_self ab g,
              closedNatInterval_subset_tripleClosedNatInterval ab hncd⟩
          · by_cases hdisj :
                Disjoint (closedNatInterval ab) (closedNatInterval cd)
            · have hcdRest : cd ∈ rest := by
                apply Finset.mem_filter.mpr
                exact ⟨Finset.mem_erase.mpr ⟨hcdab, hcdf⟩, hdisj⟩
              have hnRest : n ∈ rest.biUnion closedNatInterval :=
                Finset.mem_biUnion.mpr ⟨cd, hcdRest, hncd⟩
              obtain ⟨ef, hefg, hnef⟩ :=
                Finset.mem_biUnion.mp (hgCover hnRest)
              exact Finset.mem_biUnion.mpr
                ⟨ef, Finset.mem_insert_of_mem hefg, hnef⟩
            · have hcdSub :=
                closedNatInterval_subset_triple_of_not_disjoint
                  (hvalid ab habf) (hvalid cd hcdf)
                  (habMax cd hcdf) hdisj
              exact Finset.mem_biUnion.mpr ⟨ab, Finset.mem_insert_self ab g,
                hcdSub hncd⟩

/-- Finite uncentered weak-`(1,1)` inequality for natural intervals.  If each
interval in a finite family contains at least a `1/K` proportion of a finite
set `s`, then their union has cardinality at most `3K #s`. -/
theorem card_biUnion_closedNatInterval_le_of_density
    (f : Finset (ℕ × ℕ)) (s : Finset ℕ) (K : ℕ)
    (hvalid : ∀ ab ∈ f, ab.1 ≤ ab.2)
    (hdense : ∀ ab ∈ f,
      closedNatIntervalLength ab ≤
        K * (s ∩ closedNatInterval ab).card) :
    (f.biUnion closedNatInterval).card ≤ 3 * K * s.card := by
  classical
  obtain ⟨g, hgSub, hgPairwise, hgCover⟩ :=
    exists_disjoint_closedIntervals_cover_by_triples f hvalid
  have hgValid : ∀ ab ∈ g, ab.1 ≤ ab.2 := by
    intro ab hab
    exact hvalid ab (hgSub hab)
  have hpairInter : (g : Set (ℕ × ℕ)).PairwiseDisjoint fun ab =>
      s ∩ closedNatInterval ab := by
    intro ab hab cd hcd habne
    exact (hgPairwise ab hab cd hcd habne).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hinterUnionSub :
      g.biUnion (fun ab => s ∩ closedNatInterval ab) ⊆ s := by
    intro n hn
    obtain ⟨ab, _hab, hnInter⟩ := Finset.mem_biUnion.mp hn
    exact (Finset.mem_inter.mp hnInter).1
  have hsumInter :
      (∑ ab ∈ g, (s ∩ closedNatInterval ab).card) ≤ s.card := by
    rw [← Finset.card_biUnion hpairInter]
    exact Finset.card_le_card hinterUnionSub
  have hsumTriple :
      (∑ ab ∈ g, (tripleClosedNatInterval ab).card) ≤
        (3 * K) * ∑ ab ∈ g, (s ∩ closedNatInterval ab).card := by
    calc
      (∑ ab ∈ g, (tripleClosedNatInterval ab).card)
          ≤ ∑ ab ∈ g, (3 * K) * (s ∩ closedNatInterval ab).card := by
            apply Finset.sum_le_sum
            intro ab hab
            calc
              (tripleClosedNatInterval ab).card
                  ≤ 3 * closedNatIntervalLength ab :=
                    card_tripleClosedNatInterval_le (hgValid ab hab)
              _ ≤ 3 * (K * (s ∩ closedNatInterval ab).card) :=
                Nat.mul_le_mul_left 3 (hdense ab (hgSub hab))
              _ = (3 * K) * (s ∩ closedNatInterval ab).card := by
                simp [mul_assoc]
      _ = (3 * K) * ∑ ab ∈ g,
          (s ∩ closedNatInterval ab).card := by
            simp [Finset.mul_sum]
  calc
    (f.biUnion closedNatInterval).card
        ≤ (g.biUnion tripleClosedNatInterval).card :=
      Finset.card_le_card hgCover
    _ ≤ ∑ ab ∈ g, (tripleClosedNatInterval ab).card :=
      Finset.card_biUnion_le
    _ ≤ (3 * K) * ∑ ab ∈ g, (s ∩ closedNatInterval ab).card := hsumTriple
    _ ≤ (3 * K) * s.card := Nat.mul_le_mul_left _ hsumInter
    _ = 3 * K * s.card := by omega

/-! ## Specialization to normalized bad intervals -/

/-- Endpoint pair of the four-length enlargement attached to a normalized
interval. -/
def normalizedBadIntervalExpansionEndpoints (NH : ℕ × ℕ) : ℕ × ℕ :=
  (NH.1 - 4 * NH.2, NH.1 + NH.2 + 4 * NH.2)

theorem closedNatInterval_normalizedBadIntervalExpansionEndpoints
    (N H : ℕ) :
    closedNatInterval (normalizedBadIntervalExpansionEndpoints (N, H)) =
      expandedConsecutiveInterval N H (4 * H) := by
  rfl

/-- The finite family of all relevant enlarged normalized intervals. -/
noncomputable def normalizedBadIntervalExpansionFamily (x : ℕ) :
    Finset (ℕ × ℕ) := by
  classical
  exact (scaleNormalizedBadIntervalIndices x).image
    normalizedBadIntervalExpansionEndpoints

theorem normalizedBadIntervalExpansionFamily_valid {x : ℕ} {ab : ℕ × ℕ}
    (hab : ab ∈ normalizedBadIntervalExpansionFamily x) :
    ab.1 ≤ ab.2 := by
  classical
  rw [normalizedBadIntervalExpansionFamily, Finset.mem_image] at hab
  obtain ⟨NH, _hNH, rfl⟩ := hab
  simp only [normalizedBadIntervalExpansionEndpoints]
  omega

/-- Every interval in the normalized expansion family has normalized-union
density at least `1/10`. -/
theorem normalizedBadIntervalExpansionFamily_density {x : ℕ} {ab : ℕ × ℕ}
    (hab : ab ∈ normalizedBadIntervalExpansionFamily x) :
    closedNatIntervalLength ab ≤
      10 * ((scaleNormalizedBadIntervalUnion x) ∩
        closedNatInterval ab).card := by
  classical
  rw [normalizedBadIntervalExpansionFamily, Finset.mem_image] at hab
  obtain ⟨NH, hNH, rfl⟩ := hab
  obtain ⟨_hN, _hH, p, k, m, hnorm, _hxLower, _hxUpper⟩ :=
    mem_scaleNormalizedBadIntervalIndices.mp hNH
  have hchildUnion :
      consecutiveInterval NH.1 NH.2 ⊆ scaleNormalizedBadIntervalUnion x :=
    consecutiveInterval_subset_scaleNormalizedBadIntervalUnion hNH
  have hchildExpanded :
      consecutiveInterval NH.1 NH.2 ⊆
        expandedConsecutiveInterval NH.1 NH.2 (4 * NH.2) :=
    consecutiveInterval_subset_expandedConsecutiveInterval
      NH.1 NH.2 (4 * NH.2)
  have hchildInter :
      consecutiveInterval NH.1 NH.2 ⊆
        (scaleNormalizedBadIntervalUnion x) ∩
          expandedConsecutiveInterval NH.1 NH.2 (4 * NH.2) := by
    intro j hj
    exact Finset.mem_inter.mpr ⟨hchildUnion hj, hchildExpanded hj⟩
  have hchildCard : (consecutiveInterval NH.1 NH.2).card = NH.2 := by
    simp [consecutiveInterval]
  have hinterLower : NH.2 ≤
      ((scaleNormalizedBadIntervalUnion x) ∩
        expandedConsecutiveInterval NH.1 NH.2 (4 * NH.2)).card := by
    calc
      NH.2 = (consecutiveInterval NH.1 NH.2).card := hchildCard.symm
      _ ≤ _ := Finset.card_le_card hchildInter
  have hexpandedUpper :
      (expandedConsecutiveInterval NH.1 NH.2 (4 * NH.2)).card ≤
        9 * NH.2 + 1 := by
    refine (card_expandedConsecutiveInterval_le
      NH.1 NH.2 (4 * NH.2)).trans ?_
    omega
  have hlengthEq :
      closedNatIntervalLength
          (normalizedBadIntervalExpansionEndpoints NH) =
        (expandedConsecutiveInterval NH.1 NH.2 (4 * NH.2)).card := by
    rw [← closedNatInterval_normalizedBadIntervalExpansionEndpoints]
    exact (card_closedNatInterval _).symm
  rw [hlengthEq, closedNatInterval_normalizedBadIntervalExpansionEndpoints]
  have hHpos : 1 ≤ NH.2 := by
    exact hnorm.1.trans' (by omega)
  omega

/-- The admissible union is covered by the finite family of enlarged
normalized intervals. -/
theorem admissibleBadIntervalUnion_subset_normalizedExpansionUnion
    (hSS : SylvesterSchurConclusion) (x : ℕ) :
    admissibleBadIntervalUnion x ⊆
      (normalizedBadIntervalExpansionFamily x).biUnion
        closedNatInterval := by
  classical
  intro n hn
  obtain ⟨N, H, hNH, hnExpanded, _hdensity⟩ :=
    exists_expanded_normalized_density_of_mem_admissibleBadIntervalUnion
      hSS hn
  apply Finset.mem_biUnion.mpr
  refine ⟨normalizedBadIntervalExpansionEndpoints (N, H), ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨(N, H), hNH, rfl⟩
  · rw [closedNatInterval_normalizedBadIntervalExpansionEndpoints]
    exact hnExpanded

/-- Completed finite maximal-function transfer after Lemma 6.2.  The union of
all admissible intervals has cardinality at most thirty times the union of the
corrected comparable-scale normalized intervals. -/
theorem card_admissibleBadIntervalUnion_le_thirty_mul_normalized
    (hSS : SylvesterSchurConclusion) (x : ℕ) :
    (admissibleBadIntervalUnion x).card ≤
      30 * (scaleNormalizedBadIntervalUnion x).card := by
  classical
  have hcover :=
    admissibleBadIntervalUnion_subset_normalizedExpansionUnion hSS x
  have hweak := card_biUnion_closedNatInterval_le_of_density
    (normalizedBadIntervalExpansionFamily x)
    (scaleNormalizedBadIntervalUnion x) 10
    (fun ab hab => normalizedBadIntervalExpansionFamily_valid hab)
    (fun ab hab => normalizedBadIntervalExpansionFamily_density hab)
  calc
    (admissibleBadIntervalUnion x).card
        ≤ ((normalizedBadIntervalExpansionFamily x).biUnion
            closedNatInterval).card := Finset.card_le_card hcover
    _ ≤ 3 * 10 * (scaleNormalizedBadIntervalUnion x).card := hweak
    _ = 30 * (scaleNormalizedBadIntervalUnion x).card := by omega

end Tao2026
