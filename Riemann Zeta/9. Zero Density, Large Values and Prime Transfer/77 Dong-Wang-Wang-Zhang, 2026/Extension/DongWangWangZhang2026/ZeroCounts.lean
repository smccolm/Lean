import DongWangWangZhang2026.XiConjugation

/-!
# Finite source zero counts with actual multiplicity

Counts use the full xi divisor index, whose fibers have exactly zeta's
analytic vanishing order. Finiteness is proved for every source disk and
window before any count estimate is used. The unbounded-set default of
Set.ncard is not used as evidence of finiteness.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex Complex.Hadamard Set
open RiemannZeta.GuthMaynard
open scoped Classical

/-- Count nontrivial zeros in a region using all analytic multiplicity labels. -/
def zeroCountIn (D : Set ℂ) : ℕ := {p : XiZero | xiZeroPoint p ∈ D}.ncard

/-- The source disk is open, including when its radius is nonpositive. -/
def sourceZeroDisk (φ r : ℝ) : Set ℂ :=
  {z | ‖z - (1 + (φ : ℂ) * I)‖ < r}

/-- The source local window is closed in both coordinates. -/
def sourceZeroWindow (u δ : ℝ) : Set ℂ :=
  {z | 1 - δ ≤ z.re ∧ |z.im - u| ≤ δ}

/-- Every bounded region has finitely many genuine multiplicity indices. -/
theorem finite_xiZero_mem_bounded {D : Set ℂ} (hD : Bornology.IsBounded D) :
    {p : XiZero | xiZeroPoint p ∈ D}.Finite := by
  obtain ⟨R, hR⟩ := hD.exists_norm_le
  exact (finite_xiZero_norm_le R).subset (fun p hp => hR _ hp)

/-- Every open source disk has a finite multiplicity count. -/
theorem finite_xiZero_sourceDisk (φ r : ℝ) :
    {p : XiZero | xiZeroPoint p ∈ sourceZeroDisk φ r}.Finite := by
  apply (finite_xiZero_norm_le (r + ‖1 + (φ : ℂ) * I‖)).subset
  intro p hp
  have hn := norm_le_norm_sub_add (xiZeroPoint p) (1 + (φ : ℂ) * I)
  change ‖xiZeroPoint p - (1 + (φ : ℂ) * I)‖ < r at hp
  change ‖xiZeroPoint p‖ ≤ _
  linarith

/-- Although the window extends rightward, its nontrivial zero indices form a finite set. -/
theorem finite_xiZero_sourceWindow (u δ : ℝ) :
    {p : XiZero | xiZeroPoint p ∈ sourceZeroWindow u δ}.Finite := by
  apply (finite_xiZero_norm_le (1 + |u| + δ)).subset
  intro p hp
  have hr := xiZeroPoint_re p
  have hn := norm_le_abs_re_add_abs_im (xiZeroPoint p)
  rw [abs_of_pos hr.1] at hn
  have hi' : |(xiZeroPoint p).im| ≤ |(xiZeroPoint p).im - u| + |u| := by
    simpa using abs_add_le ((xiZeroPoint p).im - u) u
  change 1 - δ ≤ (xiZeroPoint p).re ∧ |(xiZeroPoint p).im - u| ≤ δ at hp
  change ‖xiZeroPoint p‖ ≤ _
  linarith [hp.2]

/-- Monotonicity is used only with a proved finite enclosing index set. -/
theorem zeroCountIn_mono {D E : Set ℂ} (hDE : D ⊆ E)
    (hE : {p : XiZero | xiZeroPoint p ∈ E}.Finite) :
    zeroCountIn D ≤ zeroCountIn E :=
  Set.ncard_le_ncard (fun _ hp => hDE hp) hE

/-- Conjugation preserves the count by a permutation of all multiplicity labels. -/
theorem zeroCountIn_conj (D : Set ℂ) :
    zeroCountIn {z : ℂ | star z ∈ D} = zeroCountIn D := by
  apply Set.ncard_congr'
  exact xiZeroConjEquiv.subtypeEquiv (fun _ => Iff.rfl)

/-- Source disk counts have both height signs with exactly the same open boundary. -/
theorem zeroCountIn_sourceDisk_neg (φ r : ℝ) :
    zeroCountIn (sourceZeroDisk (-φ) r) = zeroCountIn (sourceZeroDisk φ r) := by
  have he : sourceZeroDisk (-φ) r =
      {z : ℂ | star z ∈ sourceZeroDisk φ r} := by
    ext z
    change (‖z - (1 + ((-φ : ℝ) : ℂ) * I)‖ < r) ↔
      (‖star z - (1 + (φ : ℂ) * I)‖ < r)
    have hn : ‖star z - (1 + (φ : ℂ) * I)‖ =
        ‖z - (1 + ((-φ : ℝ) : ℂ) * I)‖ := by
      rw [← norm_star (z - (1 + ((-φ : ℝ) : ℂ) * I))]
      simp
    rw [hn]
  rw [he, zeroCountIn_conj]

/-- Closed source windows are likewise invariant under height conjugation. -/
theorem zeroCountIn_sourceWindow_neg (u δ : ℝ) :
    zeroCountIn (sourceZeroWindow (-u) δ) = zeroCountIn (sourceZeroWindow u δ) := by
  have he : sourceZeroWindow (-u) δ =
      {z : ℂ | star z ∈ sourceZeroWindow u δ} := by
    ext z
    simp only [sourceZeroWindow, mem_setOf_eq, star_def, conj_re, conj_im]
    rw [show -z.im - u = -(z.im - -u) by ring, abs_neg]
  rw [he, zeroCountIn_conj]

/-- Cardinality of the actual divisor indices equals the sum of complete analytic fibers. -/
theorem zeroCountIn_eq_sum_multiplicities {D : Set ℂ}
    (hD : {p : XiZero | xiZeroPoint p ∈ D}.Finite) (S : Finset ℂ)
    (hcover : ∀ p : XiZero, xiZeroPoint p ∈ D ↔ xiZeroPoint p ∈ S)
    (hpos : ∀ z ∈ S, 0 < z.re) (hpole : ∀ z ∈ S, z ≠ 1) :
    zeroCountIn D = ∑ z ∈ S, analyticOrderNatAt riemannZeta z := by
  classical
  rw [zeroCountIn, Set.ncard_eq_toFinset_card _ hD,
    Finset.card_eq_sum_card_fiberwise (f := xiZeroPoint) (t := S) (by
      intro p hp
      exact (hcover p).mp (by simpa using hp))]
  apply Finset.sum_congr rfl
  intro z hz
  have he : {p ∈ hD.toFinset | xiZeroPoint p = z} =
      divisorZeroIndex₀_fiberFinset (f := riemannXi) z := by
    ext p
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, mem_setOf_eq,
      mem_divisorZeroIndex₀_fiberFinset]
    constructor
    · exact fun h => h.2
    · intro hp
      exact ⟨(hcover p).mpr (by simpa [hp] using hz), hp⟩
  rw [he, xi_zero_fiber_card (hpos z hz) (hpole z hz)]

/-- Exact bridge to the foundation's multiplicity-weighted rectangle count. -/
theorem zeroCountIn_rectangle_eq {σ₀ : ℝ} (hσ₀ : 0 < σ₀) (σ₁ t₀ t₁ : ℝ) :
    zeroCountIn (ZeroRectangle σ₀ σ₁ t₀ t₁) = zeroCountRect σ₀ σ₁ t₀ t₁ := by
  have hfin := finite_xiZero_mem_bounded
    (isCompact_ZeroRectangle σ₀ σ₁ t₀ t₁).isBounded
  apply zeroCountIn_eq_sum_multiplicities hfin (zerosInRect σ₀ σ₁ t₀ t₁)
  · intro p
    simp only [zerosInRect, Set.Finite.mem_toFinset, mem_inter_iff, mem_setOf_eq,
      xiZeroPoint_zeta_zero, and_true]
  · intro z hz
    have hz' := (Set.Finite.mem_toFinset _).mp hz
    exact hσ₀.trans_le hz'.1.1
  · intro z hz
    have hz' := (Set.Finite.mem_toFinset _).mp hz
    intro he
    exact riemannZeta_one_ne_zero (by simpa [he] using hz'.2)

/-- A finite enclosing rectangle computes any subregion by filtering its true zeros. -/
theorem zeroCountIn_eq_rectangle_filter {D : Set ℂ} {σ₀ : ℝ} (hσ₀ : 0 < σ₀)
    (σ₁ t₀ t₁ : ℝ) (hD : D ⊆ ZeroRectangle σ₀ σ₁ t₀ t₁) :
    zeroCountIn D = ∑ z ∈ (zerosInRect σ₀ σ₁ t₀ t₁).filter (· ∈ D),
      analyticOrderNatAt riemannZeta z := by
  classical
  have hfin := (finite_xiZero_mem_bounded
    (isCompact_ZeroRectangle σ₀ σ₁ t₀ t₁).isBounded).subset
      (fun p hp => hD hp)
  apply zeroCountIn_eq_sum_multiplicities hfin
  · intro p
    simp only [Finset.mem_filter, zerosInRect, Set.Finite.mem_toFinset,
      mem_inter_iff, mem_setOf_eq, xiZeroPoint_zeta_zero, and_true]
    exact ⟨fun hp => ⟨hD hp, hp⟩, fun hp => hp.2⟩
  · intro z hz
    have hz' := (Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hz).1
    exact hσ₀.trans_le hz'.1.1
  · intro z hz
    have hz' := (Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hz).1
    intro he
    exact riemannZeta_one_ne_zero (by simpa [he] using hz'.2)

/-- Two valid enclosing rectangles give the same multiplicity-weighted regional count. -/
theorem rectangle_filter_count_independent {D : Set ℂ}
    {a₀ b₀ : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀)
    (a₁ u₀ u₁ b₁ v₀ v₁ : ℝ)
    (ha : D ⊆ ZeroRectangle a₀ a₁ u₀ u₁)
    (hb : D ⊆ ZeroRectangle b₀ b₁ v₀ v₁) :
    (∑ z ∈ (zerosInRect a₀ a₁ u₀ u₁).filter (· ∈ D),
      analyticOrderNatAt riemannZeta z) =
    ∑ z ∈ (zerosInRect b₀ b₁ v₀ v₁).filter (· ∈ D),
      analyticOrderNatAt riemannZeta z := by
  classical
  rw [← zeroCountIn_eq_rectangle_filter ha₀ a₁ u₀ u₁ ha,
    ← zeroCountIn_eq_rectangle_filter hb₀ b₁ v₀ v₁ hb]

/-- The actual closed window count equals the foundation rectangle count, not a set count. -/
theorem zeroCountIn_sourceWindow_eq {δ : ℝ} (hδ : δ < 1) (u : ℝ) :
    zeroCountIn (sourceZeroWindow u δ) = zeroCountRect (1 - δ) 1 (u - δ) (u + δ) := by
  rw [← zeroCountIn_rectangle_eq (by linarith : 0 < 1 - δ)]
  unfold zeroCountIn
  congr 1
  ext p
  change (1 - δ ≤ (xiZeroPoint p).re ∧ |(xiZeroPoint p).im - u| ≤ δ) ↔
    1 - δ ≤ (xiZeroPoint p).re ∧ (xiZeroPoint p).re ≤ 1 ∧
      u - δ ≤ (xiZeroPoint p).im ∧ (xiZeroPoint p).im ≤ u + δ
  have hr := (xiZeroPoint_re p).2.le
  rw [abs_le]
  constructor <;> intro h
  · exact ⟨h.1, hr, by linarith [h.2.1], by linarith [h.2.2]⟩
  · exact ⟨h.1, by linarith [h.2.2.1], by linarith [h.2.2.2]⟩

/-- An open disk is contained in the source closed window at any larger radius. -/
theorem sourceZeroDisk_subset_window (u : ℝ) {r δ : ℝ} (hr : r ≤ δ) :
    sourceZeroDisk u r ⊆ sourceZeroWindow u δ := by
  intro z hz
  change ‖z - (1 + (u : ℂ) * I)‖ < r at hz
  have hre := abs_re_le_norm (z - (1 + (u : ℂ) * I))
  have him := abs_im_le_norm (z - (1 + (u : ℂ) * I))
  simp only [sub_re, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, sub_zero, add_zero, zero_add, sub_im, add_im, one_im,
    mul_im, mul_one] at hre him
  exact ⟨by have hh := (abs_le.mp (hre.trans hz.le)).1; linarith,
    him.trans (hz.le.trans hr)⟩

/-- Disk-to-window transfer keeps the exact multiplicities and strict disk boundary. -/
theorem zeroCountIn_disk_le_window (u : ℝ) {r δ : ℝ} (hr : r ≤ δ) :
    zeroCountIn (sourceZeroDisk u r) ≤ zeroCountIn (sourceZeroWindow u δ) :=
  zeroCountIn_mono (sourceZeroDisk_subset_window u hr) (finite_xiZero_sourceWindow u δ)

/-- A nonpositive-radius open disk contains no zeros, including at its center. -/
theorem zeroCountIn_sourceDisk_nonpos (φ : ℝ) {r : ℝ} (hr : r ≤ 0) :
    zeroCountIn (sourceZeroDisk φ r) = 0 := by
  have he : sourceZeroDisk φ r = ∅ := by
    ext z
    simp only [sourceZeroDisk, mem_setOf_eq, mem_empty_iff_false, iff_false]
    exact not_lt.mpr (hr.trans (norm_nonneg _))
  simp [zeroCountIn, he]

end
end DongWangWangZhang2026
