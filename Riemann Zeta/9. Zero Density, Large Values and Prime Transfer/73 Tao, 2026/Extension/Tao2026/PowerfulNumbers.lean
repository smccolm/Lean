import Tao2026.Counting

/-!
# One-term powerful numbers

This file turns the square-times-squarefree-cube decomposition into the exact
finite parametrization of `VB¹`. It is the arithmetic starting point for the
`ζ(3/2) / ζ(3)` asymptotic in Tao's Theorem 1.8.
-/

namespace Tao2026

/-- A one-term very bad number is exactly a positive powerful number. -/
theorem mem_veryBadOneTermSet_iff {n : ℕ} :
    n ∈ veryBadOneTermSet ↔ 1 ≤ n ∧ Powerful n := by
  constructor
  · rintro ⟨hn, hveryBad⟩
    have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rcases hveryBad with ⟨_, hpowerful⟩
    rw [consecutiveProduct_one, hpred] at hpowerful
    exact ⟨hn, hpowerful⟩
  · rintro ⟨hn, hpowerful⟩
    refine ⟨hn, ?_⟩
    have hpred : n - 1 + 1 = n := Nat.sub_add_cancel hn
    exact ⟨by simp, by simpa [consecutiveProduct_one, hpred] using hpowerful⟩

/-- Source-facing membership in `VB¹` via the unique positive
square-times-squarefree-cube representation. -/
theorem mem_veryBadOneTermSet_iff_exists_sq_mul_cube_squarefree {n : ℕ} :
    n ∈ veryBadOneTermSet ↔
      ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Squarefree b ∧ n = a ^ 2 * b ^ 3 := by
  constructor
  · intro hn
    have hn' := mem_veryBadOneTermSet_iff.mp hn
    exact (powerful_iff_exists_sq_mul_cube_squarefree hn'.1).mp hn'.2
  · intro hrep
    rcases hrep with ⟨a, b, ha, hb, hbSquarefree, rfl⟩
    rw [mem_veryBadOneTermSet_iff]
    refine ⟨Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero 2 ha.ne') (pow_ne_zero 3 hb.ne')), ?_⟩
    exact (powerful_iff_exists_sq_mul_cube_squarefree
      (mul_pos (pow_pos ha 2) (pow_pos hb 3))).mpr
        ⟨a, b, ha, hb, hbSquarefree, rfl⟩

/-- The finite square-times-squarefree-cube parameter space below `x`.
The first sigma coordinate is the squarefree cube base `b`; the second is the
square base `a`. -/
noncomputable def powerfulOneTermRepresentations (x : ℕ) :
    Finset (Σ _b : ℕ, ℕ) := by
  classical
  exact ((Finset.Icc 1 x).filter Squarefree).sigma fun b =>
    Finset.Icc 1 (x / b ^ 3).sqrt

/-- The powerful natural represented by `(b,a)`. -/
def powerfulOneTermRepresentationValue (r : Σ _b : ℕ, ℕ) : ℕ :=
  r.2 ^ 2 * r.1 ^ 3

/-- The literal finite intersection `VB¹ ∩ [1,x]`. -/
noncomputable def veryBadOneTermNumbersUpTo (x : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 x).filter fun n => n ∈ veryBadOneTermSet

theorem mem_powerfulOneTermRepresentations_iff {x : ℕ}
    {r : Σ _b : ℕ, ℕ} :
    r ∈ powerfulOneTermRepresentations x ↔
      1 ≤ r.1 ∧ r.1 ≤ x ∧ Squarefree r.1 ∧
        1 ≤ r.2 ∧ r.2 ≤ (x / r.1 ^ 3).sqrt := by
  classical
  simp [powerfulOneTermRepresentations, and_left_comm, and_assoc]

/-- Forgetting the unique `(a,b)` representation gives exactly
`VB¹ ∩ [1,x]`. -/
theorem image_powerfulOneTermRepresentations (x : ℕ) :
    (powerfulOneTermRepresentations x).image
        powerfulOneTermRepresentationValue =
      veryBadOneTermNumbersUpTo x := by
  classical
  ext n
  rw [veryBadOneTermNumbersUpTo]
  constructor
  · intro hn
    rw [Finset.mem_image] at hn
    rcases hn with ⟨r, hr, rfl⟩
    have hr' := mem_powerfulOneTermRepresentations_iff.mp hr
    have hbpos : 0 < r.1 := hr'.1
    have hapos : 0 < r.2 := hr'.2.2.2.1
    have hsqLeDiv : r.2 ^ 2 ≤ x / r.1 ^ 3 :=
      Nat.le_sqrt'.mp hr'.2.2.2.2
    have hle : r.2 ^ 2 * r.1 ^ 3 ≤ x :=
      (Nat.le_div_iff_mul_le (pow_pos hbpos 3)).mp hsqLeDiv
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero 2 hapos.ne') (pow_ne_zero 3 hbpos.ne')), hle⟩,
      mem_veryBadOneTermSet_iff_exists_sq_mul_cube_squarefree.mpr
        ⟨r.2, r.1, hapos, hbpos, hr'.2.2.1, rfl⟩⟩
  · intro hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases hn with ⟨⟨_, hnle⟩, hveryBad⟩
    rcases mem_veryBadOneTermSet_iff_exists_sq_mul_cube_squarefree.mp hveryBad with
      ⟨a, b, ha, hb, hbSquarefree, hnrep⟩
    have hbLeCube : b ≤ b ^ 3 := by
      calc
        b ≤ b * b := Nat.le_mul_of_pos_right b hb
        _ ≤ (b * b) * b := Nat.le_mul_of_pos_right (b * b) hb
        _ = b ^ 3 := by ring
    have hbCubeLeN : b ^ 3 ≤ n := by
      rw [hnrep]
      exact Nat.le_mul_of_pos_left (b ^ 3) (pow_pos ha 2)
    have hbLeX : b ≤ x := hbLeCube.trans (hbCubeLeN.trans hnle)
    have haSqLeDiv : a ^ 2 ≤ x / b ^ 3 := by
      rw [Nat.le_div_iff_mul_le (pow_pos hb 3)]
      exact hnrep ▸ hnle
    have haLeSqrt : a ≤ (x / b ^ 3).sqrt := Nat.le_sqrt'.mpr haSqLeDiv
    rw [Finset.mem_image]
    refine ⟨⟨b, a⟩, ?_, hnrep.symm⟩
    exact mem_powerfulOneTermRepresentations_iff.mpr
      ⟨hb, hbLeX, hbSquarefree, ha, haLeSqrt⟩

/-- The representation map is injective because the squarefree cube base and
the square base are both unique. -/
theorem injOn_powerfulOneTermRepresentationValue (x : ℕ) :
    Set.InjOn powerfulOneTermRepresentationValue
      (powerfulOneTermRepresentations x) := by
  rintro ⟨b, a⟩ hba ⟨d, c⟩ hdc heq
  have hba' := mem_powerfulOneTermRepresentations_iff.mp hba
  have hdc' := mem_powerfulOneTermRepresentations_iff.mp hdc
  have hunique := sq_mul_cube_squarefree_unique
    (mul_pos (pow_pos hba'.2.2.2.1 2) (pow_pos hba'.1 3))
    hba'.1 hba'.2.2.1 hdc'.2.2.1 rfl heq
  rcases hunique with ⟨hac, hbd⟩
  change a = c at hac
  change b = d at hbd
  subst c
  subst d
  rfl

/-- Cardinality of the square-times-squarefree-cube parameter family. -/
theorem card_powerfulOneTermRepresentations (x : ℕ) :
    (powerfulOneTermRepresentations x).card =
      ∑ b ∈ (Finset.Icc 1 x).filter Squarefree, (x / b ^ 3).sqrt := by
  classical
  rw [powerfulOneTermRepresentations, Finset.card_sigma]
  simp

/-- Exact finite starting identity for the one-term very-bad count:
`#(VB¹∩[1,x]) = ∑_{b≤x, squarefree} ⌊√(x/b³)⌋`. -/
theorem veryBadOneTermCount_eq_sum_sqrt_div_cube (x : ℕ) :
    veryBadOneTermCount x =
      ∑ b ∈ (Finset.Icc 1 x).filter Squarefree, (x / b ^ 3).sqrt := by
  classical
  change (veryBadOneTermNumbersUpTo x).card = _
  rw [← image_powerfulOneTermRepresentations x,
    Finset.card_image_iff.mpr (injOn_powerfulOneTermRepresentationValue x),
    card_powerfulOneTermRepresentations]

/-- The `b=1` term in the squarefree-cube parameterization is the full family
of positive squares, giving the sharp elementary lower bound. -/
theorem sqrt_le_veryBadOneTermCount (x : ℕ) :
    Nat.sqrt x ≤ veryBadOneTermCount x := by
  rw [veryBadOneTermCount_eq_sum_sqrt_div_cube]
  by_cases hx : x = 0
  · subst x
    simp
  · have hxOne : 1 ≤ x := Nat.one_le_iff_ne_zero.mpr hx
    have hmem : 1 ∈ (Finset.Icc 1 x).filter Squarefree := by
      simp [hxOne]
    calc
      Nat.sqrt x = (x / 1 ^ 3).sqrt := by norm_num
      _ ≤ ∑ b ∈ (Finset.Icc 1 x).filter Squarefree,
          (x / b ^ 3).sqrt :=
        Finset.single_le_sum
          (s := (Finset.Icc 1 x).filter Squarefree)
          (f := fun b => (x / b ^ 3).sqrt)
          (fun _ _ => Nat.zero_le _) hmem

/-- The positive-square family transfers from `VB¹` to all very-bad values. -/
theorem sqrt_le_veryBadCount (x : ℕ) : Nat.sqrt x ≤ veryBadCount x :=
  le_trans (sqrt_le_veryBadOneTermCount x)
    (countUpTo_mono veryBadOneTermSet_subset_veryBadSet x)

end Tao2026
