import Dubon2026.SourceManinCuspSpace

/-! DUB-17/18 -> parabolic Hecke realization -> matching period dimensions
-> exact arithmetic genus bound -> count of original rational cusp orbits.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_CuspSpace.lean and
P2M/Sol/S_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime.lean.
The quotient and its level action are the previously proved SourceManin
objects. Cusp widths and unrelated geometric infrastructure are omitted.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup
open scoped MatrixGroups

/-- The actual rational cusp represented by an integral numerator and denominator. -/
def ratPoint (a c : ℤ) : OnePoint ℚ :=
  if c = 0 then ∞ else (((a : ℚ) / (c : ℚ) : ℚ) : OnePoint ℚ)

@[simp] lemma ratPoint_zero_right (a : ℤ) : ratPoint a 0 = ∞ := if_pos rfl

lemma ratPoint_of_ne_zero (a : ℤ) {c : ℤ} (hc : c ≠ 0) :
    ratPoint a c = (((a : ℚ) / (c : ℚ) : ℚ) : OnePoint ℚ) := if_neg hc

@[simp] lemma ratPoint_zero_one : ratPoint 0 1 = ((0 : ℚ) : OnePoint ℚ) := by
  simp [ratPoint]

lemma ratPoint_eq_infty_iff {a c : ℤ} : ratPoint a c = ∞ ↔ c = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · simp [ratPoint_of_ne_zero a hc, hc]

lemma ratPoint_mul_left {l : ℤ} (hl : l ≠ 0) (a c : ℤ) :
    ratPoint (l * a) (l * c) = ratPoint a c := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [ratPoint_of_ne_zero _ (mul_ne_zero hl hc), ratPoint_of_ne_zero _ hc]
    push_cast
    rw [mul_div_mul_left _ _ (by exact_mod_cast hl)]

lemma ratPoint_neg_neg (a c : ℤ) : ratPoint (-a) (-c) = ratPoint a c := by
  simpa using ratPoint_mul_left (l := -1) (by norm_num) a c

lemma exists_ratPoint_eq (x : OnePoint ℚ) : ∃ a c : ℤ, IsCoprime a c ∧ ratPoint a c = x := by
  cases x with
  | infty => exact ⟨1, 0, isCoprime_one_left, rfl⟩
  | coe q =>
    refine ⟨q.num, (q.den : ℤ), ?_, ?_⟩
    · rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using q.reduced
    · rw [ratPoint_of_ne_zero _ (by exact_mod_cast q.den_nz), OnePoint.coe_eq_coe,
        show ((q.den : ℤ) : ℚ) = (q.den : ℚ) by push_cast; ring, Rat.num_div_den]

@[simp] lemma mapGL_apply_coe (γ : SL(2, ℤ)) (i j : Fin 2) :
    (mapGL ℚ γ) i j = ((γ i j : ℤ) : ℚ) := by
  simp [mapGL]

lemma mapGL_smul_infty (γ : SL(2, ℤ)) :
    mapGL ℚ γ • (∞ : OnePoint ℚ) = ratPoint (γ 0 0) (γ 1 0) := by
  rw [smul_infty_eq_ite, mapGL_apply_coe, mapGL_apply_coe]
  rcases eq_or_ne (γ 1 0) 0 with h | h
  · simp [h]
  · rw [if_neg (by exact_mod_cast h), ratPoint_of_ne_zero _ h]

lemma mapGL_smul_ratPoint (γ : SL(2, ℤ)) {a c : ℤ} (h : a ≠ 0 ∨ c ≠ 0) :
    mapGL ℚ γ • ratPoint a c =
      ratPoint (γ 0 0 * a + γ 0 1 * c) (γ 1 0 * a + γ 1 1 * c) := by
  rcases eq_or_ne c 0 with rfl | hc
  ·
    replace h : a ≠ 0 := h.resolve_right (by simp)
    rw [ratPoint_zero_right, mapGL_smul_infty]
    simp only [mul_zero, add_zero]
    rw [mul_comm (γ 0 0) a, mul_comm (γ 1 0) a, ratPoint_mul_left h]
  ·
    rw [ratPoint_of_ne_zero _ hc, smul_some_eq_ite]
    have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast hc
    have hden : (mapGL ℚ γ) 1 0 * ((a : ℚ) / c) + (mapGL ℚ γ) 1 1
        = (((γ 1 0 * a + γ 1 1 * c : ℤ) : ℚ)) / (c : ℚ) := by
      simp only [mapGL_apply_coe]
      field_simp
      push_cast
      ring
    have hnum : (mapGL ℚ γ) 0 0 * ((a : ℚ) / c) + (mapGL ℚ γ) 0 1
        = (((γ 0 0 * a + γ 0 1 * c : ℤ) : ℚ)) / (c : ℚ) := by
      simp only [mapGL_apply_coe]
      field_simp
      push_cast
      ring
    rcases eq_or_ne (γ 1 0 * a + γ 1 1 * c) 0 with h0 | h0
    · rw [if_pos (by rw [hden, h0]; simp), h0, ratPoint_zero_right]
    · rw [if_neg (by rw [hden]; exact div_ne_zero (by exact_mod_cast h0) hcQ),
        ratPoint_of_ne_zero _ h0, hnum, hden, OnePoint.coe_eq_coe,
        div_div_div_cancel_right₀ hcQ]

lemma isCoprime_smul_pair (γ : SL(2, ℤ)) {a c : ℤ} (h : IsCoprime a c) :
    IsCoprime (γ 0 0 * a + γ 0 1 * c) (γ 1 0 * a + γ 1 1 * c) := by
  have := IsCoprime.mulVecSL (v := ![a, c]) (by simpa using h) γ
  simpa [Matrix.mulVec_fin_two] using this


theorem ratPoint_eq_ratPoint_iff_of_isCoprime {a c a' c' : ℤ} (h : IsCoprime a c)
    (h' : IsCoprime a' c') :
    Dubon2026.SourceManin.ratPoint a c = Dubon2026.SourceManin.ratPoint a' c' ↔ (a = a' ∧ c = c') ∨ (a = -a' ∧ c = -c') := by
  constructor
  · intro heq
    rcases eq_or_ne c 0 with rfl | hc
    ·
      have hc' : c' = 0 := by
        rw [ratPoint_zero_right] at heq
        exact ratPoint_eq_infty_iff.mp heq.symm
      subst hc'
      have hu : IsUnit a := isCoprime_zero_right.mp h
      have hu' : IsUnit a' := isCoprime_zero_right.mp h'
      rcases Int.isUnit_iff.mp hu with rfl | rfl <;>
          rcases Int.isUnit_iff.mp hu' with rfl | rfl <;>
        norm_num
    ·
      have hc' : c' ≠ 0 := by
        intro h0
        rw [h0, ratPoint_zero_right, ratPoint_eq_infty_iff] at heq
        exact hc heq
      have hcQ : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
      have hcQ' : (c' : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc'
      rw [ratPoint_of_ne_zero _ hc, ratPoint_of_ne_zero _ hc', OnePoint.coe_eq_coe,
        div_eq_div_iff hcQ hcQ'] at heq
      have hZ : a * c' = a' * c := by exact_mod_cast heq

      have h1 : c ∣ c' := h.symm.dvd_of_dvd_mul_left ⟨a', by linear_combination hZ⟩
      have h2 : c' ∣ c := h'.symm.dvd_of_dvd_mul_left ⟨a, by linear_combination - hZ⟩
      obtain ⟨u, hu⟩ := h1
      obtain ⟨v, hv⟩ := h2
      have huv : u * v = 1 := by
        have h3 : c * (u * v) = c * 1 := by
          rw [mul_one, ← mul_assoc, ← hu, ← hv]
        exact mul_left_cancel₀ hc h3
      rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one v huv) with hu1 | hu1
      ·
        rw [hu1, mul_one] at hu
        rw [hu] at hZ
        exact Or.inl ⟨mul_right_cancel₀ hc hZ, hu.symm⟩
      ·
        rw [hu1, mul_neg_one] at hu
        have hc2 : c = -c' := by rw [hu]; ring
        have h4 : a * c' = -a' * c' := by
          rw [hc2] at hZ
          linear_combination hZ
        exact Or.inr ⟨mul_right_cancel₀ hc' h4, hc2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact ratPoint_neg_neg a' c'

end
end Dubon2026.SourceManin
