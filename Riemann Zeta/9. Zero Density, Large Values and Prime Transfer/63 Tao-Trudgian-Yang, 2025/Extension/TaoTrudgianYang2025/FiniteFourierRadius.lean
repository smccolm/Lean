import TaoTrudgianYang2025.FiniteFourierExtraction

/-!
# Arbitrary-order finite Fourier radius

This radius pays for the full complementary Fourier integral of an
actual finite phase sum. The profile, scale factor and index cardinality
remain explicit; the elementary subpower bound is separate from the
later physical source-growth estimate.
-/

noncomputable section
open scoped BigOperators FourierTransform
open MeasureTheory Complex
namespace TaoTrudgianYang2025
open RiemannZeta.GuthMaynard

noncomputable def finiteFourierRadius
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (k : ℕ) (c V : ℝ) : ℝ :=
  (1 +
    4 * (c * (S).card) *
      SchwartzMap.seminorm ℝ k 0
        (𝓕 (f)) /
      (((k : ℝ) - 1) * V)) ^ (1 / ((k : ℝ) - 1))

theorem finiteFourierRadius_pos
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (k : ℕ) (c V : ℝ) (hc : 0 ≤ c) (hV : 0 < V) (hk : 1 < k) :
    0 < finiteFourierRadius f S k c V := by
  unfold finiteFourierRadius
  have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
  have hq : 0 < (k : ℝ) - 1 := by linarith
  have hterm : 0 ≤
      4 * (c * (S).card) *
        SchwartzMap.seminorm ℝ k 0
          (𝓕 (f)) /
        (((k : ℝ) - 1) * V) := by positivity
  exact Real.rpow_pos_of_pos (by linarith) _

/-- By construction, the canonical arbitrary-order radius makes the complete
sharp Type-I Fourier tail at most half the threshold. -/
theorem finiteFourierRadius_tail_numeric
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (k : ℕ) (c V : ℝ) (hc : 0 ≤ c) (hV : 0 < V) (hk : 1 < k) :
    let R := finiteFourierRadius f S k c V
    c * (S).card *
        ((2 * SchwartzMap.seminorm ℝ k 0
            (𝓕 (f)) / ((k : ℝ) - 1)) *
          R ^ (1 - (k : ℝ))) ≤ V / 2 := by
  dsimp only
  let q : ℝ := (k : ℝ) - 1
  let M : ℝ := c *
    (S).card
  let C : ℝ := SchwartzMap.seminorm ℝ k 0
    (𝓕 (f))
  let B : ℝ := 1 + 4 * M * C / (q * V)
  let R : ℝ := B ^ (1 / q)
  have hq : 0 < q := by
    dsimp only [q]
    have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    have : 0 ≤ 4 * M * C / (q * V) := by positivity
    linarith
  have hR : 0 < R := Real.rpow_pos_of_pos hB _
  have hRq : R ^ q = B := by
    dsimp only [R]
    rw [← Real.rpow_mul hB.le]
    have hqne : q ≠ 0 := hq.ne'
    rw [show (1 / q) * q = 1 by field_simp]
    exact Real.rpow_one B
  have hcore : 4 * M * C / (q * V) ≤ B := by
    dsimp only [B]
    linarith
  have hmul : 4 * M * C ≤ B * (q * V) := by
    rw [div_le_iff₀ (mul_pos hq hV)] at hcore
    nlinarith
  have hRadius : finiteFourierRadius f S k c V = R := by rfl
  rw [hRadius]
  change M * ((2 * C / q) * R ^ (1 - (k : ℝ))) ≤ V / 2
  have hexponent : 1 - (k : ℝ) = -q := by
    dsimp only [q]
    ring
  rw [hexponent]
  rw [Real.rpow_neg hR.le, hRq]
  have hrearrange : M * (2 * C / q * B⁻¹) = 2 * M * C / (q * B) := by
    field_simp
  rw [hrearrange, div_le_iff₀ (mul_pos hq hB)]
  nlinarith

/-- Abstract subpower engine for the canonical radius.  Once its defining
base has growth `T^α`, choosing the Fourier order so that
`α ≤ δ (k - 1)` places the complete radius below `T^δ`. -/
theorem finiteFourierRadius_le_rpow_of_base_growth
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (k : ℕ) (c V T α δ : ℝ) (hc : 0 ≤ c) (hV : 0 < V) (hk : 1 < k)
    (hT : 1 ≤ T) (horder : α ≤ δ * ((k : ℝ) - 1))
    (hbase :
      1 +
          4 * (c * (S).card) *
            SchwartzMap.seminorm ℝ k 0
              (𝓕 (f)) /
            (((k : ℝ) - 1) * V) ≤
        T ^ α) :
    finiteFourierRadius f S k c V ≤ T ^ δ := by
  let q : ℝ := (k : ℝ) - 1
  have hq : 0 < q := by
    dsimp only [q]
    have hkReal : (1 : ℝ) < k := by exact_mod_cast hk
    linarith
  let B : ℝ :=
    1 +
      4 * (c * (S).card) *
        SchwartzMap.seminorm ℝ k 0
          (𝓕 (f)) /
        (((k : ℝ) - 1) * V)
  have hBnonneg : 0 ≤ B := by
    dsimp only [B]
    have hq' : 0 < (k : ℝ) - 1 := by simpa only [q] using hq
    have hterm : 0 ≤
        4 * (c * (S).card) *
          SchwartzMap.seminorm ℝ k 0
            (𝓕 (f)) /
          (((k : ℝ) - 1) * V) := by positivity
    linarith
  have hbase' : B ≤ T ^ α := by simpa only [B] using hbase
  have hexponent : α * (1 / q) ≤ δ := by
    have horder' : α ≤ δ * q := by simpa only [q] using horder
    have hdiv : α / q ≤ δ := (div_le_iff₀ hq).2 (by nlinarith)
    simpa only [div_eq_mul_inv, one_mul] using hdiv
  change B ^ (1 / q) ≤ T ^ δ
  calc
    B ^ (1 / q) ≤ (T ^ α) ^ (1 / q) :=
      Real.rpow_le_rpow hBnonneg hbase' (by positivity)
    _ = T ^ (α * (1 / q)) := by
      rw [← Real.rpow_mul (by linarith : 0 ≤ T)]
    _ ≤ T ^ δ := Real.rpow_le_rpow_of_exponent_le hT hexponent


theorem exists_explicitly_bounded_coefficientOne_shift_of_schwartz_logShift
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (k : ℕ) (c a V t : ℝ)
    (hS : ∀ n ∈ S, 0 < n) (hc : 0 < c) (hV : 0 < V) (hk : 1 < k)
    (hlarge : V ≤ ‖(c : ℂ) * ∑ n ∈ S,
      f (Real.log n-a) * (n : ℂ)^(-(t : ℂ)*I)‖) :
    let R := finiteFourierRadius f S k c V
    ∃ ξ ∈ Set.Icc (-R) R,
      V/(4*c*finiteFourierMass f) ≤
        ‖∑ n ∈ S, (n : ℂ)^(-(((t-2*Real.pi*ξ : ℝ) : ℂ))*I)‖ := by
  dsimp only
  apply exists_bounded_coefficientOne_shift_of_schwartz_logShift
    f S k c a V t (finiteFourierRadius f S k c V) hS hc hV hk
    (finiteFourierRadius_pos f S k c V hc.le hV hk) hlarge
  exact finiteFourierRadius_tail_numeric f S k c V hc.le hV hk

end TaoTrudgianYang2025
