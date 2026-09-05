import GafniTao.HeathBrownEPHalfAlgebra
import GafniTao.Pintz2023CorollaryOneAlgebra

/-!
# Power form of the native logarithmic derivative estimate

This file evaluates the already proved Heath--Brown k-th derivative bound
at the physical scale `t = N^tau`.  It retains all three source terms and
their order-dependent constants, then supplies a generic consumer which
may compare the three exponents with one target exponent.
-/

namespace GafniTao

noncomputable section

def heathBrownLogFirstExponent
    (k : ℕ) (epsilon tau : ℝ) : ℝ :=
  1 + epsilon + (tau - k) /
    ((k : ℝ) * ((k : ℝ) - 1))

def heathBrownLogSecondExponent
    (k : ℕ) (epsilon : ℝ) : ℝ :=
  1 + epsilon - 1 /
    ((k : ℝ) * ((k : ℝ) - 1))

def heathBrownLogThirdExponent
    (k : ℕ) (epsilon tau : ℝ) : ℝ :=
  1 + epsilon - 2 * tau /
    ((k : ℝ) ^ 2 * ((k : ℝ) - 1))

/-- Exact three-power expansion after putting the height at `N^tau`. -/
theorem pintz2023_scaled_derivative_factor_at_rpow
    {k N : ℕ} {epsilon tau : ℝ}
    (hk : 3 ≤ k) (hN : 0 < N) :
    (N : ℝ) ^ (1 + epsilon) *
        heathBrownKthDerivativeFactor k N
          (pintz2023DerivativeLambda k N ((N : ℝ) ^ tau)) =
      (pintz2023DerivativeConstant k) ^ pintz2023HBAlpha k *
          (N : ℝ) ^ (heathBrownLogFirstExponent k epsilon tau) +
        (N : ℝ) ^ (heathBrownLogSecondExponent k epsilon) +
        (pintz2023DerivativeConstant k) ^ (-pintz2023HBGamma k) *
          (N : ℝ) ^ (heathBrownLogThirdExponent k epsilon tau) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hbase := pintz2023_scaled_derivative_factor_eq
    (r := k) (N := N) (t := (N : ℝ) ^ tau)
      (xi := 1) (epsilon := epsilon) hk hN
      (Real.rpow_pos_of_pos hNReal tau)
  rw [hbase]
  have hfirst :
      (N : ℝ) ^
          (1 - 1 / ((k : ℝ) - 1) + epsilon) *
          ((N : ℝ) ^ tau) ^ pintz2023HBAlpha k =
        (N : ℝ) ^ (heathBrownLogFirstExponent k epsilon tau) := by
    rw [← Real.rpow_mul hNReal.le, ← Real.rpow_add hNReal]
    unfold heathBrownLogFirstExponent pintz2023HBAlpha
    have hkReal : (3 : ℝ) ≤ k := by exact_mod_cast hk
    field_simp
    ring_nf
  have hthird :
      (N : ℝ) ^ (1 + epsilon) *
          ((N : ℝ) ^ tau) ^ (-pintz2023HBGamma k) =
        (N : ℝ) ^ (heathBrownLogThirdExponent k epsilon tau) := by
    rw [← Real.rpow_mul hNReal.le, ← Real.rpow_add hNReal]
    unfold heathBrownLogThirdExponent pintz2023HBGamma
    ring_nf
  have hsecond :
      1 + epsilon - pintz2023HBAlpha k =
        heathBrownLogSecondExponent k epsilon := by
    unfold heathBrownLogSecondExponent pintz2023HBAlpha
    rfl
  rw [mul_assoc, hfirst, mul_assoc, hthird, hsecond]

/-- Fixed-order logarithmic block estimate, with the exact three exponents
visible and one constant uniform in `N`, the terminal endpoint, and `tau`.
-/
theorem norm_pintz2023ExponentialBlock_le_log_powers
    (k : ℕ) (epsilon : ℝ) (hk : 3 ≤ k) (hepsilon : 0 < epsilon) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C *
          ((pintz2023DerivativeConstant k) ^ pintz2023HBAlpha k *
              (N : ℝ) ^ (heathBrownLogFirstExponent k epsilon tau) +
            (N : ℝ) ^ (heathBrownLogSecondExponent k epsilon) +
            (pintz2023DerivativeConstant k) ^ (-pintz2023HBGamma k) *
              (N : ℝ) ^ (heathBrownLogThirdExponent k epsilon tau)) := by
  obtain ⟨C, hC, hbound⟩ :=
    norm_pintz2023ExponentialBlock_prefix_le k epsilon hk hepsilon
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR
  have ht : 0 < (N : ℝ) ^ tau := by positivity
  have hraw := hbound N R ((N : ℝ) ^ tau) hN hNR hR ht
  rw [mul_assoc,
    pintz2023_scaled_derivative_factor_at_rpow hk hN] at hraw
  exact hraw

/-- If all three displayed exponents are below `target`, the whole native
derivative estimate is bounded by one power of `N`. -/
theorem norm_pintz2023ExponentialBlock_le_target_of_exponents
    (k : ℕ) (epsilon : ℝ) (hk : 3 ≤ k) (hepsilon : 0 < epsilon)
    (range : ℝ → Prop)
    (target : ℝ → ℝ)
    (hfirst : ∀ tau : ℝ, range tau →
      heathBrownLogFirstExponent k epsilon tau ≤ target tau)
    (hsecond : ∀ tau : ℝ, range tau →
      heathBrownLogSecondExponent k epsilon ≤ target tau)
    (hthird : ∀ tau : ℝ, range tau →
      heathBrownLogThirdExponent k epsilon tau ≤ target tau) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N R : ℕ) (tau : ℝ),
      0 < N → N < R → R ≤ 2 * N → range tau →
      ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C * (N : ℝ) ^ target tau := by
  obtain ⟨C₀, hC₀, hbound⟩ :=
    norm_pintz2023ExponentialBlock_le_log_powers k epsilon hk hepsilon
  let A : ℝ := (pintz2023DerivativeConstant k) ^ pintz2023HBAlpha k
  let G : ℝ :=
    (pintz2023DerivativeConstant k) ^ (-pintz2023HBGamma k)
  let C : ℝ := C₀ * (A + 1 + G)
  have hA : 0 < A := by
    dsimp only [A]
    exact Real.rpow_pos_of_pos (pintz2023DerivativeConstant_pos k) _
  have hG : 0 < G := by
    dsimp only [G]
    exact Real.rpow_pos_of_pos (pintz2023DerivativeConstant_pos k) _
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N R tau hN hNR hR htau
  have hNOne : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hf := Real.rpow_le_rpow_of_exponent_le hNOne (hfirst tau htau)
  have hs := Real.rpow_le_rpow_of_exponent_le hNOne (hsecond tau htau)
  have ht := Real.rpow_le_rpow_of_exponent_le hNOne (hthird tau htau)
  have hraw := hbound N R tau hN hNR hR
  calc
    ‖pintz2023ExponentialBlock N R ((N : ℝ) ^ tau)‖ ≤
        C₀ *
          (A * (N : ℝ) ^ (heathBrownLogFirstExponent k epsilon tau) +
            (N : ℝ) ^ (heathBrownLogSecondExponent k epsilon) +
            G * (N : ℝ) ^ (heathBrownLogThirdExponent k epsilon tau)) := by
      simpa only [A, G] using hraw
    _ ≤ C₀ * ((A + 1 + G) * (N : ℝ) ^ target tau) := by
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      calc
        A * (N : ℝ) ^ (heathBrownLogFirstExponent k epsilon tau) +
              (N : ℝ) ^ (heathBrownLogSecondExponent k epsilon) +
              G * (N : ℝ) ^ (heathBrownLogThirdExponent k epsilon tau) ≤
            A * (N : ℝ) ^ target tau + (N : ℝ) ^ target tau +
              G * (N : ℝ) ^ target tau := by
          exact add_le_add
            (add_le_add (mul_le_mul_of_nonneg_left hf hA.le) hs)
            (mul_le_mul_of_nonneg_left ht hG.le)
        _ = (A + 1 + G) * (N : ℝ) ^ target tau := by ring
    _ = C * (N : ℝ) ^ target tau := by
      dsimp only [C]
      ring

#print axioms pintz2023_scaled_derivative_factor_at_rpow
#print axioms norm_pintz2023ExponentialBlock_le_log_powers
#print axioms norm_pintz2023ExponentialBlock_le_target_of_exponents

end

end GafniTao
