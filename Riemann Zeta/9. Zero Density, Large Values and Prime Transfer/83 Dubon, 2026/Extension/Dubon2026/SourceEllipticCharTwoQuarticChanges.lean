import Dubon2026.SourceEllipticCharTwoCubicParameters
import Dubon2026.SourceEllipticCharTwoNegation

/-! DUB-17/18 -> characteristic-two weighted census -> actual fixed cyclic
subgroup counts. Construct the source automorphisms of native ofJ0 and prove
their exact quaternion relations. Existing stabilizer coordinates, negation,
primitive cubic roots and point-map naturality avoid duplicate foundations.
Source: anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, characteristic-two nuTwo solution. -/
namespace Dubon2026.SourceEllipticCharTwo
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [CharP K 2]

theorem stabilizer_cubic_coordinates_iff (γ : VariableChange K) :
    γ • ofJ0 K = ofJ0 K ↔
      (γ.u : K) ^ 3 = 1 ∧ γ.r = γ.s ^ 2 ∧ γ.s ^ 4 = γ.s ∧ γ.t ^ 2 + γ.t = γ.s ^ 3 := by
  rw [stabilizer_coordinates_iff]
  have hs (h : γ.s ^ 4 = γ.s) : γ.s ^ 6 = γ.s ^ 3 := by
    calc γ.s ^ 6 = γ.s ^ 4 * γ.s ^ 2 := by ring
      _ = γ.s * γ.s ^ 2 := by rw [h]
      _ = γ.s ^ 3 := by ring
  constructor
  · rintro ⟨hu, hr, h4, ht⟩
    exact ⟨hu, hr, h4, ht.trans (hs h4)⟩
  · rintro ⟨hu, hr, h4, ht⟩
    exact ⟨hu, hr, h4, ht.trans (hs h4).symm⟩

/-- The literal characteristic-two elliptic negation change. -/
def epsilonChange : VariableChange K := ⟨1, 0, 0, 1⟩

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)

/-- The actual order-four coordinate change used for the nuTwo count. -/
def quarticChange : VariableChange K := ⟨1, 1, 1, ω⟩

/-- The conjugate product whose point action squares to negation. -/
def quaternionChange : VariableChange K := ⟨1, ω ^ 2, ω, ω ^ 2⟩

include hω

/-- The nonzero cubic-root parameter as a unit. -/
def omegaUnit : Kˣ := Units.mk0 ω (omega_ne_zero ω hω)

omit [CharP K 2] in
theorem coe_omegaUnit : ((omegaUnit ω hω : Kˣ) : K) = ω := rfl

/-- The actual cubic scaling change used for the nuThree count. -/
def cubicChange : VariableChange K := ⟨omegaUnit ω hω, 0, 0, 0⟩

theorem quarticChange_smul : quarticChange ω • ofJ0 K = ofJ0 K :=
  (stabilizer_cubic_coordinates_iff _).2 ⟨by simp [quarticChange], by simp [quarticChange], by simp [quarticChange], by
    simp only [quarticChange, one_pow]
    have := CharTwo.neg_eq (1 : K)
    linear_combination hω + this⟩

theorem cubicChange_smul : cubicChange ω hω • ofJ0 K = ofJ0 K :=
  (stabilizer_cubic_coordinates_iff _).2 ⟨by simpa [cubicChange] using omega_pow_three ω hω, by simp [cubicChange], by simp [cubicChange], by simp [cubicChange]⟩

theorem quaternionChange_smul : quaternionChange ω • ofJ0 K = ofJ0 K := by
  have h3 := omega_pow_three ω hω
  have hsq := omega_sq ω hω
  refine (stabilizer_cubic_coordinates_iff _).2 ⟨by simp [quaternionChange], by simp [quaternionChange], ?_, ?_⟩
  · show ω ^ 4 = ω
    calc ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [h3, one_mul]
  · show (ω ^ 2) ^ 2 + ω ^ 2 = ω ^ 3
    rw [h3]
    have h2 := two_eq_zero K
    have : (ω ^ 2) ^ 2 = ω ^ 3 * ω := by ring
    rw [this, h3, one_mul, hsq]
    linear_combination ω * h2

omit hω in
theorem quarticChange_mul_quarticChange : quarticChange ω * quarticChange ω = epsilonChange := by
  ext
  · simp [VariableChange.mul_def, quarticChange, epsilonChange]
  · simp only [VariableChange.mul_def, quarticChange, epsilonChange, Units.val_one]; simpa using CharTwo.add_self_eq_zero (1 : K)
  · simp only [VariableChange.mul_def, quarticChange, epsilonChange, Units.val_one]; simpa using CharTwo.add_self_eq_zero (1 : K)
  · simp only [VariableChange.mul_def, quarticChange, epsilonChange, Units.val_one]
    have := CharTwo.add_self_eq_zero ω
    linear_combination this

omit [CharP K 2] in
theorem conj_quarticChange_eq : cubicChange ω hω * quarticChange ω * (cubicChange ω hω)⁻¹ = (⟨1, ω, ω ^ 2, ω⟩ : VariableChange K) := by
  have h3 := omega_pow_three ω hω
  have hne := omega_ne_zero ω hω
  have hinv : ω⁻¹ = ω ^ 2 := inv_eq_of_mul_eq_one_right (by
    calc ω * ω ^ 2 = ω ^ 3 := by ring
      _ = 1 := h3)
  have huinv : (((omegaUnit ω hω)⁻¹ : Kˣ) : K) = ω ^ 2 := by
    rw [Units.val_inv_eq_inv_val, coe_omegaUnit, hinv]
  have h4 : ω ^ 4 = ω := by
    calc ω ^ 4 = ω ^ 3 * ω := by ring
      _ = ω := by rw [h3, one_mul]
  have h7 : ω ^ 7 = ω := by
    calc ω ^ 7 = (ω ^ 3) ^ 2 * ω := by ring
      _ = ω := by rw [h3]; ring
  rw [VariableChange.inv_def]
  ext
  · simp [VariableChange.mul_def, quarticChange, cubicChange]
  · simp only [VariableChange.mul_def, quarticChange, cubicChange, Units.val_one, huinv]
    linear_combination h4
  · simp only [VariableChange.mul_def, quarticChange, cubicChange, Units.val_one, huinv]
    ring
  · simp only [VariableChange.mul_def, quarticChange, cubicChange, Units.val_one, huinv]
    linear_combination h7

theorem quaternionChange_eq : quaternionChange ω = quarticChange ω * (cubicChange ω hω * quarticChange ω * (cubicChange ω hω)⁻¹) := by
  rw [conj_quarticChange_eq ω hω]
  have h2 := two_eq_zero K
  have hsq := omega_sq ω hω
  ext
  · simp [VariableChange.mul_def, quarticChange, quaternionChange]
  · simp only [VariableChange.mul_def, quarticChange, quaternionChange, Units.val_one]
    rw [hsq]; ring
  · simp only [VariableChange.mul_def, quarticChange, quaternionChange, Units.val_one]
    have := CharTwo.neg_eq ω
    linear_combination -hω - this
  · simp only [VariableChange.mul_def, quarticChange, quaternionChange, Units.val_one]
    linear_combination -ω * h2

theorem quaternionChange_mul_quaternionChange : quaternionChange ω * quaternionChange ω = (epsilonChange : VariableChange K) := by
  have h2 := two_eq_zero K
  have h3 := omega_pow_three ω hω
  ext
  · simp [VariableChange.mul_def, quaternionChange, epsilonChange]
  · simp only [VariableChange.mul_def, quaternionChange, epsilonChange, Units.val_one]
    linear_combination ω ^ 2 * h2
  · simp only [VariableChange.mul_def, quaternionChange, epsilonChange, Units.val_one]
    linear_combination ω * h2
  · simp only [VariableChange.mul_def, quaternionChange, epsilonChange, Units.val_one]
    linear_combination ω ^ 2 * h2 + h3


end
end Dubon2026.SourceEllipticCharTwo
