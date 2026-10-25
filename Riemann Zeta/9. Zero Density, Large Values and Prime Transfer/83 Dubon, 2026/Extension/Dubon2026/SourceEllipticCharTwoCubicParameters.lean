import Dubon2026.SourceEllipticCharTwoStabilizerCoordinates
import Dubon2026.SourceEllipticExceptionalJValues

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

variable (ω : K) (hω : ω ^ 2 + ω + 1 = 0)
include hω

omit [CharP K 2] in
theorem omega_pow_three : ω ^ 3 = 1 := by
  have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
  rw [hω, mul_zero] at h1
  linear_combination -h1

theorem omega_ne_one : ω ≠ 1 := by
  intro h
  rw [h] at hω
  have : (3 : K) = 0 := by linear_combination hω
  rw [three_eq_one K] at this
  exact one_ne_zero this

omit [CharP K 2] in
theorem omega_ne_zero : ω ≠ 0 := by
  intro h
  rw [h] at hω
  simp at hω

theorem omega_sq : ω ^ 2 = ω + 1 := by
  have h1 := CharTwo.neg_eq ω
  have h2 := CharTwo.neg_eq (1 : K)
  linear_combination hω + h1 + h2


omit hω in
theorem exists_omega [IsAlgClosed K] : ∃ ω : K, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨u, hu, hu1⟩ := SourceEllipticExceptional.exists_cubic_scaling (K := K)
    (by rw [three_eq_one]; exact one_ne_zero)
  refine ⟨u, (mul_eq_zero.mp ?_).resolve_left (sub_ne_zero.mpr hu1)⟩
  calc ((u : K) - 1) * ((u : K) ^ 2 + (u : K) + 1) = (u : K) ^ 3 - 1 := by ring
    _ = 0 := by rw [hu, sub_self]

end
end Dubon2026.SourceEllipticCharTwo
