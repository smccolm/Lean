import Dubon2026.SourceEllipticShortStabilizer
import Dubon2026.SourceEllipticQuarticModel
import Dubon2026.SourceEllipticCubicModel
import Dubon2026.SourceEllipticStabilizerScaling

/-! DUB-17/18 -> exceptional place census. Native coefficient formulas
classify the scaling factors of the actual short-model stabilizers.
Their roots have the two or three possibilities modulo sign needed by
the cyclic-subgroup orbit relation. Adapted root factorizations from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the exceptional moduli-fiber counts. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve SourceEllipticStabilizer
noncomputable section
variable {K : Type*} [Field K]

theorem quartic_stabilizer_scaling (A : K) (hA : A ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (C : VariableChange K) (hC : C • EA A = EA A) :
    C = ⟨C.u, 0, 0, 0⟩ ∧ (C.u : K) ^ 4 = 1 := by
  have he := variableChange_eq_pure_of_translation_zero C
    (short_stabilizer_translation_zero (EA A) rfl rfl rfl h2 h3 C hC)
  have hC' : (⟨C.u, 0, 0, 0⟩ : VariableChange K) • EA A = EA A := by
    rw [← he]
    exact hC
  have h4 : ((C.u⁻¹ : Kˣ) : K) ^ 4 * A = A := by
    simpa [variableChange_a₄] using congrArg WeierstrassCurve.a₄ hC'
  exact ⟨he, scaling_pow_of_invariant hA h4⟩

theorem cubic_stabilizer_scaling (B : K) (hB : B ≠ 0)
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    (C : VariableChange K) (hC : C • EB B = EB B) :
    C = ⟨C.u, 0, 0, 0⟩ ∧ (C.u : K) ^ 6 = 1 := by
  have he := variableChange_eq_pure_of_translation_zero C
    (short_stabilizer_translation_zero (EB B) rfl rfl rfl h2 h3 C hC)
  have hC' : (⟨C.u, 0, 0, 0⟩ : VariableChange K) • EB B = EB B := by
    rw [← he]
    exact hC
  have h6 : ((C.u⁻¹ : Kˣ) : K) ^ 6 * B = B := by
    simpa [variableChange_a₆] using congrArg WeierstrassCurve.a₆ hC'
  exact ⟨he, scaling_pow_of_invariant hB h6⟩

theorem fourth_roots_mod_sign {u v : K} (hu : u ^ 2 = -1) (hv : v ^ 4 = 1) :
    (v = 1 ∨ v = -1) ∨ (v = u ∨ v = -u) := by
  have hz : (v - 1) * (v + 1) * (v - u) * (v + u) = 0 := by
    have he : (v - 1) * (v + 1) * (v - u) * (v + u) =
        (v ^ 2 - 1) * (v ^ 2 - u ^ 2) := by ring
    rw [he, hu]
    linear_combination hv
  rcases mul_eq_zero.mp hz with hz | hz
  · rcases mul_eq_zero.mp hz with hz | hz
    · rcases mul_eq_zero.mp hz with hz | hz
      · exact Or.inl (Or.inl (sub_eq_zero.mp hz))
      · exact Or.inl (Or.inr (eq_neg_of_add_eq_zero_left hz))
    · exact Or.inr (Or.inl (sub_eq_zero.mp hz))
  · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left hz))

theorem cubic_roots_cases {u v : K} (hu : u ^ 3 = 1) (hu1 : u ≠ 1) (hv : v ^ 3 = 1) :
    v = 1 ∨ v = u ∨ v = u ^ 2 := by
  have hu' : u ^ 2 + u + 1 = 0 := by
    have hz : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination hu
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hu1)
  have hz : (v - 1) * (v - u) * (v - u ^ 2) = 0 := by
    linear_combination hv + (-v ^ 2 + u * v + 1 - u) * hu'
  rcases mul_eq_zero.mp hz with hz | hz
  · rcases mul_eq_zero.mp hz with hz | hz
    · exact Or.inl (sub_eq_zero.mp hz)
    · exact Or.inr (Or.inl (sub_eq_zero.mp hz))
  · exact Or.inr (Or.inr (sub_eq_zero.mp hz))

theorem sixth_roots_mod_sign {u v : K} (hu : u ^ 3 = 1) (hu1 : u ≠ 1) (hv : v ^ 6 = 1) :
    (v = 1 ∨ v = -1) ∨ (v = u ∨ v = -u) ∨ (v = u ^ 2 ∨ v = -(u ^ 2)) := by
  have hz : (v ^ 3 - 1) * (v ^ 3 + 1) = 0 := by linear_combination hv
  rcases mul_eq_zero.mp hz with hz | hz
  · rcases cubic_roots_cases hu hu1 (sub_eq_zero.mp hz) with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inr (Or.inl h))
  · have hn : (-v) ^ 3 = 1 := by linear_combination -hz
    rcases cubic_roots_cases hu hu1 hn with h | h | h
    · exact Or.inl (Or.inr (neg_eq_iff_eq_neg.mp h))
    · exact Or.inr (Or.inl (Or.inr (neg_eq_iff_eq_neg.mp h)))
    · exact Or.inr (Or.inr (Or.inr (neg_eq_iff_eq_neg.mp h)))

end
end Dubon2026.SourceEllipticExceptional
