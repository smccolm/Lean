import Dubon2026.SourceGammaOneCanonicalFiberLower
import Dubon2026.SourceGammaOneRegularCuspEquiv

/-! DUB-17/18 -> actual Gamma1 real period surjectivity -> genus lower
bound. The proved finite-coordinate support supplies the actual three
exceptional finite sets. Canonical degree converts their contribution
bound to the dimension of regular differentials, and the literal
Fourier equivalence identifies that dimension with weight-two cusp forms. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open SourceCurve IntermediateField CongruenceSubgroup
open scoped MatrixGroups IntermediateField
variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)

include hT in
theorem regular_dimension_lower_fiber_cards :
    (Module.finrank ℂ⟮jCoordinateOver Γ ℂ⟯ (functionFieldOver Γ ℂ) : ℤ) -
      Nat.card {v : Place ℂ (functionFieldOver Γ ℂ) // 0 < v.ord (jCoordinateOver Γ ℂ)} -
      Nat.card {v : Place ℂ (functionFieldOver Γ ℂ) //
        0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) 1728)} -
      Nat.card {v : Place ℂ (functionFieldOver Γ ℂ) // v.ord (jCoordinateOver Γ ℂ) < 0} ≤
        2 * (Module.finrank ℂ (regularDifferentials ℂ (functionFieldOver Γ ℂ)) : ℤ) - 2 := by
  classical
  letI := finiteDimensional_jCoordinateOver hT ℂ
  have hf (f : functionFieldOver Γ ℂ) : {v : Place ℂ (functionFieldOver Γ ℂ) | v.ord f ≠ 0}.Finite :=
    finite_function_support_of_separating_coordinate (jCoordinateOver Γ ℂ)
      (transcendental_jCoordinateOver Γ ℂ) f
  have hz : {v : Place ℂ (functionFieldOver Γ ℂ) | 0 < v.ord (jCoordinateOver Γ ℂ)}.Finite :=
    (hf _).subset fun _ hv => ne_of_gt hv
  have he : {v : Place ℂ (functionFieldOver Γ ℂ) |
      0 < v.ord (jCoordinateOver Γ ℂ - algebraMap ℂ (functionFieldOver Γ ℂ) 1728)}.Finite :=
    (hf _).subset fun _ hv => ne_of_gt hv
  have hp : {v : Place ℂ (functionFieldOver Γ ℂ) | v.ord (jCoordinateOver Γ ℂ) < 0}.Finite :=
    (hf _).subset fun _ hv => ne_of_lt hv
  have hcard {P : Place ℂ (functionFieldOver Γ ℂ) → Prop}
      (h : {v | P v}.Finite) : Nat.card {v // P v} = h.toFinset.card := by
    calc
      _ = Nat.card ↥h.toFinset := Nat.card_congr
        (Equiv.subtypeEquivRight fun v => (h.mem_toFinset (a := v)).symm)
      _ = _ := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcard hz, hcard he, hcard hp]
  have h := jCanonical_degree_lower_finsets hT hz.toFinset he.toFinset hp.toFinset
    (fun v => hz.mem_toFinset) (fun v => he.mem_toFinset) (fun v => hp.mem_toFinset)
  rwa [jCanonicalDivisor_degree hT] at h

theorem gammaOne_cusp_dimension_lower_fiber_cards (N : ℕ) [NeZero N] :
    ((plusMinus (Gamma1 N)).index : ℤ) -
      Nat.card {v : Place ℂ (functionFieldOver (Gamma1 N) ℂ) //
        0 < v.ord (jCoordinateOver (Gamma1 N) ℂ)} -
      Nat.card {v : Place ℂ (functionFieldOver (Gamma1 N) ℂ) //
        0 < v.ord (jCoordinateOver (Gamma1 N) ℂ -
          algebraMap ℂ (functionFieldOver (Gamma1 N) ℂ) 1728)} -
      Nat.card {v : Place ℂ (functionFieldOver (Gamma1 N) ℂ) //
        v.ord (jCoordinateOver (Gamma1 N) ℂ) < 0} ≤
        2 * (Module.finrank ℂ (CuspForm (Gamma1 N) 2) : ℤ) - 2 := by
  have ht : ModularGroup.T ∈ Gamma1 N := by simp [Gamma1_mem, ModularGroup.T]
  have h := regular_dimension_lower_fiber_cards ht
  rw [finrank_over_j_eq_index N ht, (regularCuspEquiv N).finrank_eq] at h
  exact h

end
end Dubon2026.SourceFunctionField.GammaOne
