import Dubon2026.SourceConstantFieldIndependentOrders
import Dubon2026.SourceConstantFieldIndependentRepresentation
import Dubon2026.SourceOriginalDivisorConorm
import Dubon2026.SourceOriginalPrincipalDivisors

/-! DUB-17/18 -> original arithmetic Picard injectivity. An actual arithmetic
divisor whose conorm is principal is already principal. Function-span descent
gives independent complex coefficients; exact local orders bound the divisor
by a nonzero arithmetic coefficient's principal divisor. Both have degree
zero, so the effective difference vanishes. No descent premise is assumed.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
local notation "FC" => modularFunctionFieldOver N ℂ
attribute [local instance] complexAlgebra fieldAlgebra complexFieldAlgebra
  complexScalarTower originalFieldScalarTower

theorem original_degree_eq_sum (D : Divisor Qbar FQ) :
    Divisor.degree D = D.sum fun _ n => n := by
  have hres (v : Place Qbar FQ) : Module.finrank Qbar v.ResidueField = 1 :=
    Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N Qbar v)
  simp only [Divisor.degree_eq_sum_support, hres, Nat.cast_one, mul_one, Finsupp.sum]

theorem isPrincipal_of_conorm {D : Divisor Qbar FQ}
    (hD : Divisor.IsPrincipal (conorm N D)) : Divisor.IsPrincipal D := by
  classical
  obtain ⟨z, hz0, hzD⟩ := hD
  have hzspan := original_mem_span_of_regular_off_image N z (by
    intro W hW
    apply W.mem_of_ord_nonneg
    rw [← hzD, conorm_apply_of_forall_ne N D hW])
  obtain ⟨n, β, u, hβ, hzu⟩ := ConstantField.exists_linearIndependent_repr
    (K := Qbar) (F := FQ) (K' := ℂ) (F' := FC) hzspan
  obtain ⟨k₀, hk₀⟩ : ∃ k, u k ≠ 0 := by
    by_contra h
    push Not at h
    apply hz0
    rw [hzu]
    simp [h]
  have hle (P : Place Qbar FQ) : D P ≤ P.ord (u k₀) := by
    have h := ConstantField.ord_sum_le P (liftPlace N P)
      (original_place_residue_algebraMap_bijective N Qbar P).surjective
      (liftPlace_comap N P) (ord_liftPlace N P) Finset.univ β hβ u
      (Finset.mem_univ k₀) hk₀
    rw [← hzu, ← hzD, conorm_apply_liftPlace] at h
    exact h
  have hdegD : Divisor.degree D = 0 := by
    have he : conorm N D = originalPrincipalDivisor N ℂ z := Finsupp.ext hzD
    rw [← degree_conorm N D, he, degree_originalPrincipalDivisor]
  let E := originalPrincipalDivisor N Qbar (u k₀)
  have hG : ∀ v, 0 ≤ (E - D) v := fun v => by
    change 0 ≤ v.ord (u k₀) - D v
    exact sub_nonneg.mpr (hle v)
  have hGdeg : Divisor.degree (E - D) = 0 := by
    rw [map_sub, degree_originalPrincipalDivisor, hdegD, sub_zero]
  have hG0 : E - D = 0 := by
    rw [original_degree_eq_sum, Finsupp.sum] at hGdeg
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hG v)).mp hGdeg
    ext v
    by_cases hv : v ∈ (E - D).support
    · exact h v hv
    · exact Finsupp.notMem_support_iff.mp hv
  refine ⟨u k₀, hk₀, fun v => ?_⟩
  have he : E = D := sub_eq_zero.mp hG0
  rw [← he]
  rfl

end
end Dubon2026.SourceFunctionField.OriginalConstantField
