import Dubon2026.SourceOriginalPrescribedPlaceOrders
import Dubon2026.SourceOriginalFinitePlaceExhaustion
import Dubon2026.SourceOriginalPicardGroup
import Dubon2026.SourceOriginalDivisorSupport
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> full original Picard-period Hecke compatibility ->
analytic representatives of every divisor class. Prescribe the divisor's
orders on the finite support of j, subtract the actual principal divisor,
and use proved analytic exhaustion at every remaining support point.
Adapted from exists_decomp in
S_ModularCurve_exists_heckeEquivariant_addEquiv_pic0_complex_quotient_periodLattice,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
All places, orders and principal divisors here are the original objects.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane SourceCurve
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_divisor_analytic_decomposition (D : Divisor ℂ F) :
    ∃ (E : Divisor ℂ F) (c : ℍ →₀ ℤ),
      Divisor.IsPrincipal E ∧ Divisor.degree E = 0 ∧
      D = E + Finsupp.mapDomain (originalAnalyticPlace N) c := by
  classical
  let S := (finite_original_divisor_support N ℂ (jOver N ℂ)).toFinset
  obtain ⟨x, hx0, hx⟩ := exists_original_prescribed_place_orders N S D
  letI := hasPrincipalDivisors_original N ℂ
  obtain ⟨E, hE, hE0⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) x hx0
  let D' := D - E
  have hfinite : ∀ v ∈ D'.support, jOver N ℂ ∈ v.toValuationSubring := by
    intro v hv
    apply v.mem_of_ord_nonneg
    have hnot : v ∉ S := by
      intro hS
      apply Finsupp.mem_support_iff.mp hv
      change D v - E v = 0
      rw [hE, hx v hS, sub_self]
    have he : v.ord (jOver N ℂ) = 0 := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hnot
    exact he ▸ le_rfl
  let lift : Place ℂ F → ℍ := fun v =>
    if h : jOver N ℂ ∈ v.toValuationSubring then
      (exists_original_analytic_place_eq N v h).choose else I
  have hlift : ∀ v ∈ D'.support, originalAnalyticPlace N (lift v) = v := by
    intro v hv
    simp only [lift, dif_pos (hfinite v hv)]
    exact (exists_original_analytic_place_eq N v (hfinite v hv)).choose_spec
  have hcomp : Finsupp.mapDomain (originalAnalyticPlace N) (Finsupp.mapDomain lift D') = D' := by
    rw [← Finsupp.mapDomain_comp]
    calc
      Finsupp.mapDomain (originalAnalyticPlace N ∘ lift) D' = Finsupp.mapDomain id D' :=
        Finsupp.mapDomain_congr (fun v hv => hlift v hv)
      _ = D' := by rw [Finsupp.mapDomain_id]
  refine ⟨E, Finsupp.mapDomain lift D', ⟨x, hx0, hE⟩, hE0, ?_⟩
  rw [hcomp]
  dsimp only [D']
  abel

theorem degree_mapDomain_originalAnalyticPlace (c : ℍ →₀ ℤ) :
    Divisor.degree (Finsupp.mapDomain (originalAnalyticPlace N) c) =
      c.sum (fun _ n => n) := by
  classical
  have hr : ∀ P : Place ℂ F, Module.finrank ℂ P.ResidueField = 1 := fun P =>
    Module.finrank_of_bijective_algebraMap (original_place_residue_algebraMap_bijective N ℂ P)
  induction c using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, Finsupp.mapDomain_single, ih,
      Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl,
      Divisor.degree_single, hr]
    simp

theorem exists_original_degree_zero_analytic_representative
    (D : Divisor ℂ F) (hD : Divisor.degree D = 0) :
    ∃ (E : Divisor ℂ F) (c : ℍ →₀ ℤ),
      Divisor.IsPrincipal E ∧ Divisor.degree E = 0 ∧ c.sum (fun _ n => n) = 0 ∧
      D = E + Finsupp.mapDomain (originalAnalyticPlace N) c := by
  obtain ⟨E, c, hE, hE0, he⟩ := exists_original_divisor_analytic_decomposition N D
  refine ⟨E, c, hE, hE0, ?_, he⟩
  rw [he, map_add, hE0, zero_add, degree_mapDomain_originalAnalyticPlace] at hD
  exact hD

end
end Dubon2026.SourceFunctionField
