import Dubon2026.SourceOriginalWeilCoverTwoPoleDifferential
import Dubon2026.SourceOriginalWeilCoverSimplePoleBounds

/-! DUB-17/18 -> cover Abel converse -> prescribed residues. The actual
global residue sum normalizes the proved two-pole differential to +1 and -1.
No normalized two-pole differential is supplied as an assumption. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) (r : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C r : Polynomial FF)

theorem cover_two_pole_residue_sum {P Q : Place ℂ EE} (hPQ : P ≠ Q)
    (ω : Ω[EE⁄ℂ])
    (hreg : ∀ v : Place ℂ EE, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω) :
    coverDifferentialResidue N n r P ω + coverDifferentialResidue N n r Q ω = 0 := by
  classical
  have hs : Function.support (fun v => coverDifferentialResidue N n r v ω) ⊆
      ({P, Q} : Finset (Place ℂ EE)) := by
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    by_contra hn
    push Not at hn
    exact hv (coverDifferentialResidue_eq_zero_of_regular N n r v ω (hreg v hn.1 hn.2))
  have h := coverDifferentialResidue_finsum N n r ω
  rwa [finsum_eq_sum_of_support_subset _ hs, Finset.sum_pair hPQ] at h

open scoped Classical in
theorem exists_cover_normalized_two_pole_differential {P Q : Place ℂ EE} (hPQ : P ≠ Q) :
    ∃ η : Ω[EE⁄ℂ], (∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η) ∧
      ∀ v : Place ℂ EE, coverDifferentialResidue N n r v η =
        (if v = P then 1 else 0) - (if v = Q then 1 else 0) := by
  classical
  obtain ⟨ω, _, hP, hQ, hreg⟩ := exists_cover_two_pole_differential N n r hPQ
  have hbound : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential ω := by
    intro v
    by_cases hvP : v = P
    · rw [hvP, hP]
    by_cases hvQ : v = Q
    · rw [hvQ, hQ]
    have h := hreg v hvP hvQ
    omega
  have hPn := coverDifferentialResidue_ne_zero_of_simplePole N n r P ω hP
  have hsum := cover_two_pole_residue_sum N n r hPQ ω hreg
  have hQres : coverDifferentialResidue N n r Q ω = -coverDifferentialResidue N n r P ω :=
    eq_neg_of_add_eq_zero_right hsum
  refine ⟨(coverDifferentialResidue N n r P ω)⁻¹ • ω,
    fun v => cover_simple_pole_smul_bound N n r v _ (hbound v), ?_⟩
  intro v
  rw [map_smul, smul_eq_mul]
  by_cases hvP : v = P
  · subst v
    simp [hPQ, hPn]
  by_cases hvQ : v = Q
  · subst v
    rw [hQres, mul_neg, inv_mul_cancel₀ hPn]
    simp [hPQ.symm]
  rw [coverDifferentialResidue_eq_zero_of_regular N n r v ω (hreg v hvP hvQ), mul_zero]
  simp only [if_neg hvP, if_neg hvQ, sub_self]


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
