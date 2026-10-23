import Dubon2026.SourceReductionPolynomialCover

/-! DUB-17/18 -> original Frobenius/inertia -> good reduction -> genus
comparison -> pole-bound preservation under residue. A transcendental residue
coordinate has a transcendental lift, and an integral polynomial value has
integral coefficients. Both conclusions reuse the proved normalization and
residue independence arguments, avoiding a second coefficient-normalization
proof. They are inputs to the integral minimal-polynomial pole bound. -/
namespace Dubon2026.SourceCurve.RegularProlongation
noncomputable section
open IsLocalRing Polynomial
variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : RegularProlongation A F Fbar) (x : R.integers)
variable (hx : Transcendental (ResidueField A) (R.residue x))

include hx in
theorem transcendental_of_residue_transcendental : Transcendental L (x : F) := by
  rw [transcendental_iff]
  intro p hp
  by_contra hp0
  obtain ⟨U, hU, c, _, hUc⟩ := exists_normalize_aeval R x hx p hp0
  have hU0 : U = 0 := Subtype.ext (by rw [hUc, hp, mul_zero]; rfl)
  exact hU (hU0 ▸ map_zero R.residue)

include hx in
theorem coeff_mem_of_aeval_mem_integers (p : Polynomial L)
    (hp : aeval (x : F) p ∈ R.integers) (i : ℕ) : p.coeff i ∈ A := by
  by_cases hi : i < p.natDegree + 1
  · apply mem_of_sum_smul_mem R (fun j : ℕ => x ^ j)
      (linearIndependent_residue_pow R x hx)
      (Finset.range (p.natDegree + 1)) p.coeff ?_ i (Finset.mem_range.mpr hi)
    change (∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j • (x : F) ^ j) ∈ R.integers
    rwa [← Polynomial.aeval_eq_sum_range]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < i)]
    exact A.zero_mem

end
end Dubon2026.SourceCurve.RegularProlongation
