import Dubon2026.SourceReductionIntegralMultiples

/-! DUB-17/18 -> Kummer power lifting -> genus inequality -> monic torsion
of the residue chart quotients. Native integral multiples clear a function's
coordinate denominator; the existing coefficient normalizer gives an integral
polynomial whose residue is nonzero. This avoids a new valuation-extension
or polynomial-denominator existence argument. -/
namespace Dubon2026.SourceCurve.RegularProlongation.Joint
noncomputable section
open Polynomial IsLocalRing

theorem exists_integral_chart_residue_polynomial
    {L F : Type*} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    (f : F) (hfin : 0 < Module.finrank (IntermediateField.adjoin L ({f} : Set F)) F)
    (z : F) : ∃ q : Polynomial A, q.map (IsLocalRing.residue A) ≠ 0 ∧
      IsIntegral (Algebra.adjoin L ({f} : Set F))
        (q.eval₂ ((algebraMap L F).comp A.subtype) f * z) := by
  classical
  obtain ⟨p, hp0, hpz⟩ := exists_chart_integral_multiple f hfin z
  let t := Finset.range (p.natDegree + 1)
  obtain ⟨j, hjt, hc0, hcA, -⟩ := exists_normalizer (A := A) t p.coeff
    (Finset.self_mem_range_succ _) (Polynomial.leadingCoeff_ne_zero.mpr hp0)
  let qL : Polynomial L := C (p.coeff j)⁻¹ * p
  have hqcoeff (n : ℕ) : qL.coeff n ∈ A := by
    dsimp only [qL]
    rw [coeff_C_mul]
    by_cases hn : n ∈ t
    · exact hcA n hn
    · have hn' : p.natDegree < n := by
        have : ¬n < p.natDegree + 1 := by simpa only [t, Finset.mem_range] using hn
        omega
      rw [coeff_eq_zero_of_natDegree_lt hn', mul_zero]
      exact A.zero_mem
  have hqLift : qL ∈ Polynomial.lifts A.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, hqcoeff n⟩, rfl⟩
  obtain ⟨q, hq⟩ := (Polynomial.mem_lifts qL).mp hqLift
  have hqj : q.coeff j = 1 := by
    apply Subtype.ext
    have h := congrArg (fun r : Polynomial L => r.coeff j) hq
    simpa only [coeff_map, qL, coeff_C_mul, inv_mul_cancel₀ hc0] using h
  refine ⟨q, ?_, ?_⟩
  · intro h0
    have h := congrArg (fun r : Polynomial (ResidueField A) => r.coeff j) h0
    apply (one_ne_zero : (1 : ResidueField A) ≠ 0)
    simpa only [coeff_map, hqj, map_one, coeff_zero] using h
  · have hc : IsIntegral (Algebra.adjoin L ({f} : Set F))
        (algebraMap L F (p.coeff j)⁻¹) :=
      (isIntegral_algebraMap (R := L) (A := F) (x := (p.coeff j)⁻¹)).tower_top
    have he : q.eval₂ ((algebraMap L F).comp A.subtype) f = aeval f qL := by
      rw [← hq, aeval_def, eval₂_map]
    rw [he]
    dsimp only [qL]
    rw [map_mul, aeval_C, mul_assoc]
    exact hc.mul hpz

end
end Dubon2026.SourceCurve.RegularProlongation.Joint
