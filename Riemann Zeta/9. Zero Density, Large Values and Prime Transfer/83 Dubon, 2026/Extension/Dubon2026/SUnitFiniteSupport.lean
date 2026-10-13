import Dubon2026.SUnitValuationKernel
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

/-! # Actual finite support for original radical coefficients

The pinned diagonal finite-adele map already proves that a field unit has
valuation one outside finitely many original places. Reusing it supplies
a finite S containing any finite family of original Kummer coefficients,
needed to place a prescribed finite abelian extension inside the full
S-unit radical field in DUB-17's global norm-index dependency.
-/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- An original field unit has valuation one away from a finite set of original places. -/
theorem unit_valuation_support_finite (x : Kˣ) :
    {v : HeightOneSpectrum R | v.valuation K x.val ≠ 1}.Finite := by
  have h := ((FiniteAdeleRing.isUnit_iff (a :=
    algebraMap K (FiniteAdeleRing R K) x.val)).mp
      (x.isUnit.map (algebraMap K (FiniteAdeleRing R K)))).2
  simpa only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.adicCompletion,
    Valued.valuedCompletion_apply, Filter.eventually_cofinite, Set.compl_setOf] using h

/-- Every finite family of original field units belongs to one actual finite S-unit group. -/
theorem exists_finite_sUnit_support (s : Finset Kˣ) :
    ∃ S : Finset (HeightOneSpectrum R), ∀ x ∈ s, x ∈ (S : Set (HeightOneSpectrum R)).unit K := by
  classical
  let S := s.biUnion fun x => (unit_valuation_support_finite (R := R) x).toFinset
  refine ⟨S, ?_⟩
  intro x hx v hv
  by_contra h
  apply hv
  exact Finset.mem_biUnion.mpr ⟨x, hx, by simpa only [Set.Finite.mem_toFinset] using h⟩

end
end Dubon2026
