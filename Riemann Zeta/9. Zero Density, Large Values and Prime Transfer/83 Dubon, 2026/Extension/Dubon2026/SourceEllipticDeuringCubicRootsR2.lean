import Dubon2026.SourceEllipticDeuringThreeTorsionR2

/-! DUB-17/18 -> characteristic-two modular genus/Picard -> faithful inertia.
The actual finite Deuring generator field is adapted from
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero.
Existing local division-field and exact torsion-cardinality proofs are reused. -/
namespace Dubon2026.SourceEllipticDeuring
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
open SourceEllipticDivisionField
noncomputable section
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [DecidableEq Ω]

variable (E : WeierstrassCurve F)

/-- All cubic roots of second division values at nonzero three-torsion points. -/
def cubeRoots : Set Ω :=
  {q | ∃ P : (E.baseChange Ω).toAffine.Point, (3 : ℕ) • P = 0 ∧ P ≠ 0 ∧ q ^ 3 = psi2 E P}

variable [E.IsElliptic] [IsAlgClosed Ω] (h3 : (3 : F) ≠ 0)

include h3 in
lemma finite_cubeRoots : (cubeRoots (Ω := Ω) E).Finite := by
  haveI := finite_three_torsion (Ω := Ω) E h3
  have h1 : cubeRoots (Ω := Ω) E ⊆
      ⋃ P : {P : (E.baseChange Ω).toAffine.Point // (3 : ℕ) • P = 0},
        {q : Ω | q ^ 3 = psi2 E P.1} := by
    rintro q ⟨P, hP, -, hq⟩
    exact Set.mem_iUnion.mpr ⟨⟨P, hP⟩, hq⟩
  refine Set.Finite.subset (Set.finite_iUnion fun P => ?_) h1
  have : {q : Ω | q ^ 3 = psi2 E P.1} = ((nthRoots 3 (psi2 E P.1)).toFinset : Set Ω) := by
    ext q
    rw [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots (by norm_num)]
  rw [this]
  exact Finset.finite_toSet _

omit [E.IsElliptic] [IsAlgClosed Ω] in
lemma map_mem_cubeRoots (φ : Ω →ₐ[F] Ω) {q : Ω} (hq : q ∈ cubeRoots E) : φ q ∈ cubeRoots E := by
  obtain ⟨P, hP, hP0, hq⟩ := hq
  refine ⟨Point.map φ P, by rw [← map_nsmul, hP, map_zero], ?_, ?_⟩
  · intro h
    apply hP0
    apply Point.map_injective φ
    rw [h, map_zero]
  · rw [psi2_map, ← map_pow, hq]

end
end Dubon2026.SourceEllipticDeuring
