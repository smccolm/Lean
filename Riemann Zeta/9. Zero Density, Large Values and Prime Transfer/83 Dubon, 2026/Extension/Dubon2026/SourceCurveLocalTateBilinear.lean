import Dubon2026.SourceCurveLocalTateLeibniz

/-! Additivity and constant-field linearity of the actual local Tate
residue pairing. These combine with its proved Leibniz rule to give a
derivation into the dual of the function field, the remaining local input
to the differential chain rule in the global residue argument. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- Addition in the first multiplication slot adds the literal commutator operators. -/
theorem tateComm_add_fst (f g h : F) :
    tateCommRestrict v.tateProj (Algebra.lmul K F (f + g)) (Algebra.lmul K F h) =
      tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F h) +
      tateCommRestrict v.tateProj (Algebra.lmul K F g) (Algebra.lmul K F h) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change v.tateProj ((f + g) * v.tateProj (h * (a : F))) -
      v.tateProj (h * v.tateProj ((f + g) * (a : F))) =
    (v.tateProj (f * v.tateProj (h * (a : F))) - v.tateProj (h * v.tateProj (f * (a : F)))) +
    (v.tateProj (g * v.tateProj (h * (a : F))) - v.tateProj (h * v.tateProj (g * (a : F))))
  simp only [add_mul, map_add, mul_add]
  abel

/-- Addition in the second multiplication slot adds the literal commutator operators. -/
theorem tateComm_add_snd (f g h : F) :
    tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F (g + h)) =
      tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F g) +
      tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F h) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change v.tateProj (f * v.tateProj ((g + h) * (a : F))) -
      v.tateProj ((g + h) * v.tateProj (f * (a : F))) =
    (v.tateProj (f * v.tateProj (g * (a : F))) - v.tateProj (g * v.tateProj (f * (a : F)))) +
    (v.tateProj (f * v.tateProj (h * (a : F))) - v.tateProj (h * v.tateProj (f * (a : F))))
  simp only [add_mul, map_add, mul_add]
  abel

/-- A scalar in the first slot scales the literal commutator. -/
theorem tateComm_smul_fst (c : K) (f g : F) :
    tateCommRestrict v.tateProj (Algebra.lmul K F (c • f)) (Algebra.lmul K F g) =
      c • tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F g) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change v.tateProj ((c • f) * v.tateProj (g * (a : F))) -
      v.tateProj (g * v.tateProj ((c • f) * (a : F))) =
    c • (v.tateProj (f * v.tateProj (g * (a : F))) -
      v.tateProj (g * v.tateProj (f * (a : F))))
  simp only [smul_mul_assoc, mul_smul_comm, map_smul, smul_sub]

/-- A scalar in the second slot scales the literal commutator. -/
theorem tateComm_smul_snd (c : K) (f g : F) :
    tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F (c • g)) =
      c • tateCommRestrict v.tateProj (Algebra.lmul K F f) (Algebra.lmul K F g) := by
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change v.tateProj (f * v.tateProj ((c • g) * (a : F))) -
      v.tateProj ((c • g) * v.tateProj (f * (a : F))) =
    c • (v.tateProj (f * v.tateProj (g * (a : F))) -
      v.tateProj (g * v.tateProj (f * (a : F))))
  simp only [smul_mul_assoc, mul_smul_comm, map_smul, smul_sub]

/-- The actual local residue is additive in its first slot. -/
theorem tateResidue_add_fst
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g h : F) :
    v.tateResidue (f + g) h = v.tateResidue f h + v.tateResidue g h := by
  haveI := v.finite_range_tate_commutator hres f h
  haveI := v.finite_range_tate_commutator hres g h
  unfold tateResidue tateCommTrace
  rw [v.tateComm_add_fst, finrankTrace_add]

/-- The actual local residue is additive in its second slot. -/
theorem tateResidue_add_snd
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (f g h : F) :
    v.tateResidue f (g + h) = v.tateResidue f g + v.tateResidue f h := by
  haveI := v.finite_range_tate_commutator hres f g
  haveI := v.finite_range_tate_commutator hres f h
  unfold tateResidue tateCommTrace
  rw [v.tateComm_add_snd, finrankTrace_add]

/-- The actual local residue is constant-field linear in its first slot. -/
theorem tateResidue_smul_fst
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (c : K) (f g : F) :
    v.tateResidue (c • f) g = c • v.tateResidue f g := by
  haveI := v.finite_range_tate_commutator hres f g
  unfold tateResidue tateCommTrace
  rw [v.tateComm_smul_fst, finrankTrace_smul]

/-- The actual local residue is constant-field linear in its second slot. -/
theorem tateResidue_smul_snd
    (hres : Function.Surjective (algebraMap K v.ResidueField)) (c : K) (f g : F) :
    v.tateResidue f (c • g) = c • v.tateResidue f g := by
  haveI := v.finite_range_tate_commutator hres f g
  unfold tateResidue tateCommTrace
  rw [v.tateComm_smul_snd, finrankTrace_smul]

end Dubon2026.SourceCurve.Place
