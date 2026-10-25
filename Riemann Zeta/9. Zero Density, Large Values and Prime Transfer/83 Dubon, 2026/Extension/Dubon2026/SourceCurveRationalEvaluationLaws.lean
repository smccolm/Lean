import Dubon2026.SourceCurveRationalResidueValues

/-! DUB-17/18 -> Weil nondegeneracy -> Kummer-cover evaluation transfer.
Use the existing actual rational residue map. These are precisely the
nonvanishing, product and natural-power identities used in the norm argument. -/
namespace Dubon2026.SourceCurve.Place
noncomputable section
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (v : Place K F) (hv : Function.Bijective (algebraMap K v.ResidueField))

theorem rationalEval_ne_zero_of_ord_eq_zero {f : F} (hf : f ≠ 0)
    (ho : v.ord f = 0) : v.rationalEval hv f ≠ 0 := by
  intro hz
  have hp := (v.rationalEval_eq_zero_iff_ord_pos hv (v.mem_of_ord_nonneg ho.ge) hf).mp hz
  rw [ho] at hp
  exact (lt_irrefl 0) hp

theorem rationalEval_mul_of_mem {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.rationalEval hv (f * g) = v.rationalEval hv f * v.rationalEval hv g := by
  rw [rationalEval_of_mem v hv (mul_mem hf hg), rationalEval_of_mem v hv hf,
    rationalEval_of_mem v hv hg]
  exact (v.rationalRegularEval hv).map_mul ⟨f, hf⟩ ⟨g, hg⟩

theorem rationalEval_pow_of_mem {f : F} (hf : f ∈ v.toValuationSubring) (n : ℕ) :
    v.rationalEval hv (f ^ n) = v.rationalEval hv f ^ n := by
  rw [rationalEval_of_mem v hv (pow_mem hf n), rationalEval_of_mem v hv hf]
  exact (v.rationalRegularEval hv).map_pow ⟨f, hf⟩ n

end
end Dubon2026.SourceCurve.Place
