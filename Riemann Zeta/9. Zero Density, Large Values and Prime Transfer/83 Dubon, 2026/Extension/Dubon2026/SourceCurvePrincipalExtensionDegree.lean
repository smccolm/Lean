import Dubon2026.SourceCurvePicardPullback

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal-divisor
degree zero -> Galois descent. The existing actual pullback degree formula
applies to literal order divisors. Residue bijectivity is the narrower
geometric input, supplied by the finite-coordinate closed-residue theorem. -/
namespace Dubon2026.SourceCurve
noncomputable section
variable {K F E : Type*} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
variable [FiniteDimensional F E] [Algebra.IsSeparable F E]

theorem principal_degree_extension
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {f : F} {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord f)
    {D' : Divisor K E} (hD' : ∀ w : Place K E, D' w = w.ord (algebraMap F E f)) :
    Divisor.degree D' = (Module.finrank F E : ℤ) * Divisor.degree D := by
  have he : D' = Divisor.finitePullback E D := by
    ext w
    rw [hD', Divisor.finitePullback_apply, hD]
    exact w.ord_algebraMap_restrict f
  rw [he, Divisor.degree_finitePullback hF hE]

theorem principal_degree_zero_of_extension
    (hF : ∀ v : Place K F, Function.Bijective (algebraMap K v.ResidueField))
    (hE : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField))
    {f : F} {D : Divisor K F} (hD : ∀ v : Place K F, D v = v.ord f)
    {D' : Divisor K E} (hD' : ∀ w : Place K E, D' w = w.ord (algebraMap F E f))
    (hz : Divisor.degree D' = 0) : Divisor.degree D = 0 := by
  have he := principal_degree_extension hF hE hD hD'
  rw [hz] at he
  have hn : (Module.finrank F E : ℤ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := F) (M := E)).ne'
  exact (mul_eq_zero.mp he.symm).resolve_left hn

end
end Dubon2026.SourceCurve
