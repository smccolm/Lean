import Dubon2026.SourceCurveRegularComparison

/-! DUB-17/18 -> regular differential dimension -> Riemann--Roch and genus.
The canonical degree is independent of the nonzero differential because
changing the differential adds a principal divisor, whose degree is zero.
The genus definition matches Def_AlgebraicCurve_CanonicalDivisor in
anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2. Its equality with the dimension of
regular differentials still requires Riemann--Roch.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_canonicalDivisorOf_eq [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω η : Ω[F⁄K]} (hω : ω ≠ 0) (hη : η ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = Divisor.degree (canonicalDivisorOf hη) := by
  obtain ⟨c, hcη⟩ := RegularDifferentialsComparison.exists_smul_eq hη ω
  have hc : c ≠ 0 := by
    intro h
    apply hω
    rw [← hcη, h, zero_smul]
  obtain ⟨P, hP, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) c hc
  have he : canonicalDivisorOf hω = P + canonicalDivisorOf hη := by
    ext v
    rw [canonicalDivisorOf_apply, Finsupp.add_apply, canonicalDivisorOf_apply, hP,
      ← hcη, v.ordDifferential_smul hc
        (RegularDifferentialsComparison.differentialCoeff_ne_zero hη v)]
  rw [he, map_add, hdeg, zero_add]

/-- The source genus defined by the degree of an actual canonical divisor. -/
def genus (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0
  then (Divisor.degree (canonicalDivisorOf h.choose_spec) + 2).toNat / 2
  else 0

theorem genus_eq_canonical_degree [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    genus K F = (Divisor.degree (canonicalDivisorOf hω) + 2).toNat / 2 := by
  have hex : ∃ η : Ω[F⁄K], η ≠ 0 := ⟨ω, hω⟩
  rw [genus, dif_pos hex, degree_canonicalDivisorOf_eq hex.choose_spec hω]

end
end Dubon2026.SourceCurve
