import Dubon2026.SourceOriginalWeilTorsionValues
import Dubon2026.SourceOriginalPicardGroup

/-! DUB-17/18 -> original Weil pairing descent. Principal degree zero
forces both divisors of nonzero-order torsion data to have degree zero.
Their classes lie in the existing actual Picard torsion subgroup. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilDatum
noncomputable section
open SourceCurve
variable {N : ℕ} [NeZero N] {L : Type*} [Field L] [Algebra ℚ L]
variable {n : ℕ} [NeZero n] (d : OriginalWeilDatum N L n)

theorem degree_first : Divisor.degree d.D₁ = 0 := by
  have h := degree_originalPrincipalDivisor N L d.f₁
  rw [d.principalDivisor_first, map_nsmul, nsmul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast (NeZero.ne n))

theorem degree_second : Divisor.degree d.D₂ = 0 := d.symm.degree_first

/-- The actual first degree-zero divisor class, as an n-torsion element. -/
def classLeft : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n :=
  ⟨Pic0.mk ⟨d.D₁, d.degree_first⟩, (Pic0.mk_mem_torsion_iff _ n).mpr
    ⟨d.f₁, d.f₁_ne_zero, fun v => by
      rw [Finsupp.smul_apply, nsmul_eq_mul, d.ord_f₁]⟩⟩

/-- The actual second degree-zero divisor class, as an n-torsion element. -/
def classRight : Pic0.torsion (K := L) (F := modularFunctionFieldOver N L) n :=
  ⟨Pic0.mk ⟨d.D₂, d.degree_second⟩, (Pic0.mk_mem_torsion_iff _ n).mpr
    ⟨d.f₂, d.f₂_ne_zero, fun v => by
      rw [Finsupp.smul_apply, nsmul_eq_mul, d.ord_f₂]⟩⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilDatum
