import Dubon2026.SourceGammaOneCoverHeckeSquare
import Dubon2026.SourceGammaOneCoverHeckeTraceCosets
import Dubon2026.SourceGammaOneConstantH1Realization
import Dubon2026.SourceCohomologyTracePullbackCoefficients

/-! DUB-17/18 -> original all-weight adic association -> actual Gamma1
surjective-transfer Hecke compatibility -> identify the original Gamma1
upper subgroup with the exact subgroup occurring in trace base change.
Use the literal cover matrix and good-prime invertibility. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup

/-- At a coprime index, the cover's literal upper-right entry shows that
membership in the two original Hecke upper subgroups is equivalent. -/
theorem sourceGammaOneDiagonalHom_heckeUpper_iff
    (Q N n : ℕ) [NeZero N] (hcop : Nat.Coprime n N)
    (g : Gamma1 (Q * N ^ 2)) :
    sourceGammaOneDiagonalHom Q N g ∈ heckeUpperSubgroup Q n ↔
      g ∈ sourceGammaOneHeckeUpper (Q * N ^ 2) n := by
  change (((N : ℤ) * g.val 0 1 : ℤ) : ZMod n) = 0 ↔ (g.val 0 1 : ZMod n) = 0
  rw [Int.cast_mul, Int.cast_natCast]
  exact IsUnit.mul_right_eq_zero ((ZMod.isUnit_iff_coprime N n).mpr hcop.symm)

/-- Restricting the already injective literal cover retains injectivity
on the genuine upper correspondence subgroup. -/
theorem sourceGammaOneCoverHeckeUpperHom_injective (Q N n : ℕ) [NeZero N] :
    Function.Injective (sourceGammaOneCoverHeckeUpperHom Q N n) := by
  intro a b h
  apply Subtype.ext
  exact sourceGammaOneDiagonalHom_injective Q N (congrArg Subtype.val h)

/-- The actual upper-subgroup cover has exactly the required image
inside the original upper group; no representative lift is assumed. -/
theorem sourceGammaOneCoverHeckeUpperHom_range
    (Q N n : ℕ) [NeZero N] (hcop : Nat.Coprime n N) :
    (sourceGammaOneCoverHeckeUpperHom Q N n).range =
      (sourceGammaOneDiagonalHom Q N).range.comap (heckeUpperSubgroup Q n).subtype := by
  ext u
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.val, rfl⟩
  · rintro ⟨g, hg⟩
    have hm : g ∈ sourceGammaOneHeckeUpper (Q * N ^ 2) n :=
      (sourceGammaOneDiagonalHom_heckeUpper_iff Q N n hcop g).mp
        (hg.symm ▸ u.property)
    refine ⟨⟨g, hm⟩, ?_⟩
    apply Subtype.ext
    exact hg

/-- The original Gamma1 upper subgroup is isomorphic to the exact
subgroup pulled back by the original good-prime Hecke conjugation. -/
def sourceGammaOneCoverHeckeUpperEquiv
    (Q N ell : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N)) :
    sourceGammaOneHeckeUpper (Q * N ^ 2) ell ≃*
      (sourceGammaOneDiagonalHom Q N).range.comap (sourceHeckeConjugation hell) :=
  (MulEquiv.ofBijective (sourceGammaOneCoverHeckeUpperHom Q N ell).rangeRestrict
    ⟨fun _ _ h => sourceGammaOneCoverHeckeUpperHom_injective Q N ell (congrArg Subtype.val h),
      (sourceGammaOneCoverHeckeUpperHom Q N ell).rangeRestrict_surjective⟩).trans
    (MulEquiv.subgroupCongr
      ((sourceGammaOneCoverHeckeUpperHom_range Q N ell
        (hcop.of_dvd_right (dvd_mul_left N Q))).trans
        (sourceGammaOneCoverHeckeTraceSubgroup_eq Q N ell hell hcop).symm))

/-- The group isomorphism keeps the exact original upper-subgroup map. -/
theorem sourceGammaOneCoverHeckeUpperEquiv_apply
    (Q N ell : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N))
    (g : sourceGammaOneHeckeUpper (Q * N ^ 2) ell) :
    (sourceGammaOneCoverHeckeUpperEquiv Q N ell hell hcop g).val =
      sourceGammaOneCoverHeckeUpperHom Q N ell g := rfl

/-- Under the proved subgroup isomorphism, the actual pullback map is
the original Gamma1 Hecke conjugation followed by its actual range isomorphism. -/
theorem sourceGammaOneCoverHeckeUpperEquiv_conjugation
    (Q N ell : ℕ) [NeZero N] [NeZero ell] (hell : ell.Prime)
    (hcop : Nat.Coprime ell (Q * N))
    (g : sourceGammaOneHeckeUpper (Q * N ^ 2) ell) :
    sourceTracePullbackSubgroupHom (sourceHeckeConjugation hell)
      (sourceGammaOneDiagonalHom Q N).range
      (sourceGammaOneCoverHeckeUpperEquiv Q N ell hell hcop g) =
    sourceGammaOneRangeEquiv Q N (sourceGammaOneHeckeConjugation (Q * N ^ 2) ell g) := by
  apply Subtype.ext
  change sourceHeckeConjugation hell (sourceGammaOneCoverHeckeUpperHom Q N ell g) =
    sourceGammaOneDiagonalHom Q N (sourceGammaOneHeckeConjugation (Q * N ^ 2) ell g)
  rw [← sourceIntegralHeckeConjugate_eq_prime]
  exact (sourceGammaOneCoverHecke_square Q N ell g).symm

end
end Dubon2026
