import Dubon2026.RationalPrimeOriginalResidueCard
import Dubon2026.LocalFieldFrobeniusFieldRoots

/-! # Original rational-prime arithmetic Frobenius on prime-to-p roots

The original completion residue cardinality is p. Nondivisibility by p
gives an actual integer unit, whose image remains a unit in the extension
integer ring. Thus neither the residue characteristic condition nor an
integer representative remains an assumption for the unramified root
formula needed in DUB-17's cyclotomic principal product.
-/
namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (p : ℕ) (hp : p.Prime) (L : Type) [Field L]
  [Algebra (rationalPrimeLocalField p hp) L] [IsGalois (rationalPrimeLocalField p hp) L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[rationalPrimeLocalField p hp] 𝒪[L]]

/-- Original arithmetic Frobenius over the actual rational p-completion acts by pth power on every original field root whose order is prime to p. -/
theorem rationalPrimeArithmeticFrobenius_field_root {n : ℕ}
    (hpn : ¬p ∣ n) (ζ : L) (hζ : ζ ^ n = 1) :
    localFieldArithmeticFrobenius (rationalPrimeLocalField p hp) L ζ = ζ ^ p := by
  have hu : IsUnit (n : 𝒪[rationalPrimeLocalField p hp]) := by
    have h := rationalPrimeValuationInteger_isUnit_int p hp (n : ℤ)
      (by exact_mod_cast hpn)
    simpa only [Int.cast_natCast] using h
  have hv : IsUnit (n : 𝒪[L]) := by
    simpa only [map_natCast] using hu.map (algebraMap 𝒪[rationalPrimeLocalField p hp] 𝒪[L])
  have hn : (n : 𝓀[L]) ≠ 0 := by
    simpa only [map_natCast] using (IsLocalRing.residue_ne_zero_iff_isUnit (n : 𝒪[L])).mpr hv
  have hf := localFieldArithmeticFrobenius_field_root (rationalPrimeLocalField p hp) L hn ζ hζ
  rwa [rationalPrimeLocalField_residue_card] at hf

end
end Dubon2026
