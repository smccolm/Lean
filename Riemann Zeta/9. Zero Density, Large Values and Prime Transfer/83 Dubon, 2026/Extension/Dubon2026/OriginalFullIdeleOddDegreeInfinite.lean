import Dubon2026.OriginalIdeleInfiniteH2
import Dubon2026.OriginalInfiniteOddH2

namespace Dubon2026
noncomputable section
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2

/-- Every original full-idele H2 class over an odd-degree finite Galois
extension has zero infinite coordinates. This removes any need to find a
prime-annihilated idele representative of a prime-annihilated class. -/
theorem originalFullIdeleInfiniteH2_eq_zero_of_odd_degree
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (hn : Odd (Module.finrank K L))
    (x : groupCohomology (originalFullIdeleRep K L) 2)
    (w : NumberField.InfinitePlace L) :
    originalFullIdeleInfiniteH2 K L w x = 0 := by
  letI : Fintype Gal(L/K) := Fintype.ofFinite _
  have hx := finiteSecondCohomology_card_nsmul_eq_zero (originalFullIdeleRep K L) x
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank] at hx
  let f := (originalFullIdeleInfiniteH2 K L w).hom
  have hz : Module.finrank K L • f x = 0 :=
    (map_nsmul f (Module.finrank K L) x).symm.trans ((congrArg f hx).trans (map_zero f))
  have hd := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hz)
    (addOrderOf_dvd_of_nsmul_eq_zero (originalInfiniteUnitH2_two_nsmul_zero K L w (f x)))
  rw [hn.coprime_two_right.gcd_eq_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

end
end Dubon2026
