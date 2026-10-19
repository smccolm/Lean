import Dubon2026.RationalPrimeTameCoefficientQuotient
import Dubon2026.ArtinianResidualMatrixPGroup

/-! Actual residual-trivial Artinian matrices kill the prime-to-coefficient
part of the cyclotomic group. This descends the fixed inertia action to the
precise coefficient-primary quotient used by the auxiliary local rings on
the Dubon Theorem 2.6 dependency chain. -/

namespace Dubon2026
noncomputable section
open Matrix

/-- The fixed coefficient-primary quotient carries the unique factor of
an actual residual-trivial Artinian cyclotomic action. -/
theorem artinian_cyclotomic_unique_primary_factor
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    {A ι : Type} [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    [CharP (IsLocalRing.ResidueField A) q] [Fintype ι] [DecidableEq ι]
    (θ : (ZMod p)ˣ →* GeneralLinearGroup ι A)
    (hres : ∀ u, GeneralLinearGroup.map (IsLocalRing.residue A) (θ u) = 1) :
    ∃! η : RationalPrimeTameCoefficientQuotient p q →* GeneralLinearGroup ι A,
      η.comp (QuotientGroup.mk' (rationalPrimeTameCoefficientKernel p q)) = θ := by
  let N := rationalPrimeTameCoefficientKernel p q
  have hker : N ≤ θ.ker := by
    intro x hx
    let v : (GeneralLinearGroup.map (n := ι) (IsLocalRing.residue A)).ker := ⟨θ x, hres x⟩
    obtain ⟨m, hm⟩ := artinianResidualMatrixKernel_isPGroup (ι := ι) (A := A)
      q (Fact.out : q.Prime) v
    have hqm : θ x ^ (q ^ m) = 1 := congrArg Subtype.val hm
    have hN : θ x ^ Nat.card N = 1 := by
      have h := congrArg (fun y : N => θ y.val) (pow_card_eq_one' (x := (⟨x, hx⟩ : N)))
      simpa only [Subgroup.coe_pow, OneMemClass.coe_one, map_pow, map_one] using h
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes
      ((rationalPrimeTameCoefficientKernel_coprime p q).pow_left m)
      (orderOf_dvd_of_pow_eq_one hqm) (orderOf_dvd_of_pow_eq_one hN)
  let η := QuotientGroup.lift N θ hker
  refine ⟨η, rfl, ?_⟩
  intro η' hη'
  apply MonoidHom.ext
  intro u
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N u
  exact DFunLike.congr_fun hη' x

end
end Dubon2026
