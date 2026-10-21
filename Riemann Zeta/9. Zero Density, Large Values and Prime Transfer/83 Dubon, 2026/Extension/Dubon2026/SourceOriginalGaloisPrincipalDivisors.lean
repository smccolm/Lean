import Dubon2026.SourceOriginalGaloisCoordinates
import Dubon2026.SourceCurveFiniteSupport
import Dubon2026.SourceCurvePrincipalDegree
import Dubon2026.SourceCurveDivisors

/-! DUB-17/18 -> global residue identity -> rational-coordinate vanishing
in the actual finite Galois closure. The existing finite-coordinate product
formula supplies the principal-divisor input needed by logarithmic residues.
Only principal divisors needed for that residue argument are constructed;
no separate Riemann--Roch theory of the auxiliary field is required here.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

theorem finite_originalGaloisClosure_places_positive (f : originalGaloisClosure N L) :
    {v : Place L (originalGaloisClosure N L) | 0 < v.ord f}.Finite := by
  classical
  by_cases ht : Transcendental L f
  · haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    haveI := finite_originalGaloisClosure_over_transcendental N L ht
    exact finite_places_positive_of_finite_coordinate f ht
  · have ha : IsAlgebraic L f := not_not.mp ht
    have he : {v : Place L (originalGaloisClosure N L) | 0 < v.ord f} = ∅ := by
      ext v
      simp [v.ord_eq_zero_of_isAlgebraic ha]
    rw [he]
    exact Set.finite_empty

theorem finite_originalGaloisClosure_divisor_support (f : originalGaloisClosure N L) :
    {v : Place L (originalGaloisClosure N L) | v.ord f ≠ 0}.Finite := by
  refine ((finite_originalGaloisClosure_places_positive N L f).union
    (finite_originalGaloisClosure_places_positive N L f⁻¹)).subset ?_
  intro v hv
  change 0 < v.ord f ∨ 0 < v.ord f⁻¹
  rw [v.ord_inv]
  change v.ord f ≠ 0 at hv
  omega

theorem sum_originalGaloisClosure_orders_eq_zero (f : originalGaloisClosure N L) :
    (∑ᶠ v : Place L (originalGaloisClosure N L),
      v.ord f * (Module.finrank L v.ResidueField : ℤ)) = 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  exact sum_orders_eq_zero_of_finite_coordinates
    (fun _ ht => finite_originalGaloisClosure_over_transcendental N L ht)
    f (finite_originalGaloisClosure_divisor_support N L f)

theorem hasPrincipalDivisors_originalGaloisClosure :
    HasPrincipalDivisors L (originalGaloisClosure N L) := by
  refine ⟨fun f _ => ?_⟩
  let E : Divisor L (originalGaloisClosure N L) :=
    Finsupp.ofSupportFinite (fun v => v.ord f) (finite_originalGaloisClosure_divisor_support N L f)
  refine ⟨E, fun _ => rfl, ?_⟩
  rw [Divisor.degree_eq_finsum]
  exact sum_originalGaloisClosure_orders_eq_zero N L f

end
end Dubon2026.SourceFunctionField
