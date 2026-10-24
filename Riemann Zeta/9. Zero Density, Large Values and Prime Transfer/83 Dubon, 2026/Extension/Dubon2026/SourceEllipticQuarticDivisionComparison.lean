import Dubon2026.SourceEllipticQuarticModel
import Dubon2026.SourceEllipticExceptionalDivision
import Dubon2026.SourceEllipticTorsionCardinality

/-! DUB-17/18 -> reverse genus -> exceptional j-fiber census ->
non-scalar action of the actual quartic elliptic automorphism on prime
torsion. Existing actual torsion cardinality, structure, multiplication
and coordinate theorems discharge the upstream inputs.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the j=1728 fixed-vcInvFun
subgroup-count source solution. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L]

theorem quartic_division_comparison_ne_zero [IsAlgClosed L]
    (A : L) (hA : A ≠ 0) (h2 : (2 : L) ≠ 0)
    (σ : (EA A).toAffine.Point →+ (EA A).toAffine.Point)
    (hσx : ∀ (x y : L) (h : (EA A).toAffine.Nonsingular x y),
      xco (σ (Point.some x y h)) = some (-x))
    (hσ : ∀ P : (EA A).toAffine.Point, σ (σ P) = -P)
    (m : ℕ) (hm1 : 1 ≤ m) :
    (EA A).Φ (m : ℤ) + X * (EA A).ΨSq (m : ℤ) ≠ 0 := by
  haveI : (EA A).IsElliptic := isElliptic_EA A hA h2
  set F : L[X] := (EA A).Φ (m : ℤ) + X * (EA A).ΨSq (m : ℤ) with hFdef
  change F ≠ 0
  intro hF

  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (max (m ^ 2 + 2) (ringChar L + 1))
  have hqm : m ^ 2 + 1 < q := by have := le_max_left (m ^ 2 + 2) (ringChar L + 1); omega
  have hqc : ringChar L < q := by have := le_max_right (m ^ 2 + 2) (ringChar L + 1); omega
  have hqL : (q : L) ≠ 0 := by
    intro h0
    have hdvd : ringChar L ∣ q := (ringChar.spec L q).mp h0
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  haveI : Fact q.Prime := ⟨hq⟩

  have hcardq : Nat.card (Submodule.torsionBy ℤ (EA A).toAffine.Point q) = q ^ 2 := by
    have h := SourceEllipticTorsion.actual_torsion_cardinality (EA A) (K := L) hqL
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using h
  obtain ⟨x₀, y₀, h₀, hq₀⟩ : ∃ (x y : L) (h : (EA A).toAffine.Nonsingular x y), (q : ℤ) • Point.some x y h = 0 := by
    let Eq' := (Submodule.torsionBy ℤ (EA A).toAffine.Point q).toAddSubgroup
    have hq1 : 1 < q := hq.one_lt
    have h1 : 1 < Nat.card Eq' := by rw [show Nat.card Eq' = q ^ 2 from hcardq]; nlinarith
    haveI : Finite Eq' := Nat.finite_of_card_ne_zero (by rw [show Nat.card Eq' = q ^ 2 from hcardq]; positivity)
    haveI : Nontrivial Eq' := Finite.one_lt_card_iff_nontrivial.mp h1
    obtain ⟨⟨T, hT⟩, hT0⟩ := exists_ne (0 : Eq')
    rcases T with _ | ⟨x, y, h⟩
    · exact absurd rfl (fun h => hT0 (Subtype.ext h))
    · exact ⟨x, y, h, (Submodule.mem_torsionBy_iff _ _).mp hT⟩
  have hordq : addOrderOf (Point.some x₀ y₀ h₀) = q :=
    addOrderOf_eq_prime_iff.mpr ⟨by rw [← natCast_zsmul]; exact hq₀, Point.some_ne_zero h₀⟩

  have hm2q : m < q := by nlinarith
  obtain ⟨hΨ, hxq⟩ := prime_torsion_mul_coordinates (EA A) m hm1 q hq hm2q x₀ y₀ h₀ hq₀
  have hΦ : ((EA A).Φ (m : ℤ)).eval x₀ = -x₀ * ((EA A).ΨSq (m : ℤ)).eval x₀ := by
    have := congrArg (Polynomial.eval x₀) hF
    rw [hFdef, eval_zero, eval_add, eval_mul, eval_X] at this
    linear_combination this
  have hx : xco (σ (Point.some x₀ y₀ h₀)) = xco ((m : ℤ) • Point.some x₀ y₀ h₀) := by
    rw [hσx, hxq, hΦ, mul_div_assoc, div_self hΨ, mul_one]

  obtain ⟨a, ha, haT⟩ : ∃ a : ℤ, (a = m ∨ a = -m) ∧ σ (Point.some x₀ y₀ h₀) = a • Point.some x₀ y₀ h₀ := by
    rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
    · exact ⟨m, Or.inl rfl, h1⟩
    · exact ⟨-m, Or.inr rfl, by rw [h1, neg_smul]⟩

  have hkill : (a * a + 1) • Point.some x₀ y₀ h₀ = 0 := by
    have := hσ (Point.some x₀ y₀ h₀)
    rw [haT, map_zsmul, haT, smul_smul] at this
    rw [add_smul, one_smul, this, neg_add_cancel]
  have hdvd : ((q : ℕ) : ℤ) ∣ a * a + 1 := by
    rw [← hordq]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkill
  have hpos : 0 < a * a + 1 := by nlinarith
  have hle := Int.le_of_dvd hpos hdvd
  have hqm' : ((m : ℤ)) ^ 2 + 1 < q := by exact_mod_cast hqm
  rcases ha with rfl | rfl <;> nlinarith

end
end Dubon2026.SourceEllipticExceptional
