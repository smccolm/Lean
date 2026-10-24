import Dubon2026.SourceEllipticCubicModel
import Dubon2026.SourceEllipticExceptionalDivision
import Dubon2026.SourceEllipticTorsionCardinality

/-! DUB-17/18 -> reverse genus -> exceptional j=0 census ->
non-scalar action of the actual cubic elliptic automorphism on prime
torsion. Reuse the already proved multiplication fraction, prime-torsion
scalar lemma, optional coordinates, actual torsion cardinality and basis.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, the j=0 fixed-vcInvFun
subgroup-count source solution. -/
namespace Dubon2026.SourceEllipticExceptional
open WeierstrassCurve WeierstrassCurve.Affine Polynomial
noncomputable section
variable {L : Type*} [Field L] [DecidableEq L]

theorem cubic_division_comparison_ne_zero [IsAlgClosed L]
    (B : L) (hB : B ≠ 0) (u : Lˣ) (h2 : (2 : L) ≠ 0) (h3 : (3 : L) ≠ 0)
    (σ : (EB B).toAffine.Point →+ (EB B).toAffine.Point)
    (hσx : ∀ (x y : L) (h : (EB B).toAffine.Nonsingular x y),
      xco (σ (Point.some x y h)) = some ((u : L) * x))
    (hσ : ∀ P : (EB B).toAffine.Point, σ (σ P) + σ P + P = 0)
    (m : ℕ) (hm1 : 1 ≤ m) :
    (EB B).Φ (m : ℤ) - C (u : L) * X * (EB B).ΨSq (m : ℤ) ≠ 0 := by
  haveI : (EB B).IsElliptic := isElliptic_EB B hB h2 h3
  set F : L[X] := (EB B).Φ (m : ℤ) - C (u : L) * X * (EB B).ΨSq (m : ℤ) with hFdef
  change F ≠ 0
  intro hF

  obtain ⟨q, hqge, hq⟩ := Nat.exists_infinite_primes (max (m ^ 2 + m + 2) (ringChar L + 1))
  have hqm : m ^ 2 + m + 1 < q := by have := le_max_left (m ^ 2 + m + 2) (ringChar L + 1); omega
  have hqc : ringChar L < q := by have := le_max_right (m ^ 2 + m + 2) (ringChar L + 1); omega
  have hqL : (q : L) ≠ 0 := by
    intro h0
    have hdvd : ringChar L ∣ q := (ringChar.spec L q).mp h0
    rcases (Nat.dvd_prime hq).mp hdvd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · omega
  haveI : Fact q.Prime := ⟨hq⟩

  have hcardq : Nat.card (Submodule.torsionBy ℤ (EB B).toAffine.Point q) = q ^ 2 := by
    have h := SourceEllipticTorsion.actual_torsion_cardinality (EB B) (K := L) hqL
    simpa only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id] using h
  obtain ⟨x₀, y₀, h₀, hq₀⟩ : ∃ (x y : L) (h : (EB B).toAffine.Nonsingular x y), (q : ℤ) • Point.some x y h = 0 := by
    let Eq' := (Submodule.torsionBy ℤ (EB B).toAffine.Point q).toAddSubgroup
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

  obtain ⟨hΨ, hxq⟩ := prime_torsion_mul_coordinates (EB B) m hm1 q hq (by nlinarith) x₀ y₀ h₀ hq₀
  have hΦ : ((EB B).Φ (m : ℤ)).eval x₀ = (u : L) * x₀ * ((EB B).ΨSq (m : ℤ)).eval x₀ := by
    have := congrArg (Polynomial.eval x₀) hF
    rw [hFdef, eval_zero, eval_sub, eval_mul, eval_mul, eval_C, eval_X] at this
    linear_combination this
  have hx : xco (σ (Point.some x₀ y₀ h₀)) = xco ((m : ℤ) • Point.some x₀ y₀ h₀) := by
    rw [hσx, hxq, hΦ, mul_div_assoc, div_self hΨ, mul_one]

  obtain ⟨a, ha, haT⟩ : ∃ a : ℤ, (a = m ∨ a = -m) ∧ σ (Point.some x₀ y₀ h₀) = a • Point.some x₀ y₀ h₀ := by
    rcases eq_or_eq_neg_of_xco_eq hx with h1 | h1
    · exact ⟨m, Or.inl rfl, h1⟩
    · exact ⟨-m, Or.inr rfl, by rw [h1, neg_smul]⟩

  have hkill : (a * a + a + 1) • Point.some x₀ y₀ h₀ = 0 := by
    have := hσ (Point.some x₀ y₀ h₀)
    rw [haT, map_zsmul, haT, smul_smul] at this
    rwa [add_smul, add_smul, one_smul]
  have hdvd : ((q : ℕ) : ℤ) ∣ a * a + a + 1 := by
    rw [← hordq]; exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hkill
  have hpos : 0 < a * a + a + 1 := by nlinarith
  have hle := Int.le_of_dvd hpos hdvd
  have hqm' : ((m : ℤ)) ^ 2 + m + 1 < q := by exact_mod_cast hqm
  rcases ha with rfl | rfl <;> nlinarith

end
end Dubon2026.SourceEllipticExceptional
