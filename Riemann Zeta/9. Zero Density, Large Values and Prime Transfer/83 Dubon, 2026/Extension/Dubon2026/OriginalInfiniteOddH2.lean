import Dubon2026.OriginalGlobalInfiniteH2
import Dubon2026.FaithfulComplexFieldAction
import Dubon2026.FiniteSecondCohomologySylowDetection

/-! # Odd torsion vanishes at the actual original infinite places

Faithful original completion transports embed the infinite decomposition
group into the real/complex Galois group, or make it trivial in the real
case. Its order divides two. The proved undivided cocycle-sum annihilation
then kills odd-primary local H2. This discharges DUB-17's real-place
obligation for the odd auxiliary-prime branch; it makes no finite-prime
zero-sum assertion at the prime two.
-/
namespace Dubon2026
noncomputable section
open NumberField
open scoped NumberField
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  (w : InfinitePlace L)

/-- The actual original infinite decomposition group has order dividing two. -/
theorem originalInfiniteDecomposition_card_dvd_two :
    Nat.card (OriginalInfiniteDecompositionGroup K L w) ∣ 2 := by
  let G := OriginalInfiniteDecompositionGroup K L w
  letI := originalInfiniteDecompositionAction K L w
  letI := originalInfiniteDecompositionAction_faithful K L w
  rcases w.isReal_or_isComplex with hw | hw
  · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
    letI : Subsingleton G := faithfulRealField_subsingleton G w.Completion e
    simp only [Nat.card_unique, one_dvd]
  · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
    have hc (σ : G) : Continuous (fun z : ℂ => e (σ • e.symm z)) :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).continuous.comp
        ((numberFieldGaloisArchimedeanTransport_continuous K L σ.val w w σ.property).comp
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous)
    have h := Subgroup.card_dvd_of_injective (faithfulComplexActionHom G w.Completion e hc)
      (faithfulComplexActionHom_injective G w.Completion e hc)
    letI : Algebra.IsQuadraticExtension ℝ ℂ := ⟨Complex.finrank_real_complex⟩
    rw [IsGalois.card_aut_eq_finrank, Complex.finrank_real_complex] at h
    exact h

variable [FiniteDimensional K L]

/-- Twice every actual original infinite-place unit H2 class is zero. -/
theorem originalInfiniteUnitH2_two_nsmul_zero
    (x : groupCohomology (originalInfiniteUnitRep K L w) 2) : (2 : ℕ) • x = 0 := by
  letI : Fintype (OriginalInfiniteDecompositionGroup K L w) := Fintype.ofFinite _
  have hx := finiteSecondCohomology_card_nsmul_eq_zero (originalInfiniteUnitRep K L w) x
  rw [← Nat.card_eq_fintype_card] at hx
  obtain ⟨m, hm⟩ := originalInfiniteDecomposition_card_dvd_two K L w
  calc
    (2 : ℕ) • x = (Nat.card (OriginalInfiniteDecompositionGroup K L w) * m) • x :=
      congrArg (fun n : ℕ => n • x) hm
    _ = 0 := by rw [mul_nsmul, hx, smul_zero]

/-- Every odd-prime-torsion class at an actual original infinite completion vanishes. -/
theorem originalInfiniteUnitH2_eq_zero_of_odd_torsion
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x : groupCohomology (originalInfiniteUnitRep K L w) 2) (hx : q • x = 0) : x = 0 := by
  have hcop : q.Coprime 2 := hq.coprime_iff_not_dvd.mpr
    (fun h => hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h))
  have hd := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hx)
    (addOrderOf_dvd_of_nsmul_eq_zero (originalInfiniteUnitH2_two_nsmul_zero K L w x))
  rw [hcop.gcd_eq_one] at hd
  exact AddMonoid.addOrderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)

/-- An odd-prime-torsion original global class has zero actual infinite-place localization. -/
theorem originalGlobalInfiniteH2_eq_zero_of_odd_torsion
    (q : ℕ) (hq : q.Prime) (hq2 : q ≠ 2)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) (hx : q • x = 0) :
    originalGlobalInfiniteH2 K L w x = 0 := by
  apply originalInfiniteUnitH2_eq_zero_of_odd_torsion K L w q hq hq2
  rw [← map_nsmul, hx, map_zero]

end
end Dubon2026
