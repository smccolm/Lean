import Dubon2026.OriginalCyclotomicLocalDegreeStage
import Dubon2026.UnramifiedUnionFiniteFieldCriterion
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-! # Cyclotomic stages supply the required enlarged-degree divisibility

The norm-root enlargement needs the coefficient prime to divide its
relative degree. The existing primitive-root stage and unramified-root
theorems give arbitrarily high prime-power divisibility of the absolute
degree. The pinned cyclotomic degree formula supplies this condition
without a primary-degree bound on the final Galois closure.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
variable (Ω : Type) [Field Ω] [CharZero Ω] [Algebra ℚ Ω] [IsSepClosed Ω]

/-- An actual stage in the original arithmetic union has absolute
degree divisible by any prescribed power of an exceptional prime. -/
theorem originalCyclotomic_exists_norm_degree_stage
    (a : 𝓞 ℚ) (ha : a ≠ 0) (p : ℕ) (hp : p.Prime)
    (hpa : (p : 𝓞 ℚ) ∣ a) (d : ℕ) :
    ∃ P : OriginalUnramifiedGaloisStage (Ω := Ω) a,
      letI : Algebra ℚ P.val := P.val.algebra'
      p ^ d ∣ Module.finrank ℚ P.val := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ (d + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (p ^ (d + 1))
  let F := originalPrimitiveRootStage ℚ Ω hζ
  letI : Algebra ℚ F := F.algebra'
  have hF : F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a := by
    change IntermediateField.adjoin ℚ ({ζ} : Set Ω) ≤ _
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact originalQUnramifiedUnion_mem_of_powerRoot a p (d + 1) hpa ζ hζ
  have hUnram := originalUnramifiedUnion_ambient_finite_ramification a ha
    F.toIntermediateField hF
  refine ⟨⟨F, hUnram⟩, ?_⟩
  letI : IsCyclotomicExtension {p ^ (d + 1)} ℚ F :=
    originalPrimitiveRootStage_isCyclotomic ℚ Ω hζ
  rw [IsCyclotomicExtension.finrank F
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos (p ^ (d + 1)))),
    Nat.totient_prime_pow hp (Nat.succ_pos d), Nat.succ_sub_one]
  exact dvd_mul_right _ _

/-- A sufficiently large prime-power divisor of the absolute degree
forces the prime to divide the relative degree in the actual tower. -/
theorem originalRelativeDegree_prime_dvd_of_absolute_power
    (p d n : ℕ) (hp : p.Prime) (hd : 0 < d)
    (h : p ^ d ∣ d * n) : p ∣ n := by
  by_contra hn
  have hc : (p ^ d).Coprime n := (hp.coprime_iff_not_dvd.mpr hn).pow_left d
  have hpd : p ^ d ∣ d := hc.dvd_of_dvd_mul_right h
  exact (Nat.lt_pow_self hp.one_lt : d < p ^ d).not_ge (Nat.le_of_dvd hd hpd)

end
end Dubon2026
