import Dubon2026.SourceCuspRationalCoordinates

/-! DUB-17/18 -> parabolic Hecke realization -> matching period dimensions
-> exact arithmetic genus bound -> count of original rational cusp orbits.
Selected from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
Definitions/Def_ModularCurve_CuspSpace.lean.
The quotient and its level action are the previously proved SourceManin
objects. Cusp widths and unrelated geometric infrastructure are omitted.
-/
namespace Dubon2026.SourceManin
noncomputable section
open Matrix Matrix.SpecialLinearGroup OnePoint CongruenceSubgroup
open scoped MatrixGroups

namespace CuspSpace
variable (N : ℕ)

/-- The gcd of the reduced rational-cusp denominator with the original level. -/
def cuspDenomAux (x : OnePoint ℚ) : ℕ :=
  x.elim N fun q => Nat.gcd q.den N

@[simp] lemma cuspDenomAux_infty : cuspDenomAux N ∞ = N := rfl

@[simp] lemma cuspDenomAux_coe (q : ℚ) : cuspDenomAux N (q : OnePoint ℚ) = Nat.gcd q.den N :=
  rfl

variable {N}

lemma cuspDenomAux_ratPoint {a c : ℤ} (h : IsCoprime a c) :
    cuspDenomAux N (ratPoint a c) = Int.gcd c N := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Int.gcd]
  · rw [ratPoint_of_ne_zero _ hc, cuspDenomAux_coe]
    have hcop : Nat.Coprime a.natAbs c.natAbs := Int.isCoprime_iff_gcd_eq_one.mp h
    have hden : (((a : ℚ) / (c : ℚ)).den : ℤ) = (c.natAbs : ℤ) := by
      rcases lt_or_gt_of_ne hc with hneg | hpos
      · have : ((a : ℚ) / (c : ℚ)) = (((-a : ℤ) : ℚ) / ((-c : ℤ) : ℚ)) := by
          push_cast; rw [neg_div_neg_eq]
        rw [this, Rat.den_div_eq_of_coprime (by omega) (by simpa using hcop)]
        omega
      · rw [Rat.den_div_eq_of_coprime hpos hcop]
        omega
    have : ((a : ℚ) / (c : ℚ)).den = c.natAbs := by exact_mod_cast hden
    rw [this]
    rfl

lemma gamma0_mem_iff_dvd {N : ℕ} {γ : SL(2, ℤ)} :
    γ ∈ Gamma0 N ↔ (N : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma cuspDenomAux_dvd_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (x : OnePoint ℚ) :
    cuspDenomAux N x ∣ cuspDenomAux N (mapGL ℚ γ • x) := by
  obtain ⟨a, c, hac, rfl⟩ := exists_ratPoint_eq x
  have hac' : a ≠ 0 ∨ c ≠ 0 := hac.ne_zero_or_ne_zero
  rw [mapGL_smul_ratPoint γ hac', cuspDenomAux_ratPoint hac,
    cuspDenomAux_ratPoint (isCoprime_smul_pair γ hac)]

  have h1 : (Int.gcd c N : ℤ) ∣ γ 1 0 * a + γ 1 1 * c := by
    refine dvd_add (Dvd.dvd.mul_right ?_ a) (Dvd.dvd.mul_left (Int.gcd_dvd_left ..) _)
    exact (Int.gcd_dvd_right ..).trans (gamma0_mem_iff_dvd.mp hγ)
  exact Int.dvd_gcd h1 (Int.gcd_dvd_right ..)

lemma cuspDenomAux_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) (x : OnePoint ℚ) :
    cuspDenomAux N (mapGL ℚ γ • x) = cuspDenomAux N x := by
  refine Nat.dvd_antisymm ?_ (cuspDenomAux_dvd_smul hγ x)
  have := cuspDenomAux_dvd_smul (inv_mem hγ) (mapGL ℚ γ • x)
  rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at this

variable (N)

/-- The denominator invariant descended to actual level cusp orbits. -/
def cuspDenom : CuspSpace N → ℕ :=
  Quotient.lift (cuspDenomAux N) (by
    rintro x y ⟨⟨g, γ, hγ, rfl⟩, rfl⟩
    exact cuspDenomAux_smul hγ y)

@[simp] lemma cuspDenom_mk (x : OnePoint ℚ) : cuspDenom N (mk N x) = cuspDenomAux N x := rfl

variable {N}

lemma cuspDenom_mk_ratPoint {a c : ℤ} (h : IsCoprime a c) :
    cuspDenom N (mk N (ratPoint a c)) = Int.gcd c N :=
  cuspDenomAux_ratPoint h

@[simp] lemma cuspDenom_mk_infty : cuspDenom N (mk N ∞) = N := rfl

lemma cuspDenom_dvd (x : CuspSpace N) : cuspDenom N x ∣ N := by
  obtain ⟨y, rfl⟩ := mk_surjective N x
  obtain ⟨a, c, hac, rfl⟩ := exists_ratPoint_eq y
  rw [cuspDenom_mk_ratPoint hac]
  simpa using Int.gcd_dvd_natAbs_right c (N : ℤ)

lemma cuspDenom_pos [NeZero N] (x : CuspSpace N) : 0 < cuspDenom N x :=
  Nat.pos_of_dvd_of_pos (cuspDenom_dvd x) (Nat.pos_of_ne_zero (NeZero.ne N))

lemma cuspDenom_mk_ratPoint_one_dvd {e : ℕ} (he : e ∣ N) :
    cuspDenom N (mk N (ratPoint 1 e)) = e := by
  rw [cuspDenom_mk_ratPoint isCoprime_one_left, Int.gcd_natCast_natCast, Nat.gcd_eq_left he]

/-- The explicit equivalence criterion for normalized original cusp representatives. -/
def NormalFormCriterion (N : ℕ) : Prop :=
  ∀ (a a' : ℤ) (e : ℕ), e ∣ N → IsCoprime a (e : ℤ) → IsCoprime a' (e : ℤ) →
    (mk N (ratPoint a e) = mk N (ratPoint a' e) ↔
      (a : ZMod (Nat.gcd e (N / e))) = (a' : ZMod (Nat.gcd e (N / e))))

/-- The precise divisor-and-unit classification statement, proved downstream. -/
def Classification (N : ℕ) : Prop :=
  Nonempty (CuspSpace N ≃ (d : N.divisors) × (ZMod (Nat.gcd d (N / (d : ℕ))))ˣ)

end CuspSpace

end
end Dubon2026.SourceManin
