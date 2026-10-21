import Dubon2026.SourceModularJTranscendence
import Dubon2026.SourcePrimeConjugatePolynomial
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! DUB-17/18 -> numerical modular genus -> exact j-map degree ->
prime lower bound. The literal q-substituted j series cannot be a polynomial
in j: its root-of-unity orbit would force a positive j coefficient to vanish.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.lean.
Only the coefficient obstruction is selected; field integrality is supplied
by the already proved actual monic relation, without an irreducibility input.
-/
namespace Dubon2026.SourceFunctionField.PrimeDegreeAux
noncomputable section
variable {K : Type*} [Field K]

/-- The original j series after a unit twist and a positive power substitution. -/
def TS (K : Type*) [Field K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K :=
  qExpand K e (qTwist u (jqModC K))

theorem TS_coeff_mul (e : ℕ) [NeZero e] (u : Kˣ) (n : ℤ) :
    (TS K e u).coeff ((e : ℤ) * n) = ((u ^ n : Kˣ) : K) * (jqModC K).coeff n := by
  rw [TS, qExpand_coeff_mul, qTwist_coeff]

theorem TS_coeff_of_not_dvd (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : ¬ (e : ℤ) ∣ k) :
    (TS K e u).coeff k = 0 := by
  exact qExpand_coeff_of_not_dvd (R := K) (N := e) _ hk

theorem coeff_jqModC_of_lt {n : ℤ} (hn : n < -1) : (jqModC K).coeff n = 0 := by
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [Dubon2026.SourceFunctionField.order_jqModC]
  exact hn

theorem TS_coeff_neg (e : ℕ) [NeZero e] (u : Kˣ) : (TS K e u).coeff (-(e : ℤ)) = ((u⁻¹ : Kˣ) : K) := by
  have h := TS_coeff_mul (K := K) e u (-1)
  rw [mul_neg_one] at h
  rw [h, Dubon2026.SourceFunctionField.coeff_jqModC_neg_one, mul_one, zpow_neg_one]

theorem TS_coeff_of_lt (e : ℕ) [NeZero e] (u : Kˣ) {k : ℤ} (hk : k < -(e : ℤ)) : (TS K e u).coeff k = 0 := by
  by_cases hd : (e : ℤ) ∣ k
  · obtain ⟨n, rfl⟩ := hd
    have he : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
    have hn : n < -1 := by
      by_contra hcon
      push Not at hcon
      have : -(e : ℤ) ≤ (e : ℤ) * n := by nlinarith
      exact absurd hk (not_lt.mpr this)
    rw [TS_coeff_mul, coeff_jqModC_of_lt hn, mul_zero]
  · exact TS_coeff_of_not_dvd e u hd

theorem TS_ne_zero (e : ℕ) [NeZero e] (u : Kˣ) : TS K e u ≠ 0 := by
  intro h
  have := TS_coeff_neg (K := K) e u
  rw [h, HahnSeries.coeff_zero] at this
  exact (u⁻¹).ne_zero this.symm

theorem TS_injective {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ} (h : TS K e u = TS K e' u') :
    e = e' ∧ u = u' := by
  have key : ∀ {a a' : ℕ} [NeZero a] [NeZero a'] {v v' : Kˣ}, TS K a v = TS K a' v' → a ≤ a' := by
    intro a a' _ _ v v' hh
    by_contra hlt
    push Not at hlt
    have h1 := TS_coeff_neg (K := K) a v
    have hlt' : (-(a : ℤ)) < -(a' : ℤ) := by
      have : (a' : ℤ) < a := by exact_mod_cast hlt
      omega
    have h2 : (TS K a' v').coeff (-(a : ℤ)) = 0 := TS_coeff_of_lt a' v' hlt'
    rw [← hh, h1] at h2
    exact (v⁻¹).ne_zero h2
  have hee : e = e' := le_antisymm (key h) (key h.symm)
  subst hee
  refine ⟨rfl, ?_⟩
  have h1 := TS_coeff_neg (K := K) e u
  rw [h, TS_coeff_neg] at h1
  exact (inv_injective (Units.val_injective h1)).symm

theorem jqModC_eq_TS : jqModC K = TS K 1 1 := by
  rw [TS, qTwist_one_apply, qExpand_one_apply]

theorem jqNModC_eq_TS (d : ℕ) [NeZero d] : jqNModC K d = TS K d 1 := by
  rw [jqNModC, TS, qTwist_one_apply]

theorem qTwist_qExpand_of_pow_eq_one (A : ℕ) [NeZero A] (v : Kˣ) (hv : v ^ A = 1) (x : LaurentSeries K) :
    qTwist v (qExpand K A x) = qExpand K A x := by
  rw [qTwist_qExpand]
  have : v ^ (A : ℤ) = 1 := by exact_mod_cast hv
  rw [this, qTwist_one_apply]
theorem units_pow_eq_one_of_isPrimitiveRoot {N : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N) : ζ ^ N = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one])

end
end Dubon2026.SourceFunctionField.PrimeDegreeAux
