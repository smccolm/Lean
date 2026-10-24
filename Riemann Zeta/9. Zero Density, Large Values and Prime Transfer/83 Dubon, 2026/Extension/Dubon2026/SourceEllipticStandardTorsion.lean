import Dubon2026.SourceEllipticStandardQuotientLattices

/-! The actual p+1 standard period-model points have exact prime order.
Integer lattice coordinates give the proof directly. These points supply
the factors of the odd-prime quotient product required by DUB-17/18;
SourceEllipticStandardCyclicDistinct proves their subgroup distinctness. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve UpperHalfPlane SourceFunctionField SourceFunctionField.JOrbitSeparation
noncomputable section

theorem fraction_mem_period_lattice_iff (τ : ℍ) (p : ℕ) [NeZero p] (a b : ℤ) :
    ((a : ℂ) * τ + b) / p ∈ (PeriodLattice.ofTau τ).lattice ↔
      (p : ℤ) ∣ a ∧ (p : ℤ) ∣ b := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [PeriodPair.mem_lattice]
  simp only [PeriodLattice.ofTau_ω₁, PeriodLattice.ofTau_ω₂, mul_one]
  constructor
  · rintro ⟨m, n, hmn⟩
    have heq : (((p : ℤ) * m : ℤ) : ℂ) * τ + ((p : ℤ) * n : ℤ) = (a : ℂ) * τ + b := by
      push_cast
      field_simp at hmn
      linear_combination hmn
    obtain ⟨hm, hn⟩ := int_indep τ heq
    exact ⟨⟨m, hm.symm⟩, ⟨n, hn.symm⟩⟩
  · rintro ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩
    refine ⟨m, n, ?_⟩
    push_cast
    field_simp

theorem periodModelHom_fraction_order (τ : ℍ) (C : VariableChange ℂ)
    (p : ℕ) [hp : Fact p.Prime] (a b : ℤ)
    (hab : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b)) :
    addOrderOf (periodModelHom (PeriodLattice.ofTau τ) C (((a : ℂ) * τ + b) / p)) = p := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  apply addOrderOf_eq_prime
  · rw [← map_nsmul, ← AddMonoidHom.mem_ker, ker_periodModelHom]
    change p • (((a : ℂ) * τ + b) / p) ∈ (PeriodLattice.ofTau τ).lattice
    rw [nsmul_eq_mul, mul_div_cancel₀ _ hp0]
    exact PeriodPair.mem_lattice.mpr ⟨a, b, by simp only [PeriodLattice.ofTau_ω₁,
      PeriodLattice.ofTau_ω₂, mul_one]⟩
  · intro h
    apply hab
    apply (fraction_mem_period_lattice_iff τ p a b).mp
    rw [← AddMonoidHom.mem_ker, ker_periodModelHom] at h
    exact h

/-- The literal standard p+1 cyclic generators in the actual period model. -/
def standardTorsionPoint (τ : ℍ) (C : VariableChange ℂ) (p : ℕ) :
    Fin (p + 1) → (C • periodCurve (PeriodLattice.ofTau τ)).toAffine.Point :=
  Fin.cases (periodModelHom (PeriodLattice.ofTau τ) C (1 / p))
    (fun b : Fin p => periodModelHom (PeriodLattice.ofTau τ) C (((τ : ℂ) + b.val) / p))

theorem standardTorsionPoint_order (τ : ℍ) (C : VariableChange ℂ)
    (p : ℕ) [hp : Fact p.Prime] (i : Fin (p + 1)) :
    addOrderOf (standardTorsionPoint τ C p i) = p := by
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    exact_mod_cast hp.out.not_dvd_one
  refine Fin.cases ?_ (fun b => ?_) i
  · simpa only [standardTorsionPoint, Fin.cases_zero, Int.cast_zero, Int.cast_one,
      zero_mul, zero_add] using periodModelHom_fraction_order τ C p 0 1 (fun h => hp1 h.2)
  · simpa only [standardTorsionPoint, Fin.cases_succ, Int.cast_one, one_mul, Int.cast_natCast]
      using periodModelHom_fraction_order τ C p 1 b.val (fun h => hp1 h.1)

end
end Dubon2026.SourceEllipticPeriod
