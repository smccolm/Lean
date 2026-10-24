import Dubon2026.SourceEllipticStandardTorsion

/-! The p+1 literal standard period-model points generate distinct cyclic
subgroups. Exact lattice coordinates distinguish the diagonal subgroup and
each upper subgroup. This is the injectivity required to enumerate the
geometric factors in the DUB-17/18 odd-prime quotient-product identity. -/

namespace Dubon2026.SourceEllipticPeriod
open WeierstrassCurve UpperHalfPlane SourceFunctionField

theorem standard_upper_not_mem_diagonal (τ : ℍ) (C : VariableChange ℂ)
    (p : ℕ) [hp : Fact p.Prime] (b : Fin p) :
    periodModelHom (PeriodLattice.ofTau τ) C (((τ : ℂ) + b.val) / p) ∉
      AddSubgroup.zmultiples (periodModelHom (PeriodLattice.ofTau τ) C (1 / p)) := by
  rw [periodModelHom_mem_zmultiples_iff]
  rintro ⟨m, hm⟩
  have hmem : (((1 : ℤ) : ℂ) * τ + ((b.val : ℤ) - m : ℤ)) / p ∈
      (PeriodLattice.ofTau τ).lattice := by
    convert hm using 1
    push_cast
    ring
  have hd := ((fraction_mem_period_lattice_iff τ p 1 (b.val - m)).mp hmem).1
  have hn : ¬ (p : ℤ) ∣ 1 := by exact_mod_cast hp.out.not_dvd_one
  exact hn hd

theorem standard_upper_mem_upper (τ : ℍ) (C : VariableChange ℂ)
    (p : ℕ) [NeZero p] (b c : Fin p)
    (h : periodModelHom (PeriodLattice.ofTau τ) C (((τ : ℂ) + b.val) / p) ∈
      AddSubgroup.zmultiples (periodModelHom (PeriodLattice.ofTau τ) C (((τ : ℂ) + c.val) / p))) :
    b = c := by
  obtain ⟨m, hm⟩ := (periodModelHom_mem_zmultiples_iff _ _ _ _).mp h
  have hmem : (((1 - m : ℤ) : ℂ) * τ + ((b.val : ℤ) - m * c.val : ℤ)) / p ∈
      (PeriodLattice.ofTau τ).lattice := by
    convert hm using 1
    push_cast
    ring
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ :=
    (fraction_mem_period_lattice_iff τ p (1 - m) (b.val - m * c.val)).mp hmem
  have hd : (p : ℤ) ∣ (b.val : ℤ) - c.val := by
    refine ⟨l - k * c.val, ?_⟩
    linear_combination hl - hk * c.val
  have heq := Int.modEq_of_dvd hd
  change (c.val : ℤ) % p = (b.val : ℤ) % p at heq
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast c.isLt),
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast b.isLt)] at heq
  exact Fin.ext (by exact_mod_cast heq.symm)

theorem standardTorsionPoint_zmultiples_injective (τ : ℍ) (C : VariableChange ℂ)
    (p : ℕ) [Fact p.Prime] :
    Function.Injective (fun i => AddSubgroup.zmultiples (standardTorsionPoint τ C p i)) := by
  intro i j h
  revert h
  refine Fin.cases ?_ (fun b => ?_) i <;> refine Fin.cases ?_ (fun c => ?_) j
  · exact fun _ => rfl
  · intro h
    simp only [standardTorsionPoint, Fin.cases_zero, Fin.cases_succ] at h
    apply (standard_upper_not_mem_diagonal τ C p c).elim
    rw [h]
    exact AddSubgroup.mem_zmultiples _
  · intro h
    simp only [standardTorsionPoint, Fin.cases_zero, Fin.cases_succ] at h
    apply (standard_upper_not_mem_diagonal τ C p b).elim
    rw [← h]
    exact AddSubgroup.mem_zmultiples _
  · intro h
    simp only [standardTorsionPoint, Fin.cases_succ] at h
    apply congrArg Fin.succ
    apply standard_upper_mem_upper τ C p b c
    rw [← h]
    exact AddSubgroup.mem_zmultiples _

end Dubon2026.SourceEllipticPeriod
