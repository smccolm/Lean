import Dubon2026.SourceEllipticIntegralInertiaCocycle

/-! Discharge the unit-two/three premises using the constant field of the
required positive-characteristic place. Thus the shortened integral-change
route serves the original characteristic-at-least-five genus application.
The algebra on the valuation ring is the actual constant-field embedding,
which is supplied by a place over that field. This feeds the inertia action
on prime-to-characteristic torsion in the DUB-17/18 exceptional-fiber census. -/
namespace Dubon2026.SourceEllipticReduction
open WeierstrassCurve IsLocalRing
noncomputable section

theorem isUnit_two_three_of_five_le (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    (p : ℕ) [CharP K p] (hp : 5 ≤ p) : IsUnit (2 : A) ∧ IsUnit (3 : A) := by
  have hsmall (n : ℕ) (hn : 0 < n) (hnp : n < p) : IsUnit (n : A) := by
    have hnK : (n : K) ≠ 0 := by
      intro hz
      have hd := (CharP.cast_eq_zero_iff K p n).mp hz
      exact (not_le_of_gt hnp) (Nat.le_of_dvd hn hd)
    simpa only [map_natCast] using hnK.isUnit.map (algebraMap K A)
  exact ⟨hsmall 2 (by omega) (by omega), hsmall 3 (by omega) (by omega)⟩

theorem exists_integral_inertia_cocycle_of_five_le
    {F M : Type*} [Field F] [Field M] [Algebra F M] {A : ValuationSubring M}
    (K : Type*) [Field K] [Algebra K A] (p : ℕ) [CharP K p] (hp : 5 ≤ p)
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hW : IsUnit W.Δ)
    (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F) :
    ∃ g : VariableChange A,
      g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
      g • conjugateModel W σ hσ = W ∧
      ((⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
        g.map (residue A) • W.map (residue A) = W.map (residue A)) := by
  obtain ⟨h2, h3⟩ := isUnit_two_three_of_five_le K A p hp
  exact exists_integral_inertia_cocycle h2 h3 E W κ hκ hW σ hσ

end
end Dubon2026.SourceEllipticReduction
