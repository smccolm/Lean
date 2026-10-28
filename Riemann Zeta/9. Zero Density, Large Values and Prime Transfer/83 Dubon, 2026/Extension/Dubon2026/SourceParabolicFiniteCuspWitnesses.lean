import Dubon2026.SourceCocycleConjugateCoboundary
import Dubon2026.SourcePeriodParabolicClass
import Dubon2026.SourceManinCuspSpace

/-! DUB17/18 -> original all-weight association -> uniform integral
parabolic denominator. The existing original cusp-orbit quotient gives
representatives; local integral witnesses at those representatives
transport to every cusp by the proved cocycle conjugation formula.
At nonzero original level this quotient is already proved finite. -/
namespace Dubon2026
noncomputable section
open CongruenceSubgroup Matrix.SpecialLinearGroup groupCohomology SourceManin
open scoped MatrixGroups

theorem sourceParabolicCocycles_of_cusp_orbit_witnesses
    {R : Type} [CommRing R] (Q : ℕ) (A : Rep R (Gamma0 Q)) (c : cocycles₁ A)
    (hc : ∀ q : CuspSpace Q, ∃ v : A,
      ∀ γ : Gamma0 Q, mapGL ℚ γ.val • q.out = q.out → c γ = A.ρ γ v - v) :
    c ∈ sourceParabolicCocycles (Gamma0 Q) A := by
  intro γ hγ
  obtain ⟨β, hβ⟩ := sourceParabolic_exists_fixed_cusp γ.val hγ
  let q := CuspSpace.mk Q β
  have hq : CuspSpace.mk Q β = CuspSpace.mk Q q.out := (Quotient.out_eq q).symm
  obtain ⟨g, hg, he⟩ := CuspSpace.mk_eq_mk_iff.mp hq
  let h : Gamma0 Q := ⟨g, hg⟩
  let δ : Gamma0 Q := h⁻¹ * γ * h
  have hd : mapGL ℚ δ.val • q.out = q.out := by
    change mapGL ℚ (g⁻¹ * γ.val * g) • q.out = q.out
    rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, he, hβ, ← he, inv_smul_smul]
  obtain ⟨v, hv⟩ := hc q
  have hh := sourceCocycle_conjugate_coboundary A c h δ v (hv δ hd)
  have hi : h * δ * h⁻¹ = γ := by dsimp only [δ]; group
  rw [hi] at hh
  exact ⟨A.ρ h v - c h, hh⟩

end
end Dubon2026
