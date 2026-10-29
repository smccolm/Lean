import Dubon2026.SourceTwistedCoefficientDualAction

/-! DUB-17/18 -> original all-weight arithmetic association -> inertia
on the genuine coefficient-valued Tate dual. Triviality of its actual
coefficient and inverse Tate actions gives triviality on the full dual;
the original valuation consumer derives both inputs. -/
namespace Dubon2026
noncomputable section
variable {R S T V G : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup T] [Module R T] [AddCommGroup V]
  [Module R V] [Module S V] [IsScalarTower R S V] [Group G]

theorem sourceTwistedCoefficientDualAction_eq_one
    (τ : G →* Module.End S V) (ρ : G →* Module.End R T) (σ : G)
    (hV : τ σ = 1) (hT : ρ σ⁻¹ = 1) : sourceTwistedCoefficientDualAction τ ρ σ = 1 := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro x
  change τ σ (φ (ρ σ⁻¹ x)) = φ x
  rw [hV, hT]
  rfl

end
end Dubon2026
