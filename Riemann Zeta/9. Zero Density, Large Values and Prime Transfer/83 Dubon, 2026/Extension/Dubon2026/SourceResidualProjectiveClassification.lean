import Dubon2026.SourceDicksonClassification

/-! DUB-17/18 -> original residual large image -> projective-image alternatives.
The field map and projective subgroup below are constructed from the actual
rank-two action. The theorem classifies that image and leaves all arithmetic
exclusions visible; it does not assert large image. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
variable (p : ℕ) [Fact p.Prime]

/-- The projective action obtained by applying a coefficient embedding entrywise. -/
def residualProjectiveAction {F : Type*} [Field F] {Γ : Type*} [Group Γ]
    (j : F →+* K p) (ρ : Γ →* GL (Fin 2) F) : Γ →* PGLOf (K p) :=
  (QuotientGroup.mk' (Subgroup.center (GL (Fin 2) (K p)))).comp
    ((GeneralLinearGroup.map j).comp ρ)

/-- A finite characteristic-p coefficient field embeds in the fixed algebraic closure. -/
theorem exists_residualCoefficientEmbedding (F : Type*) [Field F] [Finite F]
    [CharP F p] : Nonempty (F →+* K p) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  exact ⟨(IsAlgClosed.lift : F →ₐ[ZMod p] K p).toRingHom⟩

/-- The entrywise coefficient embedding and projectivization preserve finite image. -/
theorem residualProjectiveAction_finite {F : Type*} [Field F] {Γ : Type*} [Group Γ]
    (j : F →+* K p) (ρ : Γ →* GL (Fin 2) F) (hρ : (Set.range ρ).Finite) :
    Finite (residualProjectiveAction p j ρ).range := by
  let π : GL (Fin 2) F →* PGLOf (K p) :=
    (QuotientGroup.mk' _).comp (GeneralLinearGroup.map j)
  have h : (Set.range (π.comp ρ)).Finite := by
    change (Set.range (π ∘ ρ)).Finite
    rw [Set.range_comp]
    exact hρ.image π
  exact h.to_subtype

/-- The full eight-way Dickson disjunction for a projective subgroup. This is only
notation for the displayed alternatives; the following theorem proves it. -/
def HasDicksonAlternatives (G : Subgroup (PGLOf (K p))) : Prop :=
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m)))))

/-- Dickson's proved classification gives the full alternative predicate. -/
theorem hasDicksonAlternatives [Fact (2 < p)]
    (G : Subgroup (PGLOf (K p))) [Finite G] : HasDicksonAlternatives p G :=
  dickson_classification p G

/-- Dickson's alternatives hold for the actual embedded projective residual image. -/
theorem residual_projective_classification [Fact (2 < p)]
    {F : Type*} [Field F] {Γ : Type*} [Group Γ]
    (j : F →+* K p) (ρ : Γ →* GL (Fin 2) F) (hρ : (Set.range ρ).Finite) :
    HasDicksonAlternatives p (residualProjectiveAction p j ρ).range := by
  letI := residualProjectiveAction_finite p j ρ hρ
  exact hasDicksonAlternatives p _

end
end Dubon2026.SourceDickson
