import Dubon2026.SourceAbsoluteCyclicFrobeniusEquality

/-! DUB-17/18 -> original all-weight association -> compatible original
adic traces. A small trace/determinant comparison consumes proved actual
norm-Frobenius values. Its source consumer uses the native quotient maps
and the original Fourier coefficients at two arbitrary precisions. -/
namespace Dubon2026
noncomputable section
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric algebraicLocalIntegerAction
attribute [local instance 1100] rationalPrimeOriginalNormedField
local notation "Qbar" => AlgebraicClosure ℚ
private local instance : IsGalois ℚ Qbar := sourceRationalAlgebraicClosure_isGalois

private theorem monoid_cyclic {G R : Type} [Group G] [CommRing R]
    (D : G →* R) (g h : G) : D (g * h) = D (h * g) := by
  rw [map_mul, map_mul, mul_comm]

/-- Exact original norm-Frobenius comparison identifies a mapped continuous
trace/determinant pair on the entire actual absolute Galois group. -/
theorem absolute_continuous_trace_pair_map_eq
    {A B : Type} [CommRing A] [CommRing B] (π : A →+* B)
    (t₁ : Gal(Qbar/ℚ) → A) (D₁ : Gal(Qbar/ℚ) →* A)
    (t₂ : Gal(Qbar/ℚ) → B) (D₂ : Gal(Qbar/ℚ) →* B)
    (hc₁ : @Continuous _ _ _ ⊥ t₁) (hD₁ : @Continuous _ _ _ ⊥ D₁)
    (hc₂ : @Continuous _ _ _ ⊥ t₂) (hD₂ : @Continuous _ _ _ ⊥ D₂)
    (ht₁ : ∀ g h, t₁ (g * h) = t₁ (h * g))
    (ht₂ : ∀ g h, t₂ (g * h) = t₂ (h * g)) (S : Finset ℕ)
    (hFrob : ∀ (q : ℕ) (hq : q.Prime), q ∉ S →
      ∀ (e : Qbar →ₐ[ℚ] rationalPrimeLocalClosure q hq)
        (φ : Gal(rationalPrimeLocalClosure q hq/rationalPrimeLocalField q hq)),
        (∀ z : IsLocalRing.ResidueField (algebraicLocalIntegerRing
          (rationalPrimeLocalClosure q hq)), φ • z = z ^ q) →
        (π (t₁ (embeddedNormalGaloisRestriction e φ)), π (D₁ (embeddedNormalGaloisRestriction e φ))) =
          (t₂ (embeddedNormalGaloisRestriction e φ), D₂ (embeddedNormalGaloisRestriction e φ)))
    (g : Gal(Qbar/ℚ)) : π (t₁ g) = t₂ g ∧ π (D₁ g) = D₂ g := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : TopologicalSpace B := ⊥
  letI : DiscreteTopology B := ⟨rfl⟩
  have hπ : Continuous π := continuous_of_discreteTopology
  have he := absolute_continuous_cyclic_eq_of_norm_frobenius
    (fun a => (π (t₁ a), π (D₁ a))) (fun a => (t₂ a, D₂ a))
    ((hπ.comp hc₁).prodMk (hπ.comp hD₁)) (hc₂.prodMk hD₂)
    (fun a b => Prod.ext (congrArg π (ht₁ a b)) (congrArg π (monoid_cyclic D₁ a b)))
    (fun a b => Prod.ext (ht₂ a b) (monoid_cyclic D₂ a b)) S hFrob
  exact ⟨congrArg Prod.fst (congrFun he g), congrArg Prod.snd (congrFun he g)⟩

end
end Dubon2026
