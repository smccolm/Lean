import Dubon2026.ContinuousInvariantConnectingCocycle

/-! # The original continuous H0-to-H1 connecting map

Independence of the actual coefficient lift supplies the linear connecting map
needed by the cup-boundary adjunction in DUB-17's local duality dependency.
-/

namespace Dubon2026
noncomputable section

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G]
  (A B C : Rep.{0} R G)
  [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  [TopologicalSpace B] [DiscreteTopology B]
  (φ : A →ₗ[R] B) (hφ : Function.Injective φ)
  (hφρ : ∀ g a, φ (A.ρ g a) = B.ρ g (φ a))
  (ψ : B →ₗ[R] C) (hψ : Function.Surjective ψ)
  (hψρ : ∀ g b, ψ (B.ρ g b) = C.ρ g (ψ b))
  (hExact : LinearMap.range φ = LinearMap.ker ψ)
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (hB : Continuous (fun z : G × B => B.ρ z.1 z.2))

/-- Any genuine lift of the same invariant gives the original connecting class.
The difference of lifts supplies an explicit original continuous coboundary. -/
theorem coefficientInvariantConnectingClass_eq_of_lift
    (c : C.ρ.invariants) (a : continuousRepresentationCocyclesOne A) (b : B)
    (hb : ψ b = c.val) (ha : ∀ g, φ (a.val g) = B.ρ g b - b) :
    (Submodule.Quotient.mk
      (coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
        ContinuousRepresentationH1 A hA) = Submodule.Quotient.mk a := by
  let b₀ := exactCoefficientSection ψ hψ c.val
  have hd : b₀ - b ∈ LinearMap.range φ := by
    rw [hExact]
    change ψ (b₀ - b) = 0
    rw [map_sub, exactCoefficientSection_rightInverse, hb, sub_self]
  let v := exactCoefficientPreimage φ hφ (b₀ - b)
  have hv : φ v = b₀ - b := exactCoefficientPreimage_map φ hφ _ hd
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨v, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext g
  apply hφ
  change φ (A.ρ g v - v) =
    φ ((coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c).val g - a.val g)
  rw [map_sub, map_sub, hφρ, hv, coefficientInvariantConnectingCocycle_map, ha, map_sub]
  change B.ρ g b₀ - B.ρ g b - (b₀ - b) = (B.ρ g b₀ - b₀) - (B.ρ g b - b)
  abel

/-- The actual connecting map from invariant original coefficients to the
original continuous H1 quotient. Linearity follows from lift independence. -/
def continuousCoefficientInvariantConnectingMap :
    C.ρ.invariants →ₗ[R] ContinuousRepresentationH1 A hA where
  toFun c := Submodule.Quotient.mk
    (coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c)
  map_add' c d := by
    change (Submodule.Quotient.mk _ : ContinuousRepresentationH1 A hA) =
      Submodule.Quotient.mk
        (coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c +
          coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB d)
    apply coefficientInvariantConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
      (c + d) _ (exactCoefficientSection ψ hψ c.val + exactCoefficientSection ψ hψ d.val)
    · rw [map_add, exactCoefficientSection_rightInverse, exactCoefficientSection_rightInverse]
      rfl
    · intro g
      change φ (_ + _) = _
      rw [map_add, map_add]
      exact (congrArg₂ (fun x y : B => x + y)
        (coefficientInvariantConnectingCocycle_map A B C φ hφ hφρ ψ hψ hψρ hExact hB c g)
        (coefficientInvariantConnectingCocycle_map A B C φ hφ hφρ ψ hψ hψρ hExact hB d g)).trans
        (by abel)
  map_smul' r c := by
    change (Submodule.Quotient.mk _ : ContinuousRepresentationH1 A hA) =
      Submodule.Quotient.mk
        (r • coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c)
    apply coefficientInvariantConnectingClass_eq_of_lift A B C φ hφ hφρ ψ hψ hψρ hExact hA hB
      (r • c) _ (r • exactCoefficientSection ψ hψ c.val)
    · rw [map_smul, exactCoefficientSection_rightInverse]
      rfl
    · intro g
      change φ (r • _) = _
      rw [map_smul, map_smul]
      exact (congrArg (fun x : B => r • x)
        (coefficientInvariantConnectingCocycle_map A B C φ hφ hφρ ψ hψ hψρ hExact hB c g)).trans
        (smul_sub r _ _)

/-- The connecting map retains the class of the exact original lifted cocycle. -/
theorem continuousCoefficientInvariantConnectingMap_apply (c : C.ρ.invariants) :
    continuousCoefficientInvariantConnectingMap A B C φ hφ hφρ ψ hψ hψρ hExact hA hB c =
      (Submodule.Quotient.mk
        (coefficientInvariantConnectingCocycle A B C φ hφ hφρ ψ hψ hψρ hExact hB c) :
        ContinuousRepresentationH1 A hA) := rfl

end
end Dubon2026
