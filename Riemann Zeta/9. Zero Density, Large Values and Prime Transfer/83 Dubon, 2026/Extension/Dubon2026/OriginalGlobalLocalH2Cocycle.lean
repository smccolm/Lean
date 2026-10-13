import Dubon2026.OriginalIdeleH2LocalDetection

/-! # The actual global-to-local H2 maps retain the original completion embedding

The local-detection maps send the original global cocycle to its literal
subgroup restriction, with each coefficient embedded into the original
completion. This provides the cochain identity needed to compare them
with normalized local invariants before DUB-17's cyclotomic killing step.
-/
namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The literal embedding of original field units into an original completion. -/
def originalGlobalCompletionUnitMap (p : SUnitLogPlace L S) :
    Additive Lˣ →ₗ[ℤ] supportedUnrestrictedUnitModule L S p := by
  cases p with
  | inl w => exact (Units.map (algebraMap L w.Completion).toMonoidHom).toAdditive.toIntLinearMap
  | inr w => exact (Units.map (algebraMap L (w.val.adicCompletion L)).toMonoidHom).toAdditive.toIntLinearMap

/-- The original principal-idele coordinate is the literal original completion embedding. -/
theorem originalFullUnrestrictedCoordinate_principal
    (p : SUnitLogPlace L S) (x : Additive Lˣ) :
    originalFullUnrestrictedCoordinate K L S p ((originalFullPrincipalRepHom K L).hom x) =
      originalGlobalCompletionUnitMap L S p x := by
  cases p <;> rfl

/-- The actual completion-stabilizer coefficient attached to an original finite-support orbit. -/
def originalLocalCompletionRep :
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      Rep ℤ (MulAction.stabilizer Gal(L/K)
        (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)) := by
  letI := sUnitLogPlaceAction K L S hS
  intro ω
  exact transportedOrbitPointRep ℤ Gal(L/K) (SUnitLogPlace L S)
    (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
    (supportedUnrestrictedUnitTransport_one K L S hS)
    (supportedUnrestrictedUnitTransport_mul K L S hS) ω
    (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)

/-- The original global-unit coefficient restricted to the actual stabilizer and embedded into its original completion. -/
def originalGlobalLocalUnitRepHom :
    letI := sUnitLogPlaceAction K L S hS
    ∀ ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S),
      Rep.res (MulAction.stabilizer Gal(L/K)
        (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)).subtype
        (Rep.ofAlgebraAutOnUnits K L) ⟶ originalLocalCompletionRep K L S hS ω := by
  letI := sUnitLogPlaceAction K L S hS
  intro ω
  let H := MulAction.stabilizer Gal(L/K) (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)
  exact (Rep.resFunctor H.subtype).map (originalFullPrincipalRepHom K L) ≫
    (Rep.resFunctor H.subtype).map (originalFullUnrestrictedRepHom K L S hS) ≫
      originalTransportedOrbitEvaluation ℤ Gal(L/K) (SUnitLogPlace L S)
        (supportedUnrestrictedUnitModule L S) (supportedUnrestrictedUnitTransport K L S hS)
        (supportedUnrestrictedUnitTransport_one K L S hS)
        (supportedUnrestrictedUnitTransport_mul K L S hS) ω

/-- The original local coefficient homomorphism is literally the original field-to-completion map. -/
theorem originalGlobalLocalUnitRepHom_apply :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S)) (x : Additive Lˣ),
      (originalGlobalLocalUnitRepHom K L S hS ω).hom x =
        originalGlobalCompletionUnitMap L S ω.out x := by
  letI := sUnitLogPlaceAction K L S hS
  intro ω x
  exact originalFullUnrestrictedCoordinate_principal K L S ω.out x

/-- The actual original global two-cocycle restricted and embedded into its original local coefficient. -/
def originalGlobalLocalTwoCocycle :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S)),
      groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L) →
        groupCohomology.cocycles₂ (originalLocalCompletionRep K L S hS ω) := by
  letI := sUnitLogPlaceAction K L S hS
  intro ω c
  exact groupCohomology.mapCocycles₂
    (MulAction.stabilizer Gal(L/K) (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)).subtype
    (originalGlobalLocalUnitRepHom K L S hS ω) c

/-- Original localization retains the actual global cocycle values and the actual completion embedding. -/
theorem originalGlobalLocalTwoCocycle_apply :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S))
      (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L))
      (g h : MulAction.stabilizer Gal(L/K) (originalOrbitPoint Gal(L/K) (SUnitLogPlace L S) ω)),
      originalGlobalLocalTwoCocycle K L S hS ω c (g, h) =
        originalGlobalCompletionUnitMap L S ω.out (c (g.val, h.val)) := by
  letI := sUnitLogPlaceAction K L S hS
  intro ω c g h
  exact originalGlobalLocalUnitRepHom_apply K L S hS ω (c (g.val, h.val))

/-- The global-to-local H2 map used for detection is induced by that same literal restricted completion cocycle. -/
theorem originalIdeleLocalH2Map_principal_cocycle :
    letI := sUnitLogPlaceAction K L S hS
    ∀ (ω : MulAction.orbitRel.Quotient Gal(L/K) (SUnitLogPlace L S))
      (c : groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L)),
      originalIdeleLocalH2Map K L S hS ω
        ((groupCohomology.functor ℤ Gal(L/K) 2).map (originalFullPrincipalRepHom K L)
          (groupCohomology.H2π _ c)) =
        groupCohomology.H2π _ (originalGlobalLocalTwoCocycle K L S hS ω c) := by
  letI := sUnitLogPlaceAction K L S hS
  intro ω c
  change groupCohomology.map _ _ 2
    (groupCohomology.map (MonoidHom.id Gal(L/K)) (originalFullPrincipalRepHom K L) 2
      (groupCohomology.H2π _ c)) = _
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply]
  rfl

end
end Dubon2026
