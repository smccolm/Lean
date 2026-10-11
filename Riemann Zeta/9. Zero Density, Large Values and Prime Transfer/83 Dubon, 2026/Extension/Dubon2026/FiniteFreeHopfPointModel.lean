import Dubon2026.FiniteFreeHopfGaloisAction

/-! # Actual finite free Hopf models of a given original Galois module

This is the coordinate form of the geometric-point realization in de Smit--Lenstra,
Section 6.3. The structure records an actual coordinate ring and its operations.
Its existence, closure under subgroup and quotient, and the arithmetic deformation
application are separate proof obligations.
-/

namespace Dubon2026
noncomputable section

universe uR uF uK uV uC

variable (R : Type uR) (F : Type uF) (K : Type uK) (V : Type uV)
  [CommRing R] [Field F] [Field K] [Algebra R F] [Algebra F K] [Algebra R K]
  [IsScalarTower R F K] [CommGroup V]

/-- Genuine finite free cocommutative Hopf coordinates realizing the specified original Galois module. The group law, integral coordinate algebra, finite freeness, and actual coefficient action are part of the mathematical model, not substitutes for proving that a given representation admits such a model. -/
structure FiniteFreeHopfPointModel (ρ : (K ≃ₐ[F] K) →* MulAut V) where
  /-- The actual original integral coordinate algebra. -/
  Coordinates : Type uC
  /-- Commutative coordinate multiplication. -/
  [commRing : CommRing Coordinates]
  /-- The actual integral Hopf operations and their proved identities. -/
  [hopf : HopfAlgebra R Coordinates]
  /-- Cocommutativity models the commutative geometric group law. -/
  [cocomm : Coalgebra.IsCocomm R Coordinates]
  /-- Finite original coordinates. -/
  [finite : Module.Finite R Coordinates]
  /-- Free original coordinates, hence flat. -/
  [free : Module.Free R Coordinates]
  /-- The actual original geometric point group realizes the given group. -/
  pointEquiv : WithConv (Coordinates →ₐ[R] K) ≃* V
  /-- The model realizes precisely the specified original Galois action. -/
  galois : ∀ (g : K ≃ₐ[F] K) (p : WithConv (Coordinates →ₐ[R] K)),
    pointEquiv (hopfPointsGaloisAction (R := R) (F := F) g p) = ρ g (pointEquiv p)

variable {R F K V} {ρ : (K ≃ₐ[F] K) →* MulAut V}

/-- A genuine finite free model forces finiteness of the original represented group, by finiteness of its actual coordinate points. -/
theorem finiteFreeHopfPointModel_finite (m : FiniteFreeHopfPointModel R F K V ρ) :
    Finite V := by
  letI := m.commRing
  letI := m.hopf
  letI := m.finite
  letI := m.free
  letI : Finite (WithConv (m.Coordinates →ₐ[R] K)) := finiteFreeHopfPoints_finite
  exact Finite.of_surjective m.pointEquiv m.pointEquiv.surjective

/-- Over the actual algebraic point field, the given original action has open kernel because the model identifies it with the genuine finite-coordinate Galois action. -/
theorem finiteFreeHopfPointModel_isOpen_ker [Algebra.IsIntegral F K]
    (m : FiniteFreeHopfPointModel R F K V ρ) :
    IsOpen (ρ.ker : Set (K ≃ₐ[F] K)) := by
  letI := m.commRing
  letI := m.hopf
  letI := m.finite
  letI := m.free
  let a := hopfPointsGaloisAction (R := R) (A := m.Coordinates) (F := F) (K := K)
  have hker : ρ.ker = a.ker := by
    ext g
    change ρ g = 1 ↔ a g = 1
    constructor
    · intro hg
      apply MulEquiv.ext
      intro p
      apply m.pointEquiv.injective
      change m.pointEquiv (a g p) = m.pointEquiv p
      rw [m.galois, hg]
      rfl
    · intro hg
      apply MulEquiv.ext
      intro v
      obtain ⟨p, rfl⟩ := m.pointEquiv.surjective v
      rw [← m.galois]
      change m.pointEquiv (a g p) = m.pointEquiv p
      rw [hg]
      rfl
  rw [hker]
  exact hopfPointsGaloisAction_isOpen_ker

end
end Dubon2026
