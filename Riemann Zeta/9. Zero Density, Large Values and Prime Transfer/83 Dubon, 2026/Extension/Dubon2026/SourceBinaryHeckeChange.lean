import Dubon2026.SourceBinaryHeckeCohomology

/-! Hecke compatibility of literal coefficient change.
DUB-17/18 -> residual modular Galois association -> nonzero residual H1
eigensystem -> the integral Hecke algebra and its complex/residual actions.
The actual full coset formula proves compatibility on all cocycles and H1,
without a supplied Hecke compatibility hypothesis.
-/

namespace Dubon2026
noncomputable section
open CongruenceSubgroup

variable {R S : Type} [CommRing R] [CommRing S]
    (φ : R →+* S) {p Q : ℕ} [NeZero p] (hp : Nat.Prime p) (w : ℕ)

private local instance sourceBinaryHeckeChangeFintype :
    Fintype (Gamma0 Q ⧸ heckeUpperSubgroup Q p) :=
  sourceHeckeUpperFintype Q p

/-- The actual cocycle coefficient map commutes with the full original Hecke correspondence. -/
theorem sourceBinaryCocyclesChange_hecke
    (c : groupCohomology.cocycles₁ (sourceBinaryCoefficientRep R Q w)) :
    sourceBinaryCocyclesChange φ Q w (sourceBinaryHeckeCocycle R hp w c) =
      sourceBinaryHeckeCocycle S hp w (sourceBinaryCocyclesChange φ Q w c) := by
  apply groupCohomology.cocycles₁_ext
  intro g
  change homogeneousCoefficientMap w φ (sourceBinaryHeckeCocycle R hp w c g) =
    sourceBinaryHeckeCocycle S hp w (sourceBinaryCocyclesChange φ Q w c) g
  rw [sourceBinaryHeckeCocycle_apply, sourceBinaryHeckeCocycle_apply, map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [sourceBinaryCoefficientMap_equivariant, homogeneousCoefficientMap_intertwines]
  have hm : (Matrix.diagonal ![(p : R), 1]).map φ =
      Matrix.diagonal ![(p : S), 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hm]
  rfl

/-- The full actual native binary H1 Hecke action commutes with coefficient change. -/
theorem sourceBinaryH1Change_hecke
    (x : groupCohomology.H1 (sourceBinaryCoefficientRep R Q w)) :
    sourceBinaryH1Change φ Q w (sourceBinaryHeckeH1 R hp w x) =
      sourceBinaryHeckeH1 S hp w (sourceBinaryH1Change φ Q w x) := by
  refine groupCohomology.H1_induction_on x ?_
  intro c
  rw [sourceBinaryHeckeH1_cocycle, sourceBinaryH1Change_cocycle,
    sourceBinaryH1Change_cocycle, sourceBinaryHeckeH1_cocycle,
    sourceBinaryCocyclesChange_hecke]

end
end Dubon2026
