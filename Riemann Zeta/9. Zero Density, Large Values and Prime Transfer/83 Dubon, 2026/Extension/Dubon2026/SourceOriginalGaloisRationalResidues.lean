import Dubon2026.SourceOriginalGaloisResidueMap
import Dubon2026.SourceOriginalRationalResidues

/-! DUB-17/18 -> original global residue identity -> auxiliary Galois trace.
The actual auxiliary residue functional vanishes on the original rational
j-subfield. The frozen rational embedding is composed with the actual field
inclusion; the existing partial-fraction span and power-residue theorem then
give vanishing. This is the base-field input to Galois averaging.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

private theorem D_sub_constant {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (c : K) : D K F (x - algebraMap K F c) = D K F x := by
  rw [map_sub, Derivation.map_algebraMap, sub_zero]

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

/-- The original rational j-embedding followed by the literal normal-closure inclusion. -/
def originalGaloisRationalEmbedding : RatFunc L →ₐ[L] originalGaloisClosure N L :=
  ((Algebra.ofId (modularFunctionFieldOver N L) (originalGaloisClosure N L)).restrictScalars L).comp
    (originalRationalJEmbedding N L)

omit [NeZero N] in
theorem originalGaloisRationalEmbedding_X :
    originalGaloisRationalEmbedding N L RatFunc.X = originalGaloisJ N L := by
  change algebraMap (modularFunctionFieldOver N L) (originalGaloisClosure N L)
    (originalRationalJEmbedding N L RatFunc.X) = _
  rw [originalRationalJEmbedding_X]
  rfl

omit [NeZero N] in
theorem originalGaloisRationalEmbedding_shift_power (c : L) (n : ℤ) :
    originalGaloisRationalEmbedding N L ((RatFunc.X - RatFunc.C c) ^ n) =
      (originalGaloisJ N L - algebraMap L (originalGaloisClosure N L) c) ^ n := by
  rw [map_zpow₀, map_sub, originalGaloisRationalEmbedding_X,
    ← RatFunc.algebraMap_eq_C, AlgHom.commutes]

theorem originalGaloisResidueMap_shift_power [IsAlgClosed L] (c : L) (n : ℤ) :
    originalGaloisResidueMap N L
      ((originalGaloisJ N L - algebraMap L (originalGaloisClosure N L) c) ^ n) = 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI := hasPrincipalDivisors_originalGaloisClosure N L
  haveI : ∀ v : Place L (originalGaloisClosure N L),
      Module.Finite v.toValuationSubring Ω[v.toValuationSubring⁄L] :=
    finite_originalGaloisClosure_place_differentials N L
  haveI : ∀ v : Place L (originalGaloisClosure N L), Algebra.IsSeparable L v.ResidueField :=
    fun v => by
      haveI := originalGaloisClosure_place_residue_isAlgebraic N L v
      infer_instance
  haveI : ∀ v : Place L (originalGaloisClosure N L), v.DCoordGenerates :=
    originalGaloisClosure_place_dCoordGenerates N L
  haveI : Nontrivial Ω[originalGaloisClosure N L⁄L] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_originalGaloisClosure_differentials N L)
  have hf : originalGaloisJ N L - algebraMap L (originalGaloisClosure N L) c ≠ 0 := by
    intro he
    apply transcendental_originalGaloisClosure_j N L
    change IsAlgebraic L (originalGaloisJ N L)
    rw [sub_eq_zero.mp he]
    exact isAlgebraic_algebraMap c
  have hD : D L (originalGaloisClosure N L)
      (originalGaloisJ N L - algebraMap L (originalGaloisClosure N L) c) =
      D L (originalGaloisClosure N L) (originalGaloisJ N L) :=
    D_sub_constant (originalGaloisJ N L) c
  rw [originalGaloisResidueMap_apply, ← hD]
  exact residueSum_power_differential (K := L) (F := originalGaloisClosure N L)
    (originalGaloisCanonicalLocalResidueData N L)
    (originalGaloisClosure_place_residue_bijective N L) hf n

theorem originalGaloisResidueMap_rational [IsAlgClosed L] (h : RatFunc L) :
    originalGaloisResidueMap N L (originalGaloisRationalEmbedding N L h) = 0 := by
  let φ := (originalGaloisResidueMap N L).comp (originalGaloisRationalEmbedding N L).toLinearMap
  have hφ : φ = 0 := by
    apply linearMap_eq_zero_of_shift_powers L
    intro c n
    change originalGaloisResidueMap N L
      (originalGaloisRationalEmbedding N L ((RatFunc.X - RatFunc.C c) ^ n)) = 0
    rw [originalGaloisRationalEmbedding_shift_power]
    exact originalGaloisResidueMap_shift_power N L c n
  exact LinearMap.congr_fun hφ h

end
end Dubon2026.SourceFunctionField
