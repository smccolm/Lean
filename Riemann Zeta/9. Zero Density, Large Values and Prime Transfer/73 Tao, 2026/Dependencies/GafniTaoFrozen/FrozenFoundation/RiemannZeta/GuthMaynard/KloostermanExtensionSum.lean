import RiemannZeta.GuthMaynard.KloostermanRoots

/-!
# Extension-field Kloosterman sums

This module defines the exact two-frequency sum over `GaloisField p n` and
identifies the scalar trace sum in the Harcos point-count calculation with
that source-facing object.
-/

open scoped BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- The `extensionKloostermanSum` definition used by the source-facing construction in `KloostermanExtensionSum`. -/
noncomputable def extensionKloostermanSum
    (p n : ℕ) [Fact p.Prime]
    (A B : GaloisField p n) : ℂ := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact ∑ t : (GaloisField p n)ˣ,
    ZMod.stdAddChar
      (Algebra.trace (ZMod p) (GaloisField p n)
        (A * (t : GaloisField p n) + B / (t : GaloisField p n)))

theorem extensionKloostermanScalarSum_eq
    (p n : ℕ) [Fact p.Prime] (c : GaloisField p n) (m : ZMod p) :
    extensionKloostermanScalarSum p n c m =
      extensionKloostermanSum p n
        (algebraMap (ZMod p) (GaloisField p n) m)
        (algebraMap (ZMod p) (GaloisField p n) m * c) := by
  classical
  letI := Fintype.ofFinite (GaloisField p n)
  unfold extensionKloostermanScalarSum extensionKloostermanSum
  apply Finset.sum_congr rfl
  intro t _ht
  apply congrArg ZMod.stdAddChar
  change m • (Algebra.trace (ZMod p) (GaloisField p n))
      ((t : GaloisField p n) + c / (t : GaloisField p n)) = _
  rw [← LinearMap.map_smul]
  congr 1
  simp only [Algebra.smul_def]
  field_simp

end RiemannZeta.GuthMaynard
