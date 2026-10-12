import Dubon2026.ContinuousKummerCharacterPairing
import Mathlib.Algebra.Module.ZMod

/-! # Actual residue-ring module structures for the Kummer pairing factors -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (n : ℕ) [NeZero n]

/-- The group of original finite characters is a module over the actual
residue ring, since each original character value is killed by n. -/
abbrev galoisFiniteCharacterZModModule :
    Module (ZMod n) (Additive (Gal(Ω/K) →ₜ* Multiplicative (ZMod n))) :=
  AddCommGroup.zmodModule (fun χ => by
    apply Additive.toMul.injective
    change χ.toMul ^ n = 1
    apply ContinuousMonoidHom.ext
    intro g
    simp only [ContinuousMonoidHom.pow_apply]
    change n • (χ.toMul g).toAdd = 0
    exact ZModModule.char_nsmul_eq_zero n _)

variable [IsGalois K Ω] [IsAlgClosed Ω]
  [TopologicalSpace (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [DiscreteTopology (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) n)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Every original Kummer H1 class is killed by n. Surjectivity of the
actual Kummer map reduces this to its proved original power kernel. -/
theorem galoisRootContinuousH1_nsmul_eq_zero
    (x : GaloisRootContinuousH1 (K := K) (Ω := Ω) n) : n • x = 0 := by
  obtain ⟨a, rfl⟩ := galoisKummerH1Class_surjective n x
  have hp : galoisKummerH1Class n (a ^ n) = n • galoisKummerH1Class (Ω := Ω) n a :=
    map_pow (galoisKummerH1Hom (K := K) (Ω := Ω) n) a n
  rw [← hp]
  exact (galoisKummerH1Class_eq_zero_iff (Ω := Ω) n (a ^ n)).mpr ⟨a, rfl⟩

/-- The actual root H1 is a module over the original residue ring, derived
from its proved exponent and retaining its original additive group. -/
abbrev galoisRootH1ZModModule :
    Module (ZMod n) (GaloisRootContinuousH1 (K := K) (Ω := Ω) n) :=
  AddCommGroup.zmodModule (galoisRootContinuousH1_nsmul_eq_zero n)

end
end Dubon2026
