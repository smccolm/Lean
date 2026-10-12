import Dubon2026.CharacterDualTrivialLine
import Dubon2026.GaloisRootExponentPairing

/-! # Exact scalar character-dual coefficients of the original Kummer cup

An actual equivariant character-line/root identification identifies the dual
of the trivial prime-field line with the original roots. Evaluation becomes
the literal root exponent pairing. The actual rational-prime cyclotomic
identification already supplies these premises for DUB-17's local application.
-/

namespace Dubon2026
noncomputable section

attribute [local instance] galoisRootZModModule

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  (q : ℕ) [Fact q.Prime] (χ : Gal(Ω/K) →* ZMod q)
  (e : coefficientCharacterRep χ ≃+ galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q)
  (heρ : ∀ g a, e ((coefficientCharacterRep χ).ρ g a) =
    (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g (e a))

/-- The original scalar character dual is identified with the actual roots,
through its pinned evaluation coordinate and the given actual root identification. -/
def scalarCharacterDualRootCoefficientEquiv :
    characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ ≃+
      galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q :=
  (characterDualTrivialLineEquiv χ).toAddEquiv.trans e

include heρ in
/-- The dual-to-root identification retains the same actual Galois actions. -/
theorem scalarCharacterDualRootCoefficientEquiv_equivariant (g : Gal(Ω/K))
    (ℓ : characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ) :
    scalarCharacterDualRootCoefficientEquiv K Ω q χ e
      ((characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ).ρ g ℓ) =
        (galoisRootOfUnityRepresentation (K := K) (Ω := Ω) q).ρ g
          (scalarCharacterDualRootCoefficientEquiv K Ω q χ e ℓ) := by
  exact (congrArg e (characterDualTrivialLineEquiv_equivariant χ g ℓ)).trans
    (heρ g (characterDualTrivialLineEquiv χ ℓ))

/-- The actual scalar evaluation becomes exactly the original root exponent
pairing, preserving its two factors and the prime-field scalar action. -/
theorem scalarCharacterDualRootCoefficient_pairing (x : ZMod q)
    (ℓ : characterDualCoefficientRep (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ) :
    e (characterDualEvaluation (coefficientCharacterRep (1 : Gal(Ω/K) →* ZMod q)) χ x ℓ) =
      galoisRootExponentPairing q (scalarCharacterDualRootCoefficientEquiv K Ω q χ e ℓ) x := by
  rw [characterDualTrivialLine_pairing]
  exact ZMod.map_smul e x (characterDualTrivialLineEquiv χ ℓ)

end
end Dubon2026
