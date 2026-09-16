import Tao2026.SylvesterSchurComplete
import Tao2026.ErdosSelfridgeHanson
import Tao2026.FactorialOneTermAsymptotics

/-!
# Unconditional square Erdős--Selfridge and factorial-fiber consequences

The unrestricted Sylvester--Schur theorem closes the last premise of the
already formalized Hanson/Erdős--Selfridge square argument.  This module
exports the resulting unconditional square theorem and removes that premise
from the public Theorem 1.10 consumers.
-/

namespace Tao2026

/-- The square specialization of Erdős--Selfridge used by Tao's factorial
fiber argument. -/
theorem erdosSelfridgeSquare : ErdosSelfridgeSquareConclusion :=
  erdosSelfridgeSquareConclusion_of_sylvesterSchur sylvesterSchur

/-- Every factorial squarefree-component fiber has at most two elements. -/
theorem factorialSquarefreeFiberUpTo_card_le_two_unconditional (x d : ℕ) :
    (factorialSquarefreeFiberUpTo x d).card ≤ 2 :=
  factorialSquarefreeFiberUpTo_card_le_two erdosSelfridgeSquare x d

/-- With the square theorem internal, Lemma 4.2 is the only remaining input
to the exact public Theorem 1.10 conclusion. -/
theorem taoTheorem110_of_lemma42
    (h42 : TaoLemma42Conclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_lemma42_and_erdosSelfridge erdosSelfridgeSquare h42

/-- Theorem 1.10 now follows from Theorem 2.5 and Proposition 2.3(ii), with
the Erdős--Selfridge dependency discharged internally. -/
theorem taoTheorem110_of_analytic_inputs
    (h25 : TaoTheorem25SpecializedConclusion)
    (h23ii : TaoProposition23iiConclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_analytic_inputs_direct erdosSelfridgeSquare h25 h23ii

/-- Source-facing variant using the pinned Baker--Harman--Pintz contract. -/
theorem taoTheorem110_of_source_inputs
    (h25 : TaoTheorem25SpecializedConclusion)
    (hBHP : BakerHarmanPintzTheorem1Conclusion) : TaoTheorem110Conclusion :=
  taoTheorem110_of_source_inputs_direct erdosSelfridgeSquare h25 hBHP

end Tao2026
