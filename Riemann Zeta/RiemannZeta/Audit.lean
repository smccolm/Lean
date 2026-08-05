import Lean
import RiemannZeta.FiniteDirichletPolynomial
import RiemannZeta.CrossNormProduct
import RiemannZeta.CompletedZetaSymmetry
import RiemannZeta.HardyZ
import RiemannZeta.Nonvanishing
import RiemannZeta.GuthMaynard.Asymptotics
import RiemannZeta.GuthMaynard.Separated
import RiemannZeta.GuthMaynard.DirichletPolynomial
import RiemannZeta.GuthMaynard.ZeroCount
import RiemannZeta.GuthMaynard.ZeroDetector
import RiemannZeta.GuthMaynard.ExponentArithmetic
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.MeanValue
import RiemannZeta.GuthMaynard.Transfer
import RiemannZeta.GuthMaynard.ExtractSeparated
import RiemannZeta.GuthMaynard.BetaDependence
import RiemannZeta.GuthMaynard.DensityReduction

open Lean

def checkNoAxioms : CoreM Unit := do
  let env ← getEnv
  let mut foundAxiom := false
  for (n, cinfo) in env.constants.toList do
    if n.getRoot.toString == "RiemannZeta" then
      match cinfo with
      | ConstantInfo.axiomInfo _ => 
          logError m!"Axiom found in project: {n}"
          foundAxiom := true
      | _ => pure ()
  if foundAxiom then
    throwError "Project contains unproved axioms!"

#eval checkNoAxioms

#print axioms RiemannZeta.GuthMaynard.conditionalZeroDensityTransfer
#print axioms RiemannZeta.GuthMaynard.mean_value_reduction
#print axioms RiemannZeta.GuthMaynard.polynomialPowerIdentity
#print axioms RiemannZeta.GuthMaynard.deduce_extract_separated
#print axioms RiemannZeta.GuthMaynard.beta_dependence_removal
#print axioms RiemannZeta.GuthMaynard.functional_symmetry_implies_reduction
