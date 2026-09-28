"""Diagnostic replay of pinned paper-time ANTEDB, NOT mathematical proof.

The archived five-coordinate powering transformation is known false.
No output from this script is accepted as a Lean premise or proof.
The sole skipped source statement is the unrelated import-time density demo.
"""
from __future__ import annotations

import argparse
import ast
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import sys
import types

ROOT = Path("E:/Lean/.tmp_epzae_reproduction_20260927")
sys.dont_write_bytecode = True
sys.stdout.reconfigure(encoding="utf-8")
sys.stderr.reconfigure(encoding="utf-8")
sys.path.insert(0, str(ROOT / "site-packages"))
SOURCE = ROOT / "archive/expdb-9953003/blueprint/src/python"
sys.path.insert(0, str(SOURCE))
os.environ["MPLBACKEND"] = "Agg"
os.environ["MPLCONFIGDIR"] = str(ROOT / "matplotlib-cache")

parser = argparse.ArgumentParser()
parser.add_argument("recipes", nargs="*", default=["inspect"])
args = parser.parse_args()

print("HISTORICAL REPRODUCTION ONLY: archived powering is not a valid proof.", flush=True)
print("Python", sys.version, flush=True)
for package in ("pycddlib", "sympy", "numpy", "scipy", "matplotlib"):
    print(package, importlib.metadata.version(package), flush=True)

source = (SOURCE / "derived.py").read_text(encoding="utf-8")
tree = ast.parse(source, filename=str(SOURCE / "derived.py"))
skipped = []
kept = []
for node in tree.body:
    if (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and isinstance(node.value.func, ast.Name)
            and node.value.func.id == "compute_best_zero_density"
            and not node.value.args and not node.value.keywords):
        skipped.append(node.lineno)
    else:
        kept.append(node)
if skipped != [1069]:
    raise RuntimeError(f"Unexpected import-time demo position: {skipped}")
tree.body = kept
module = types.ModuleType("paper_time_derived")
module.__file__ = str(SOURCE / "derived.py")
sys.modules[module.__name__] = module
exec(compile(tree, module.__file__, "exec"), module.__dict__)
print("Loaded unchanged recipe definitions; skipped density demo at", skipped, flush=True)

# This adapter repairs the stale final API call, not the mathematical powering
# rule. It retains both separately computed historical projected regions.
def legacy_projection_combine(general, zeta, interval):
    candidates = []
    for hypothesis in (general, zeta):
        candidates.extend((row[0], row[1]) for row in
                          module.ze.compute_sup_LV_on_tau(hypothesis.data.region, interval))
    maximum = module.ze.RF.max(candidates, interval)
    return [
        module.ze.derived_zero_density_energy_estimate(
            module.ze.Zero_Density_Energy_Estimate.from_rational_func(
                row[0] / module.ze.RF([-1, 1]), row[1]),
            "Historical projection replay with an explicit stale-API adapter",
            {general, zeta})
        for row in maximum
    ]

def install_clause_one_adapter():
    import copy
    original = next(node for node in tree.body
                    if isinstance(node, ast.FunctionDef)
                    and node.name == "prove_improved_heath_brown_energy_estimate")
    adapted = copy.deepcopy(original)
    adapted.name = "prove_adapted_heath_brown_energy_estimate"
    domain_replacements = 0
    for node in ast.walk(adapted):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
                and node.func.id == "Interval"
                and ast.unparse(node) == "Interval(frac(3, 4), frac(4, 5))"):
            node.args[1] = ast.parse("frac(5, 6)", mode="eval").body
            domain_replacements += 1
    if domain_replacements != 1:
        raise RuntimeError("Unexpected archived clause-one domain")
    final = adapted.body[-1]
    if (not isinstance(final, ast.Assign)
            or ast.unparse(final.value) !=
            "ze.lver_to_energy_bound(LV_star_hyp, LVZ_star_hyp, Interval(frac(1, 2), 1))"):
        raise RuntimeError("Unexpected archived clause-one final call")
    final.value = ast.parse(
        "_legacy_projection_combine(LV_star_hyp, LVZ_star_hyp, tau0s[0].domain)",
        mode="eval").body
    adapted.body.append(ast.Return(value=ast.Name(id="bounds", ctx=ast.Load())))
    unit = ast.fix_missing_locations(ast.Module(body=[adapted], type_ignores=[]))
    module.__dict__["_legacy_projection_combine"] = legacy_projection_combine
    exec(compile(unit, "<explicit-clause-one-API-adapter>", "exec"), module.__dict__)
    print("ADAPTER: clause-one API repair; public domain [3/4,5/6]; return result.",
          flush=True)

install_clause_one_adapter()

if args.recipes == ["inspect"]:
    for name, value in sorted(vars(module).items()):
        if name.startswith("prove_") and "energy" in name and callable(value):
            print("RECIPE", name)
else:
    import sympy
    from functions import RationalFunction as RF
    for recipe in args.recipes:
        if not recipe.startswith("prove_") or "energy" not in recipe:
            raise ValueError("Only an explicitly named archived energy recipe is permitted.")
        fn = getattr(module, recipe)
        print("RUN", recipe, flush=True)
        result = fn()
        print("RETURN", repr(result), flush=True)
        rows = []
        if result is not None:
            for hypothesis in result:
                data = hypothesis.data
                data._ensure_bound_is_computed()
                expression = sympy.cancel((1-RF.x)*data.bound.num/data.bound.den)
                num, den = sympy.fraction(expression)
                rows.append({
                    "lower": str(data.interval.x0),
                    "upper": str(data.interval.x1),
                    "include_lower": data.interval.include_lower,
                    "include_upper": data.interval.include_upper,
                    "numerator": [str(c) for c in sympy.Poly(num, RF.x).all_coeffs()],
                    "denominator": [str(c) for c in sympy.Poly(den, RF.x).all_coeffs()],
                })
        print("EXACT_ROWS", json.dumps({"recipe": recipe, "rows": rows}, sort_keys=True), flush=True)
