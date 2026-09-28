#!/usr/bin/env python3
"""Replay the frozen ANTEDB computations, never mathematical proof.

The archive contains the disproved five-coordinate powering transformation.
These results are historical computational evidence only. The independent Lean
proofs and preserved counterexample remain the mathematical authority.
"""
from __future__ import annotations

import argparse
import ast
import contextlib
import copy
from fractions import Fraction
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import sys
import tempfile
import traceback
import types
import zipfile

TOOLS = Path(__file__).resolve().parent
PROJECT = TOOLS.parent
sys.path.insert(0, str(TOOLS))
from generate_certificates import (ARCHIVE_SHA256, extract_energy_clauses,
                                   extract_pairs, extract_bourgain_candidates,
                                   bourgain_pieces)

RECIPES = [
    "prove_adapted_heath_brown_energy_estimate",
    "prove_zero_density_energy_2",
    "prove_zero_density_energy_8",
    "prove_zero_density_energy_9",
    "prove_zero_density_energy_10",
    "prove_zero_density_energy_4",
    "prove_zero_density_energy_5",
    "prove_zero_density_energy_6",
    "prove_zero_density_energy_7",
]


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def verify_installed_archive(archive, installed, wheel=False):
    """Check imported bytes, not just distribution version metadata."""
    with zipfile.ZipFile(archive) as source:
        for item in source.infolist():
            if item.is_dir():
                continue
            relative = Path(item.filename)
            if relative.is_absolute() or ".." in relative.parts:
                raise RuntimeError("Unsafe installed archive member")
            if wheel and relative.name == "RECORD" and relative.parent.suffix == ".dist-info":
                # Pip records relocated/generated launcher files in this ledger.
                continue
            if wheel and relative.parts[0].endswith(".data"):
                kind = relative.parts[1]
                if kind in ("purelib", "platlib"):
                    relative = Path(*relative.parts[2:])
                elif kind in ("scripts", "headers", "data"):
                    # Launchers/headers are not imported by this computation.
                    continue
                else:
                    raise RuntimeError(f"Unknown wheel relocation: {item.filename}")
            target = installed / relative
            if not target.is_file() or target.read_bytes() != source.read(item):
                raise RuntimeError(f"Installed runtime/package byte mismatch: {target}")


def verify_environment(runtime):
    lock = json.loads((TOOLS / "paper_time_environment.json").read_text("utf-8"))
    if platform.python_version() != lock["python"]["version"]:
        raise RuntimeError("Use the pinned isolated Python runtime, not system Python.")
    if sys.platform != "win32":
        raise RuntimeError("This reproduction environment is pinned for Windows x86-64.")
    if Path(sys.executable).resolve() != (runtime / "python/python.exe").resolve():
        raise RuntimeError("The executing interpreter is not the pinned runtime executable.")
    sys.path.insert(0, str(runtime / "site-packages"))
    for name, version in lock["packages"].items():
        if importlib.metadata.version(name) != version:
            raise RuntimeError(f"Environment version mismatch: {name}")
    for wheel in lock["wheels"]:
        if digest(runtime / "wheels" / wheel["file"]) != wheel["sha256"]:
            raise RuntimeError(f"Wheel checksum mismatch: {wheel['file']}")
        verify_installed_archive(runtime / "wheels" / wheel["file"],
                                 runtime / "site-packages", wheel=True)
    if digest(runtime / lock["python"]["file"]) != lock["python"]["sha256"]:
        raise RuntimeError("Python archive checksum mismatch")
    verify_installed_archive(runtime / lock["python"]["file"], runtime / "python")
    return lock


class DiagnosticTee:
    def __init__(self, console, log):
        self.console, self.log = console, log

    def write(self, value):
        self.console.write(value)
        self.log.write(value)
        return len(value)

    def flush(self):
        self.console.flush()
        self.log.flush()


def load_archive(archive, destination):
    if digest(archive) != ARCHIVE_SHA256:
        raise RuntimeError("Frozen ANTEDB archive checksum mismatch")
    prefix = "expdb-9953003/blueprint/src/"
    with zipfile.ZipFile(archive) as source:
        for item in source.infolist():
            if not item.filename.startswith(prefix):
                continue
            relative = Path(item.filename.removeprefix(prefix))
            if relative.is_absolute() or ".." in relative.parts:
                raise RuntimeError("Unsafe archive member")
            if item.is_dir():
                continue
            if relative.as_posix() == "references.bib" or (
                    relative.parts[0] == "python" and relative.suffix == ".py"):
                target = destination / relative
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(source.read(item))
    source_root = destination / "python"
    sys.path.insert(0, str(source_root))
    filename = source_root / "derived.py"
    tree = ast.parse(filename.read_text("utf-8"), filename=str(filename))
    skipped, kept = [], []
    for node in tree.body:
        if (isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
                and ast.dump(node.value, include_attributes=False) ==
                ast.dump(ast.parse("compute_best_zero_density()", mode="eval").body,
                         include_attributes=False)):
            skipped.append(node.lineno)
        else:
            kept.append(node)
    if skipped != [1069]:
        raise RuntimeError(f"Unexpected import-time density demo: {skipped}")
    tree.body = kept
    module = types.ModuleType("paper_time_derived")
    module.__file__ = str(filename)
    sys.modules[module.__name__] = module
    exec(compile(tree, str(filename), "exec"), module.__dict__)
    install_clause_one_adapter(module, tree)
    return module


def install_clause_one_adapter(module, tree):
    # The frozen driver computes two projected regions, then calls a newer
    # hypotheses/tau0 API with the old region/region signature. Reuse the
    # frozen projection and supremum routines, and the blueprint's full domain.
    def combine(general, zeta, interval):
        candidates = []
        for hypothesis in (general, zeta):
            candidates.extend((row[0], row[1]) for row in
                module.ze.compute_sup_LV_on_tau(hypothesis.data.region, interval))
        return [
            module.ze.derived_zero_density_energy_estimate(
                module.ze.Zero_Density_Energy_Estimate.from_rational_func(
                    row[0] / module.ze.RF([-1, 1]), row[1]),
                "Historical replay with an explicit stale-API adapter", {general, zeta})
            for row in module.ze.RF.max(candidates, interval)
        ]

    original = next(node for node in tree.body if isinstance(node, ast.FunctionDef)
                    and node.name == "prove_improved_heath_brown_energy_estimate")
    adapted = copy.deepcopy(original)
    adapted.name = RECIPES[0]
    replacements = 0
    for node in ast.walk(adapted):
        if (isinstance(node, ast.Call) and
                ast.unparse(node) == "Interval(frac(3, 4), frac(4, 5))"):
            node.args[1] = ast.parse("frac(5, 6)", mode="eval").body
            replacements += 1
    if replacements != 1:
        raise RuntimeError("Unexpected archived clause-one domain")
    final = adapted.body[-1]
    if (not isinstance(final, ast.Assign) or ast.unparse(final.value) !=
            "ze.lver_to_energy_bound(LV_star_hyp, LVZ_star_hyp, Interval(frac(1, 2), 1))"):
        raise RuntimeError("Unexpected archived clause-one final call")
    final.value = ast.parse(
        "_legacy_projection_combine(LV_star_hyp, LVZ_star_hyp, tau0s[0].domain)",
        mode="eval").body
    adapted.body.append(ast.Return(value=ast.Name(id="bounds", ctx=ast.Load())))
    unit = ast.fix_missing_locations(ast.Module(body=[adapted], type_ignores=[]))
    module.__dict__["_legacy_projection_combine"] = combine
    exec(compile(unit, "<explicit-clause-one-API-adapter>", "exec"), module.__dict__)


def exact(value):
    import sympy as sp
    result = sp.sympify(value)
    if result.has(sp.Float):
        raise RuntimeError(f"Inexact arithmetic in replay result: {value}")
    return result


def formula(data, energy=False):
    import sympy as sp
    from functions import RationalFunction as RF
    data._ensure_bound_is_computed()
    result = sp.cancel(data.bound.num / data.bound.den * ((1 - RF.x) if energy else 1))
    if result.has(sp.Float):
        raise RuntimeError("Inexact rational function")
    return result


def coefficients(expression):
    import sympy as sp
    from functions import RationalFunction as RF
    num, den = sp.fraction(sp.cancel(expression))
    return {
        "numerator": [str(v) for v in sp.Poly(num, RF.x).all_coeffs()],
        "denominator": [str(v) for v in sp.Poly(den, RF.x).all_coeffs()],
    }


def dominates(actual, other, lo, hi):
    """Exact polynomial critical-point comparison, not floating sampling."""
    import sympy as sp
    from functions import RationalFunction as RF
    num, den = sp.fraction(sp.cancel(actual - other))
    roots = []
    for polynomial in (num, den, sp.denom(actual), sp.denom(other)):
        if polynomial == 0:
            continue
        for root in sp.solve(polynomial, RF.x):
            root = exact(root)
            if root.is_real and bool(lo <= root) and bool(root <= hi):
                roots.append(root)
    points = sorted(set([lo, hi, *roots]))
    for point in points:
        if sp.denom(actual).subs(RF.x, point) == 0 or sp.denom(other).subs(RF.x, point) == 0:
            raise RuntimeError("Pole in compared closed interval")
    samples = points + [(a + b) / 2 for a, b in zip(points, points[1:])]
    for point in samples:
        if not bool(sp.simplify((actual - other).subs(RF.x, point)) >= 0):
            return False
    return True


def verify_energy(result, spec):
    import sympy as sp
    from functions import RationalFunction as RF
    label, lower, upper, bounds = spec
    lo, hi = exact(lower), exact(upper)
    candidates = [sp.cancel((a * RF.x + b) / (c * RF.x + d))
                  for a, b, c, d in bounds]
    rows, cursor = [], lo
    matched = set()
    envelope_equal = True
    for hypothesis in result:
        data = hypothesis.data
        left = max(lo, exact(data.interval.x0))
        right = min(hi, exact(data.interval.x1))
        if not bool(left < right):
            continue
        if sp.simplify(left - cursor) != 0:
            raise RuntimeError(f"Missing or overlapping interval in {label}")
        value = formula(data, energy=True)
        matches = {i for i, candidate in enumerate(candidates)
                   if sp.cancel(value - candidate) == 0}
        if not matches:
            raise RuntimeError(f"Unexpected formula in {label}: {value}")
        matched.update(matches)
        for candidate in candidates:
            envelope_equal = dominates(value, candidate, left, right) and envelope_equal
        encoded = coefficients(value)
        if rows and all(rows[-1][key] == encoded[key] for key in encoded):
            # Archived polytope iteration can insert redundant internal cuts.
            # Coverage was checked above; merge only the exact same function.
            rows[-1]["upper"] = str(right)
        else:
            rows.append({"lower": str(left), "upper": str(right), **encoded})
        cursor = right
    if cursor != hi:
        raise RuntimeError(f"Incomplete public domain in {label}")
    if matched != set(range(len(candidates))):
        raise RuntimeError(f"Not all printed branches were reproduced in {label}")
    return {"source_label": label, "lower": str(lo), "upper": str(hi),
            "endpoint_convention": "continuous extension of archived half-open cells",
            "public_bounds": [coefficients(candidate) for candidate in candidates],
            "envelope_relation": ("equal" if envelope_equal else
                "public maximum relaxes the replayed piecewise envelope"),
            "rows": rows}



def checker_regressions(module):
    """Reject inexact, incomplete, or altered data; retain strict relaxation."""
    import sympy as sp
    from functions import RationalFunction as RF

    count = 0

    def require_failure(action, expected):
        nonlocal count
        try:
            action()
        except RuntimeError as error:
            if expected not in str(error):
                raise
        else:
            raise RuntimeError("A negative replay regression unexpectedly passed")
        count += 1

    def row(expression, lo, hi):
        return types.SimpleNamespace(data=module.ze.Zero_Density_Energy_Estimate.from_rational_func(
            RF.parse(str(expression / (1 - RF.x))), module.Interval(lo, hi)))

    test_spec = ("test-max", Fraction(0), Fraction(1),
                 [(1, 0, 0, 1), (-1, 1, 0, 1)])
    good = [row(1 - RF.x, 0, Fraction(1, 2)), row(RF.x, Fraction(1, 2), 1)]
    if verify_energy(good, test_spec)["envelope_relation"] != "equal":
        raise RuntimeError("Exact max regression failed")
    count += 1
    split_good = [good[0], row(RF.x, Fraction(1, 2), Fraction(3, 4)),
                  row(RF.x, Fraction(3, 4), 1)]
    if verify_energy(split_good, test_spec) != verify_energy(good, test_spec):
        raise RuntimeError("Redundant partition changed canonical exact data")
    count += 1
    require_failure(lambda: exact(sp.Float("0.1")), "Inexact")
    require_failure(lambda: verify_energy(good[:1], test_spec), "Incomplete")
    require_failure(lambda: verify_energy(
        [row(2 - RF.x, 0, Fraction(1, 2)), good[1]], test_spec), "Unexpected formula")
    require_failure(lambda: verify_energy(
        [row(1 - RF.x, 0, Fraction(1, 3)), good[1]], test_spec), "Missing or overlapping")
    require_failure(lambda: dominates(1 / (RF.x - 1), 0 * RF.x, 0, 1), "Pole")

    # This exact failure of equality was found by the first strict replay.
    sigma = sp.Rational(373, 493)
    first = (730 * sigma - 533) / (1050 * sigma - 780)
    second = (-99 * sigma + 78) / (85 * sigma - 62)
    if sp.cancel(second - first) != sp.Rational(12551, 8098290):
        raise RuntimeError("Clause-five strict-relaxation witness changed")
    count += 1
    reversed_rows = [row(RF.x, 0, Fraction(1, 2)), row(1 - RF.x, Fraction(1, 2), 1)]
    if verify_energy(reversed_rows, test_spec)["envelope_relation"] != (
            "public maximum relaxes the replayed piecewise envelope"):
        raise RuntimeError("Strict relaxation was incorrectly labelled equality")
    count += 1
    return count


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--archive", type=Path,
                        default=PROJECT / "Sources/antedb-expdb-paper-time-9953003.zip")
    parser.add_argument("--log", required=True, type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    if args.output is None and args.check is None:
        parser.error("Provide --output and/or --check")
    sys.dont_write_bytecode = True
    sys.stdout.reconfigure(encoding="utf-8")
    sys.stderr.reconfigure(encoding="utf-8")
    runtime = args.runtime.resolve(strict=True)
    lock = verify_environment(runtime)
    os.environ["MPLBACKEND"] = "Agg"
    os.environ["MPLCONFIGDIR"] = str(runtime / "matplotlib-cache")
    print("HISTORICAL REPRODUCTION ONLY; the archived powering rule is false.", flush=True)
    print(f"Full computation transcript: {args.log}", flush=True)
    with args.log.open("x", encoding="utf-8", newline="\n") as log, \
            contextlib.redirect_stderr(DiagnosticTee(sys.stderr, log)):
        try:
            with tempfile.TemporaryDirectory(prefix="epzae-source-", dir=runtime) as temp:
                with contextlib.redirect_stdout(log):
                    module = load_archive(args.archive, Path(temp))
                    regression_count = checker_regressions(module)
                print(f"PASS: {regression_count} exact replay-checker regressions", flush=True)
                report = {"schema": 1, "proof_evidence": False,
                          "archive_sha256": ARCHIVE_SHA256,
                          "checker_regressions": regression_count,
                          "environment": {"python": lock["python"]["version"],
                                          "packages": lock["packages"]},
                          "adaptations": [
                              "Skip unrelated import-time compute_best_zero_density demo.",
                              "Clause 1: repair stale projection API, return output, "
                              "use blueprint domain [3/4,5/6].",
                              "Restrict replay cells to the nine public clause domains.",
                              "Closed endpoints compared by continuous rational extension.",
                              "Coalesce contiguous cells only when their exact rational functions coincide.",
                              "Reconstruct the printed maximum from exactly the replayed "
                              "branches; explicitly report any strict relaxation."],
                          "energy": [], "exponent_pair_coordinates": []}
                specs = extract_energy_clauses(args.archive)
                for recipe, spec in zip(RECIPES, specs, strict=True):
                    print(f"REPLAY {recipe}", flush=True)
                    with contextlib.redirect_stdout(log):
                        result = getattr(module, recipe)()
                        verified = verify_energy(result, spec)
                    report["energy"].append(verified)
                    print(f"PASS: exact branches/domain for {spec[0]}; "
                          f"{verified['envelope_relation']}", flush=True)
                for kn, kd, ln, ld in extract_pairs(args.archive):
                    k, ell = Fraction(kn, kd), Fraction(ln, ld)
                    print(f"REPLAY archived pair discovery ({k},{ell})", flush=True)
                    with contextlib.redirect_stdout(log):
                        result = module.prove_exponent_pair(k, ell, simplify_deps=False,
                                                           verbose=False)
                    if result is None or result.data.k != k or result.data.l != ell:
                        raise RuntimeError(f"Archived pair discovery failed: {(k, ell)}")
                    report["exponent_pair_coordinates"].append([str(k), str(ell)])
                # Existing exact generator selects the eight public candidates.
                # This is coefficient/interval reproduction, not pair provenance.
                report["bourgain_pieces"] = [
                    {"candidate": index, "k": str(k), "ell": str(ell),
                     "lower": str(lo), "upper": str(hi),
                     "numerator": bound[0], "denominator_slope": bound[1],
                     "denominator_constant": bound[2]}
                    for index, k, ell, lo, hi, bound in
                    bourgain_pieces(extract_bourgain_candidates(args.archive))]
        except BaseException:
            traceback.print_exc(file=log)
            raise
    content = json.dumps(report, indent=2, sort_keys=True, ensure_ascii=True) + "\n"
    if args.output:
        with args.output.open("x", encoding="utf-8", newline="\n") as output:
            output.write(content)
    if args.check and args.check.read_bytes() != content.encode("utf-8"):
        raise RuntimeError("Replay is not byte-identical to the reference data")
    print("REPRODUCTION PASS: nine energy envelopes, four discovered coordinates, "
          "eight rational density pieces. This is not a Lean proof.", flush=True)


if __name__ == "__main__":
    main()
