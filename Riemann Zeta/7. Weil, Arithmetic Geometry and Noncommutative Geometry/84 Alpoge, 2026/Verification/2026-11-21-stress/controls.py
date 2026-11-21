"""Replay four Nanoda controls on the prefix ending at the export's first theorem."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile

AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
EXTRA = "Node84InjectedAssumption"


def line(row):
    return json.dumps(row, separators=(",", ":")).encode() + b"\n"


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("solution", type=Path)
    args.add_argument("nanoda", type=Path)
    options = args.parse_args()
    exe = options.nanoda.resolve(strict=True)
    prefix = bytearray()
    prop = None
    last_name = 0
    with options.solution.open("rb") as f:
        for raw in f:
            row = json.loads(raw)
            last_name = max(last_name, row.get("in", 0))
            if prop is None and row.get("sort") == 0:
                prop = row["ie"]
            if "thm" in row:
                break
            prefix.extend(raw)
        else:
            raise ValueError("Export contains no theorem")
    if prop is None or row["thm"]["value"] == prop:
        raise ValueError("Export prefix cannot support this control")

    with tempfile.TemporaryDirectory(prefix="node84-controls-") as tmp:
        folder = Path(tmp)
        data, config = folder/"input.ndjson", folder/"nanoda.json"

        def run(label, allowed, accept, diagnostic):
            config.write_text(json.dumps({
                "export_file_path": str(data), "use_stdin": False,
                "permitted_axioms": allowed, "unpermitted_axiom_hard_error": True,
                "num_threads": 1, "nat_extension": True, "string_extension": True,
                "print_success_message": True, "pp_to_stdout": True,
            }), encoding="utf-8")
            result = subprocess.run([str(exe), str(config)], stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, encoding="utf-8", errors="replace")
            print(f"{label} (exit {result.returncode})\n{result.stdout.strip()}")
            if (result.returncode == 0) != accept or diagnostic not in result.stdout:
                raise RuntimeError(f"Unexpected result for {label}")

        original = bytes(prefix) + raw
        data.write_bytes(original)
        run("Unmodified prefix", AXIOMS, True, "199 declarations")
        row["thm"]["value"] = prop
        data.write_bytes(prefix + line(row))
        run("Wrong proof body", AXIOMS, False, "def_eq")
        fresh = last_name + 1
        data.write_bytes(original + line({"in": fresh, "str": {"pre": 0, "str": EXTRA}})
                         + line({"axiom": {"isUnsafe": False, "levelParams": [],
                                           "name": fresh, "type": prop}}))
        run("Unexpected axiom", AXIOMS, False, 'unpermitted axiom "' + EXTRA + '"')
        run("Explicitly permitted control", AXIOMS + [EXTRA], True, "200 declarations")


if __name__ == "__main__":
    main()
