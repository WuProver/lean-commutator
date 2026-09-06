#!/usr/bin/env python3
"""Build, check the expanded main statement, and audit its full axiom dependency closure."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
from datetime import datetime, timezone

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lake", default="lake", help="Lake executable for the pinned toolchain")
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
out = root / "verification"
out.mkdir(exist_ok=True)
env = os.environ.copy()
lake_path = Path(args.lake)
if lake_path.is_absolute():
    env["PATH"] = str(lake_path.parent) + os.pathsep + env.get("PATH", "")
commands = [
    ("build.log", [args.lake, "build", "CommutatorTheorem.NoEpsilon"]),
    ("axioms.log", [args.lake, "env", "lean", "CommutatorTheorem/NoEpsilon/AxiomAudit.lean"]),
    ("main_statement.log", [args.lake, "env", "lean", "CommutatorTheorem/NoEpsilon/FinalVerification.lean"]),
]
results = []
for filename, command in commands:
    result = subprocess.run(command, cwd=root, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (out / filename).write_text(result.stdout)
    print(f"{filename}: exit {result.returncode}", flush=True)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    results.append({"command": command, "exit_code": result.returncode, "log": filename})
audit = (out / "axioms.log").read_text()
dependencies = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", audit)
if not dependencies:
    raise SystemExit("No axiom audit declarations recognized; inspect axioms.log")
allowed = {"propext", "Classical.choice", "Quot.sound"}
checked = []
for name, axioms in dependencies:
    names = {x.strip() for x in axioms.split(",") if x.strip()}
    if not names <= allowed:
        raise SystemExit(f"Unexpected axiom dependencies for {name}: {sorted(names - allowed)}")
    checked.append({"declaration": name, "axioms": sorted(names)})
main_name = "NoEpsilon.uniformCommutatorBound"
if main_name not in {item["declaration"] for item in checked}:
    raise SystemExit("The complete main theorem is missing from the axiom audit")
main_audit = (out / "main_statement.log").read_text()
if not re.search(r"'NoEpsilon\.uniformCommutatorBound' depends on axioms:", main_audit):
    raise SystemExit("The expanded main-statement check did not audit the main theorem")
source_files = [root / "CommutatorTheorem/NoEpsilon.lean",
                *sorted((root / "CommutatorTheorem/NoEpsilon").glob("*.lean"))]
import hashlib
source_hashes = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in source_files if p.exists()}
record = {
    "verified_at_utc": datetime.now(timezone.utc).isoformat(),
    "scope": "Complete NoEpsilon theorem, expanded original statement, Euclidean norm, and components",
    "full_UniformCommutatorBound_proved": True,
    "main_declaration": main_name,
    "lean_toolchain": (root / "lean-toolchain").read_text().strip(),
    "commands": results,
    "checked_declarations": checked,
    "source_sha256": source_hashes,
}
(out / "results.json").write_text(json.dumps(record, indent=2) + "\n")
print(f"Audited {len(checked)} declarations: only standard logical axioms.")
print("The full UniformCommutatorBound and its expanded statement passed kernel checking.")
