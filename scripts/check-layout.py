#!/usr/bin/env python3
"""Check source organisation and coverage before invoking Lean.

This is a repository hygiene check. Audit.lean is responsible for transitive
proof dependencies; the Python check is not a substitute for kernel checking.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]


def code_only(source: str) -> str:
    """Mask nested Lean comments and string literals, retaining line boundaries."""
    result = []
    position = 0
    depth = 0
    in_string = False
    while position < len(source):
        pair = source[position:position + 2]
        char = source[position]
        if depth:
            if pair == "/-":
                depth += 1
                result.append("  ")
                position += 2
                continue
            if pair == "-/":
                depth -= 1
                result.append("  ")
                position += 2
                continue
            result.append("\n" if char == "\n" else " ")
        elif in_string:
            if char == "\\":
                result.append("  ")
                position += 2
                continue
            if char == '"':
                in_string = False
            result.append("\n" if char == "\n" else " ")
        elif pair == "/-":
            depth = 1
            result.append("  ")
            position += 2
            continue
        elif pair == "--":
            end = source.find("\n", position)
            end = len(source) if end == -1 else end
            result.append(" " * (end - position))
            position = end
            continue
        elif char == '"':
            in_string = True
            result.append(" ")
        else:
            result.append(char)
        position += 1
    if depth or in_string:
        raise ValueError("Unterminated comment or string")
    return "".join(result)


def main() -> None:
    files = [ROOT / "Kourovka.lean", ROOT / "Tests.lean", ROOT / "Audit.lean"]
    files += sorted((ROOT / "Kourovka").rglob("*.lean"))
    files += sorted((ROOT / "Tests").rglob("*.lean"))
    modules = {".".join(path.relative_to(ROOT).with_suffix("").parts): path for path in files}
    imports = {}
    failures = []
    forbidden = re.compile(r"\b(?:sorry|admit|axiom|unsafe|native_decide)\b")
    for module, path in modules.items():
        source = path.read_text()
        if not source.endswith("\n") or any(line.rstrip() != line for line in source.splitlines()):
            failures.append(f"{path.relative_to(ROOT)}: final newline or trailing whitespace")
        if "/-!" not in source:
            failures.append(f"{module}: missing module documentation")
        code = code_only(source)
        if forbidden.search(code):
            failures.append(f"{module}: forbidden proof placeholder or trust shortcut")
        if re.search(r"set_option\s+debug\.skipKernelTC\s+true", code):
            failures.append(f"{module}: kernel checking disabled")
        imports[module] = re.findall(r"(?m)^import\s+([\w.]+)", code)
        for dependency in imports[module]:
            if dependency.startswith(("Kourovka", "Tests")) and dependency not in modules:
                failures.append(f"{module}: missing local import {dependency}")
            if module.startswith("Kourovka") and dependency.startswith("Tests"):
                failures.append(f"{module}: the proof library must not import Tests")
    visited = set()
    active = set()

    def visit(module: str) -> None:
        if module in active:
            failures.append(f"Cyclic local import: {module}")
            return
        if module in visited:
            return
        active.add(module)
        for dependency in imports.get(module, []):
            if dependency in modules:
                visit(dependency)
        active.remove(module)
        visited.add(module)

    visit("Audit")
    for module in sorted(set(modules) - visited):
        failures.append(f"{module}: not reached by the library-wide audit")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for dependency in manifest["packages"]:
        if dependency.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", dependency["rev"]):
            failures.append(f"Unpinned dependency: {dependency['name']}")
    for record in json.loads((ROOT / "docs/source-map.json").read_text())["files"]:
        if not (ROOT / record["destination"]).is_file():
            failures.append(f"Missing preserved module: {record['destination']}")
    if failures:
        raise SystemExit("\n".join(failures))
    print(f"Layout passed: {len(modules)} Lean modules; all reached by the audit; dependencies pinned.")


if __name__ == "__main__":
    main()
