# Contributing

Start with `Kourovka/Paper.lean` and `docs/reading-guide.md`. For a proof change,
first identify which named mathematical statement it affects.

## Local workflow

1. Use the pinned toolchain and manifest. Run `lake exe cache get` after cloning.
2. Make a focused change in the relevant mathematical directory.
3. Build the affected module, then run `./scripts/check.sh`.
4. Update the paper map if a public statement or source path changes.

## Lean style

Use two-space indentation and aim for lines of at most 100 characters, following
[Lean community conventions](https://leanprover-community.github.io/contribute/style.html).
Keep declarations flush left within namespaces. Use mathematical names and
explicit types, add docstrings to public definitions and substantive theorems,
and explain the purpose of a difficult proof step rather than narrating tactics.
Prefer small supporting lemmas when they expose a reusable mathematical fact.
Avoid renaming stable public declarations solely for cosmetic consistency.

Module docstrings should identify the construction, its main results, and its
place in the proof. Preserve the distinction between an ordered word and its
literal inverse, and between total decoding and input well-formedness.
The code targets Lean 4.24.0; newer module-system syntax should not be introduced
without a separately reviewed toolchain update.

## Proof requirements

Do not weaken the main target or add assumptions to obtain a successful build.
Use kernel-checked proofs; `sorry`, extra axioms, `native_decide`, and unsafe
shortcuts are not accepted. Keep source checks and the transitive audit enabled.
Tests should exercise a mathematical boundary or a theorem statement, not merely
repeat a definition's implementation.

Keep generated files and caches out of Git. Retain upstream notices in adapted
Schreier sources. Document changes to encodings, statement hypotheses or
computability claims so reviewers can assess their mathematical effect.
