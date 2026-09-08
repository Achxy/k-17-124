# Verification

Run `./scripts/check.sh` from a checkout with Elan and Python 3 available.
The script has three stages:

1. Check the source layout, local import graph, and coverage of every proof module.
2. Build `Kourovka` and `Tests` with the pinned Lean toolchain; warnings fail the check.
3. Run `Audit.lean`, which traverses the dependencies of every declaration in
   the `Kourovka` and `Tests` namespaces, including their private declarations.

The audit accepts only `propext`, `Classical.choice`, and `Quot.sound`.
An admitted proof introduces `sorryAx` and fails the audit. The source-layout
check also rejects proof placeholders, unsafe declarations, native decision
shortcuts, and local axiom declarations in the proof sources.

`Tests/Completion.lean` checks both assembled enumeration routes against an
expanded statement about ordinary `PresentedGroup` quotients. The default build
includes this file, the cone boundary examples, and the presentation examples.

The result is a proof of the formal statements. Correspondence with the paper's
natural-language exposition is documented separately in `paper-map.md`.

## Reproduction

```sh
lake exe cache get
./scripts/check.sh
```

`lake exe cache get` fetches published artifacts for external dependencies;
project proof artifacts are built in this checkout's `.lake/build` directory.
The manifest and toolchain are versioned, and neither is upgraded by the check.
A clean clone requires network access to obtain the pinned dependencies.

For a focused edit:

```sh
lake build Kourovka.Enumeration.EpimorphismEnumeration
./scripts/check.sh
```

CI uses the same full check. It does not run on a schedule and has read-only
repository permissions. A passing CI status concerns the commit it checked.
