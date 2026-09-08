# Source provenance

The proof was reorganised from the pinned Lean companion to the paper
*Finite presentations of metabelian groups: effective enumeration via Laurent
relations*. The original companion's 81-file checksum manifest was verified
before exporting its 75 proof modules.

`source-map.json` records each original path and SHA-256 digest alongside its
new path. The reorganisation groups modules by mathematical topic, preserves
existing public namespaces, adds module and declaration documentation, and
adds `Kourovka/Paper.lean` as the principal reading entry point. Source hashes in
that map describe the original snapshot, not the edited files in this repository.
The cleanup also removes redundant simplification arguments and tactics,
uses clearer local names, and drops unused typeclass assumptions from helper
lemmas. The assembled mathematical targets are unchanged. The new checkout
is built and audited separately.

The alternative isomorphism-based enumeration proof remains available.
Boundary examples are in `Tests`, and the proof library does not import them.
No original proof module has been discarded.

## Third-party code

`Kourovka/Schreier` contains four adapted files from ProCGroups at commit
`6933dfe3f376833421ce10e782108b95ac84bda5`. Their existing headers, detailed
provenance and Apache-2.0 licence are retained in `third_party`. Those licence
terms are separate from the repository's existing CC0 dedication.

Mathlib and its dependencies are obtained through Lake at the revisions in
`lake-manifest.json`; they are not vendored here.

## Scope of this repository

This repository contains the proof library, examples, and its documentation.
The manuscript's design assets, working drafts, research downloads and local
build logs are not part of the proof distribution.
