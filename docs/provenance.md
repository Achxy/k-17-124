# Source provenance

The initial export came from the pinned Lean companion to *Finite presentations
of metabelian groups: effective enumeration via Laurent relations*. Its 81-file
checksum manifest was verified before the 75 proof modules were imported.

`source-map.json` records the original paths and SHA-256 digests of the retained
sources. These digests describe the original snapshot, not subsequent edits.
The files are grouped by mathematical topic. The complete enumeration targets
are checked separately in `Tests/Completion.lean`.

## Schreier implementation

The current Schreier proof is implemented in three modules:

- [Transversal](../Kourovka/Schreier/Transversal.lean): normalized coset sections and edges.
- [PathLifting](../Kourovka/Schreier/PathLifting.lean): group-valued path lifting,
  free-reduction invariance, the cocycle identity, and evaluation.
- [KernelPresentation](../Kourovka/Schreier/KernelPresentation.lean): inverse
  homomorphisms between the Schreier presentation and the subgroup relator quotient.

The implementation uses Mathlib's free-group and quotient-group APIs.
Its presentation has two relator families: lifts of original relators and
section-path relations. An arbitrary normalized transversal suffices.

These modules replace the four files initially adapted from ProCGroups.
The adapted proof modules are no longer included or imported. Original source
records are retained under `replaced_sources` in `source-map.json`. The former
code, licence and attribution remain in Git history at commit
`5627cc84341985db2708f408cc80203fba33fdd8`.

## Dependencies and distribution

Mathlib and its dependencies are obtained through Lake at the revisions in
`lake-manifest.json`; they are not vendored here. The repository's code is
covered by its existing CC0 dedication.

Both enumeration proofs and the boundary examples remain included. The proof
library does not import the examples. Manuscript assets, working drafts,
research downloads and build logs are outside the proof distribution.
