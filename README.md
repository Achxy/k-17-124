# Finite presentations of metabelian groups

Lean 4 formalisation accompanying **Finite presentations of metabelian groups:
effective enumeration via Laurent relations**, by
[Achyuth Jayadevan](https://orcid.org/0009-0008-8745-4078).

For an ordinary finite presentation `P`, the development constructs a
primitive-recursive Boolean predicate `V` satisfying

```text
P is well formed and G(P) is metabelian  ↔  ∃ c ∈ ℕ, V(P, c) = true.
```

Consequently, ordinary finite presentations defining metabelian groups are
recursively enumerable. The group `G(P)` is the quotient of a free group by
the normal closure of its relators. The result concerns presentations in the
variety of all groups.

## Start here

**[The main theorem](Kourovka/Paper.lean)** is the shortest entry point. Its three
public results give primitive recursiveness, certificate correctness, and
recursive enumerability. From there:

1. Read [the input definitions](Kourovka/Presentations/Presentations.lean).
2. Read [the certificate and its proof](Kourovka/Enumeration/EpimorphismEnumeration.lean).
3. Follow [the mathematical reading guide](docs/reading-guide.md) into the algebraic ingredients.

The [paper-to-Lean map](docs/paper-map.md) lists the exact declarations behind
each statement. [Small examples](Tests/PresentationExamples.lean) explain the
alphabet convention and exercise both accepted and rejected inputs.

## Build and verify

Install [Lean via Elan](https://leanprover-community.github.io/get_started.html),
then run:

```sh
git clone https://github.com/Achxy/k-17-124.git
cd k-17-124
lake exe cache get
./scripts/check.sh
```

Open this directory in VS Code with the **Lean 4** extension to inspect goals and definitions.
`lean-toolchain` pins Lean **4.24.0**; `lake-manifest.json` fixes the complete
Mathlib dependency graph. No sibling repository or custom workspace helper is
needed. The first cache download can take several minutes.

`lake build` builds the library and the kernel-checked examples. The full check
also verifies module coverage and runs the transitive axiom audit. Details,
including the exact expanded target, are in [verification](docs/verification.md).

## Organisation

| Directory | Mathematical role |
| --- | --- |
| `Kourovka/Presentations` | Ordinary presentations, kernels, central extensions |
| `Kourovka/Certificates` | Finite word, isomorphism, and epimorphism certificates |
| `Kourovka/Computability` | Encodings, primitive recursion, enumeration |
| `Kourovka/Polyhedral` | Rational elimination, cone coverage, margins |
| `Kourovka/Covers` | Finite Laurent presentations and their soundness |
| `Kourovka/Collection` | Reordering words inside a finite radius |
| `Kourovka/Modules` | Conjugation modules and signed Laurent relations |
| `Kourovka/Halfspaces` | The finite-presentation necessity argument |
| `Kourovka/Cofinality` | Covers surjecting onto every finitely presented metabelian group |
| `Kourovka/Enumeration` | Assembly of the certificate theorem |
| `Kourovka/Schreier` | Adapted Reidemeister-Schreier infrastructure |
| `Tests` | Expanded theorem statements and explicit boundary examples |

Namespaces are preserved from the paper companion. The shorter epimorphism
route is the primary reading path; the original isomorphism route remains
available and is also audited.

## Attribution and contributions

The repository's existing [CC0 licence](LICENSE) applies to the original work.
The four adapted Schreier modules retain their Apache-2.0 terms and attribution;
see [third-party provenance](third_party/ProCGroups-PROVENANCE.md).
[Source provenance](docs/provenance.md) records the reorganisation.

See [CONTRIBUTING.md](CONTRIBUTING.md) for proof and documentation conventions,
and [CITATION.cff](CITATION.cff) for citation metadata.
