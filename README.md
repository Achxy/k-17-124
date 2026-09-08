# Finite presentations of metabelian groups

Lean 4 formalisation accompanying **Finite presentations of metabelian groups:
effective enumeration via Laurent relations**, by
[Achyuth Jayadevan](https://orcid.org/0009-0008-8745-4078).

## Finite presentations and their encoding

The input type is

```math
\mathcal P=\mathbb N\times
\mathrm{List}\bigl(\mathrm{List}(\mathbb N\times\mathrm{Bool})\bigr).
```

An element $P=(n,R)$ specifies $n$ generators and a finite list of relator
words. A letter $(i,\mathrm{true})$ denotes $x_i$, and
$(i,\mathrm{false})$ denotes $x_i^{-1}$. Indices start at zero. In
[Presentations.lean](Kourovka/Presentations/Presentations.lean),

```math
\begin{aligned}
\mathrm{WF}(P)
&\iff \forall w\in R\;\forall(i,\varepsilon)\in w,\quad i<n,\\
G(P)
&=F(x_0,\ldots,x_{n-1})\big/\langle\!\langle
\mathrm{interpretWord}_n(R)\rangle\!\rangle.
\end{aligned}
```

`GroupOf` uses Mathlib's `PresentedGroup`: the quotient of the ordinary free
group by the normal closure of the relators. `interpretWord` assigns the
identity to an out-of-range letter; `WellFormed` excludes such letters from
accepted presentations.

The natural-number decoder $d:\mathbb N\to\mathcal P$ satisfies

```math
d(\mathrm{encode}(P))=P.
```

It is total: a failed decode returns $(0,[])$, the empty presentation of the
trivial group. Successfully decoded presentations must still satisfy
$\mathrm{WF}$.

## The theorem checked by Lean

The group property is the identity

```math
\mathrm{Met}(G)
\iff
\forall a,b,c,d\in G,\quad
[a,b][c,d]=[c,d][a,b],
\qquad [a,b]=aba^{-1}b^{-1}.
```

Define

```math
\mathcal M=\{m\in\mathbb N:
\mathrm{WF}(d(m))\ \land\ \mathrm{Met}(G(d(m)))\}.
```

The formalisation constructs a primitive-recursive Boolean predicate

```math
V:\mathbb N\times\mathbb N\longrightarrow\mathrm{Bool}
```

and proves

```math
\forall m\in\mathbb N,\qquad
m\in\mathcal M\ \iff\ \exists c\in\mathbb N,\quad V(m,c)=\mathrm{true}.
```

Consequently, $\mathcal M$ is recursively enumerable. The declarations in
[Paper.lean](Kourovka/Paper.lean) are:

```lean
abbrev certificateCheck : ℕ → ℕ → Bool := EpimorphismEnumeration.check

theorem certificateCheck_primrec : Primrec₂ certificateCheck :=
  EpimorphismEnumeration.check_primrec

theorem metabelian_iff_certificate (p : ℕ) :
    DefinesMetabelian p ↔ ∃ c : ℕ, certificateCheck p c = true :=
  EpimorphismEnumeration.check_correct p

theorem metabelian_presentations_re : REPred DefinesMetabelian :=
  EpimorphismEnumeration.kourovka_17_124_via_epimorphisms
```

Here `DefinesMetabelian m` is exactly
`WellFormed (decodePresentation m) ∧ Metabelian (GroupOf (decodePresentation m))`.
[Completion.lean](Tests/Completion.lean) also checks the recursive-enumerability
statement with these definitions expanded to ordinary presented groups and
four universally quantified group elements.

## The finite certificate

A decoded certificate is $((\mathcal D,r),e)$. The datum $\mathcal D$ consists
of a positive lattice rank $k$, a positive kernel alphabet size $a$, designated
commutator generators, and a finite list of signed, ordered Laurent term lists.
The number $r\in\mathbb N$ specifies a dyadic cone margin, and $e\in\mathbb N$
encodes an epimorphism certificate.

For the decoded exponent vectors, set

```math
\begin{aligned}
D(\mathcal D)
&=1+\sum_{\lambda}\sum_{(u,c)\in\lambda}\|u\|_1,\\
\rho(\mathcal D,r)
&=1+2k\bigl(1+D(\mathcal D)+D(\mathcal D)^2k2^r\bigr).
\end{aligned}
```

The sums count listed terms with multiplicity. Terms may have repeated
exponents or zero coefficients; exponent lists are padded with zeros or
truncated to $k$ coordinates. The equality of this integer formula with the
geometric radius is proved in
[ComputableCoverData.lean](Kourovka/Covers/ComputableCoverData.lean).

The ordinary finite cover presentation $Q_{\mathcal D,\rho}$ has generators
$t_0,\ldots,t_{k-1},z_0,\ldots,z_{a-1}$. Write
$q(u)=t_0^{u_0}\cdots t_{k-1}^{u_{k-1}}$,
$x^w=w^{-1}xw$, and $[x,y]_{\mathrm r}=x^{-1}y^{-1}xy$.
Its relators are

```math
\begin{aligned}
\left[t_i,t_j\right]_{\mathrm r}&=z_{A(i,j)} &&(i<j),\\
\left[z_i,z_j^{q(v)}\right]_{\mathrm r}&=1 &&(\|v\|_2^2<\rho^2),\\
z_i&=\prod_{(u,c)\in\lambda}(z_i^c)^{q(u)}
&& (\lambda\text{ signed }+),\\
z_i&=\prod_{(u,c)\in\lambda}(z_i^c)^{q(u)^{-1}}
&& (\lambda\text{ signed }-).
\end{aligned}
```

Each product follows the term-list order. In particular, $q(u)^{-1}$ is the
literal inverse of the ordered word. These are the definitions in
[FiniteCover.lean](Kourovka/Covers/FiniteCover.lean).

Let $C(\mathcal D,r)$ denote the Boolean cone-margin check and
$E(Q,P,e)$ the Boolean epimorphism check. The structured predicate is

```math
\begin{aligned}
\mathrm{checkData}(P,((\mathcal D,r),e))
&=\mathrm{WF}(P)\land(n=0\lor B),\\
B&=C(\mathcal D,r)\land E(Q_{\mathcal D,\rho(\mathcal D,r)},P,e).
\end{aligned}
```

where propositions on the right are evaluated as Booleans. Finally,
$V(m,c)=\mathrm{checkData}(d(m),\mathrm{decodeCertificate}(c))$.
These are the definitions `checkData` and `check` in
[EpimorphismEnumeration.lean](Kourovka/Enumeration/EpimorphismEnumeration.lean).

## Soundness, completeness, and effectivity

**Soundness.** A successful cone check gives

```math
C(\mathcal D,r)=\mathrm{true}
\quad\Longrightarrow\quad
\mathrm{Met}(G(Q_{\mathcal D,\rho(\mathcal D,r)})).
```

[CoverSoundness.lean](Kourovka/Covers/CoverSoundness.lean) proves this by
collection and strict decrease of squared lattice norms. An accepted
epimorphism certificate gives a surjection onto $G(P)$, so the metabelian
identity descends to $G(P)$. The zero-generator case is handled directly.

**Completeness.** [Cofinality.lean](Kourovka/Cofinality/Cofinality.lean) proves
that every finitely presented metabelian group is a quotient of a finite cover
whose Laurent supports cover all directions. Its proof constructs the central
pullback and Laurent module, proves the required Bieri–Strebel necessity
statement, and extracts finitely many signed relations. Cone-margin existence
and finite epimorphism certificates then give

```math
\mathrm{WF}(P)\land\mathrm{Met}(G(P))
\quad\Longrightarrow\quad
\exists c,\quad\mathrm{checkData}(P,c)=\mathrm{true}.
```

**Effectivity.** Rational Fourier–Motzkin elimination, the integer radius,
finite relator construction, and the epimorphism check are proved primitive
recursive. Word equalities use finite normal-closure certificates checked by
free reduction. Thus checking a fixed certificate always terminates; searching
for one terminates exactly on $\mathcal M$. The final step uses `Nat.rfind`
in [Enumeration.lean](Kourovka/Computability/Enumeration.lean).

The [statement correspondence](docs/paper-map.md) records the declarations
for the individual results in the paper.

## Reproducing the verification

With [Elan](https://leanprover-community.github.io/get_started.html) and Python 3 installed:

```sh
git clone https://github.com/Achxy/k-17-124.git
cd k-17-124
lake exe cache get
./scripts/check.sh
```

Lean **4.24.0** and the full Mathlib dependency graph are pinned. The check
builds both complete theorem routes and the examples, treats Lean warnings as
failures, and audits transitive dependencies for additional axioms.
The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
See [verification](docs/verification.md) for the precise checks.

## Attribution

The original work is covered by [CC0](LICENSE). The currently adapted Schreier
sources retain their Apache-2.0 terms and
[attribution](third_party/ProCGroups-PROVENANCE.md).
Citation metadata is in [CITATION.cff](CITATION.cff).
