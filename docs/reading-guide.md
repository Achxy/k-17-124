# Reading the proof

This guide follows the proof in the paper rather than the order in which Lean
imports files. You can read the theorem statements before reading their proofs;
VS Code's “Go to Definition” then gives a precise route to each ingredient.
All paths below are relative to this directory.

## 1. What is the input?

[Presentations](../Kourovka/Presentations/Presentations.lean) defines a presentation
as a pair `(numberOfGenerators, relators)`. A relator is a list of signed letters;
`(i, true)` denotes the generator `i`, and `(i, false)` its inverse. Generator
indices begin at zero. `WellFormed` checks their bounds.

`GroupOf` forms the ordinary presented group, while `Metabelian` states that
any two commutators commute. These definitions are expanded again in
[the completion check](../Tests/Completion.lean), so the final theorem can be
read without relying on a name such as `MainClaim`.

## 2. What does a certificate say?

[EpimorphismEnumeration](../Kourovka/Enumeration/EpimorphismEnumeration.lean)
uses `((data, r), e)`:

* `data` is finite signed Laurent data;
* `r` certifies a positive dyadic margin and determines a finite radius;
* `e` encodes words witnessing a surjection from the resulting cover onto the input group.

`checkData_sound` proves that an accepted input is metabelian.
`checkData_complete` constructs a certificate for every well-formed metabelian
input. `check_correct` transports the equivalence to natural-number codes.
Finally, [Paper](../Kourovka/Paper.lean) states the three results used by the article.

## 3. Why is the source group metabelian?

[FiniteCover](../Kourovka/Covers/FiniteCover.lean) spells out the generators and
relators. The relations enforce commutation at short lattice displacements and
supply signed polynomial identities. In [CoverSoundness](../Kourovka/Covers/CoverSoundness.lean),
those identities reduce a longer displacement to shorter ones.

The geometry is the strict squared-norm decrease in
[Radius](../Kourovka/Polyhedral/Radius.lean). The required reordering of conjugates
is proved in [CollectionRadius](../Kourovka/Collection/CollectionRadius.lean).
The two covered word shapes are the ordered product and the literal inverse
ordered product; arbitrary reorderings are not silently identified.

## 4. Why are there enough covers?

[Cofinality](../Kourovka/Cofinality/Cofinality.lean) is the algebraic centre of
completeness. Starting with a finitely presented metabelian group, it constructs
a central pullback with a free abelian quotient. The abelian kernel carries a
Laurent module structure and is finitely generated as a module.

Finite presentation then yields tameness through
[BieriStrebelNecessity](../Kourovka/Halfspaces/BieriStrebelNecessity.lean).
[SignedTameness](../Kourovka/Modules/SignedTameness.lean) extracts finitely many
signed centralising polynomials. Their supports cover all directions, and
[CofinalRealization](../Kourovka/Cofinality/CofinalRealization.lean) turns these
identities into surjections from the finite-cover family.

The longer halfspace argument is separated into path geometry, Schreier
relators, the two-halfspace splitting obstruction, and module generation.
The [Schreier presentation](../Kourovka/Schreier/KernelPresentation.lean)
is constructed from group-valued path lifting and inverse quotient homomorphisms.

## 5. Why are all checks effective?

[FourierMotzkin](../Kourovka/Polyhedral/FourierMotzkin.lean) proves rational
elimination correct over ordered fields. [ConeVerifier](../Kourovka/Polyhedral/ConeVerifier.lean)
reduces cone coverage to finitely many rational systems, and
[ConeMargin](../Kourovka/Polyhedral/ConeMargin.lean) proves that a dyadic margin
search terminates for a covering family.

The `Computable*` files prove primitive recursiveness for concrete lists and
natural-number encodings. In particular,
[ComputableCoverData](../Kourovka/Covers/ComputableCoverData.lean) proves the radius formula
and [EpimorphismSemantics](../Kourovka/Certificates/EpimorphismSemantics.lean)
proves the finite epimorphism check correct. Word equations are certified by
finite products of conjugates of relators.

## Important conventions

* A failed presentation decode gives the empty presentation. A successfully
  decoded word with an out-of-range letter fails `WellFormed`.
* A well-formed zero-generator presentation defines the trivial group and is
  handled directly by the checker.
* Polynomial data are ordered term lists. They may include repeated exponents
  or zero coefficients. Completeness uses the canonical nonzero-polynomial subfamily.
* Primitive recursiveness applies to checking a given finite certificate.
  Searching for one need not terminate on a non-metabelian input.

The [complete module index](modules.md) is useful when following an import into
a technical part of the proof.
