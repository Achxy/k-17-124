# Module index

For the mathematical argument, see [the reading guide](reading-guide.md).

## Presentations

| Module | Contents |
| --- | --- |
| [Presentations](../Kourovka/Presentations/Presentations.lean) | `PresentationCode` stores a finite alphabet and a list of words. `GroupOf` is the quotient of the free group by the normal closure of those relators. `DefinesMetabelian` includes the alphabet check; decoding alone does not establish it. |
| [RelatorCodes](../Kourovka/Presentations/RelatorCodes.lean) | Passage between finite relator lists and the ordinary presentation codes used in the exact recursive-enumerability target. |
| [FreeAbelianPresentation](../Kourovka/Presentations/FreeAbelianPresentation.lean) | Commutator relators identify the presented group with the integer lattice. |
| [KernelGenerators](../Kourovka/Presentations/KernelGenerators.lean) | The kernel of a surjection admits finitely many normal generators, which later supply generators for the conjugation module. |
| [CentralExtension](../Kourovka/Presentations/CentralExtension.lean) | Finite ordinary presentations for central extensions. The kernel and the quotient are represented by actual presented groups; no finite-presentation closure principle is assumed. |
| [CentralExtensionPresentation](../Kourovka/Presentations/CentralExtensionPresentation.lean) | A finite-rank free abelian central kernel can be adjoined to a finite presentation of the quotient. Relations record centrality and the errors in lifting relators. |
| [PullbackPresentation](../Kourovka/Presentations/PullbackPresentation.lean) | The pullback replaces the abelian quotient by a free abelian group. Its central structure allows the finite-presentation theorem to be applied. |
| [FiniteQuotient](../Kourovka/Presentations/FiniteQuotient.lean) | A surjective map between ordinary finite presentations is represented by appending finitely many relators to the source presentation. The construction is explicit and uses no Tietze theorem as an assumption. |
| [QuotientCodes](../Kourovka/Presentations/QuotientCodes.lean) | Appending finite natural-word relators realizes every quotient between ordinary finite presentations. The zero-generator case is handled directly. |

## Computability

| Module | Contents |
| --- | --- |
| [Enumeration](../Kourovka/Computability/Enumeration.lean) | The search below is unbounded only when the input has no certificate. `recursively_enumerable_of_certificates` proves the general computability reduction; the application to metabelian groups is in `Kourovka.Paper`. |
| [ComputableIntegers](../Kourovka/Computability/ComputableIntegers.lean) | Primitive recursive signed integer arithmetic using an explicit sum encoding. All external certificate data remains natural numbers and lists. |
| [ComputableWords](../Kourovka/Computability/ComputableWords.lean) | Primitive-recursive free reduction, with the actual Mathlib encoding. This is a computability theorem, not merely an executable implementation. |
| [ComputablePresentations](../Kourovka/Computability/ComputablePresentations.lean) | Uniform natural-alphabet word certificates for ordinary finite presentations. The generator bound is validated separately, and the semantics is the original `GroupOf` on `Fin p.1`, including presentations with no generators. |
| [ComputableClosure](../Kourovka/Computability/ComputableClosure.lean) | A primitive-recursive bounded search for normal-closure membership. The certificate consists only of a finite list of conjugators and a natural depth. Its completeness is proved for the actual subgroup normal closure. |

## Certificates

| Module | Contents |
| --- | --- |
| [WordCertificates](../Kourovka/Certificates/WordCertificates.lean) | Finite, executable normal-closure derivations for ordinary group presentations. The certificate checker solves no word problem in the presented group: its only equality comparisons are in a free group, using free reduction. |
| [NaturalWordCertificates](../Kourovka/Certificates/NaturalWordCertificates.lean) | One finite natural-number certificate verifies an arbitrary finite list of ordinary-presentation word equations. |
| [NaturalWordSubstitution](../Kourovka/Certificates/NaturalWordSubstitution.lean) | Uniform substitution of natural-alphabet words, with primitive-recursive code and the exact finite-generator semantics. |
| [PresentationIsomorphism](../Kourovka/Certificates/PresentationIsomorphism.lean) | A finite isomorphism-certificate alternative to enumerating Tietze moves. The checker uses explicit words for both generator maps and finite derivations for their relators and inverse identities. |
| [ComputableIsomorphism](../Kourovka/Certificates/ComputableIsomorphism.lean) | Natural-number isomorphism certificates for arbitrary ordinary finite presentation codes. All equations are checked by the proved word checker. |
| [IsomorphismSemantics](../Kourovka/Certificates/IsomorphismSemantics.lean) | Soundness and completeness of the natural-alphabet isomorphism equations. |
| [ComputableEpimorphism](../Kourovka/Certificates/ComputableEpimorphism.lean) | Finite epimorphism certificates for ordinary finite presentations. Only the source relators and the target-generator preimage equations are checked. The words giving preimages need not induce a reverse homomorphism. |
| [EpimorphismSemantics](../Kourovka/Certificates/EpimorphismSemantics.lean) | Soundness and completeness of finite epimorphism certificates. |

## Polyhedral

| Module | Contents |
| --- | --- |
| [FourierMotzkin](../Kourovka/Polyhedral/FourierMotzkin.lean) | A rational Fourier–Motzkin algorithm with correctness over every ordered field. The same Boolean computation therefore decides both rational and real feasibility. No oracle or floating-point computation is used. |
| [ComputableFourierMotzkin](../Kourovka/Polyhedral/ComputableFourierMotzkin.lean) | Uniform list encoding of integer Fourier–Motzkin elimination. Dimensions are natural inputs, so no dependent finite-vector encoding is required. |
| [ConeVerifier](../Kourovka/Polyhedral/ConeVerifier.lean) | The finite rational cone test used in the Bieri–Strebel certificate. All support choices and all faces of the infinity-norm unit sphere are checked. The Boolean test is proved equivalent to the quantified real cone condition. |
| [ConeMargin](../Kourovka/Polyhedral/ConeMargin.lean) | A positive rational margin exists for every accepted cone cover. Hence the dyadic margin search in the manuscript terminates; this is not a numerical test. |
| [ComputableCone](../Kourovka/Polyhedral/ComputableCone.lean) | Natural/list computation of the dyadic cone-margin test, uniformly in the dimension. Scaling by 2^r keeps the elimination arithmetic integral. |
| [Radius](../Kourovka/Polyhedral/Radius.lean) | Subtracting a bounded lattice vector with a sufficiently positive scalar product strictly decreases squared norm. This is the geometric step in cover soundness. |

## Covers

| Module | Contents |
| --- | --- |
| [FiniteCover](../Kourovka/Covers/FiniteCover.lean) | The actual finite ordinary presentation appearing in (17.124.1)–(17.124.4). The signed-polynomial relation retains the literal inverse ordered word. |
| [CertifiedRadius](../Kourovka/Covers/CertifiedRadius.lean) | The manuscript's explicit radius bound uses exact rational arithmetic. |
| [CertifiedCover](../Kourovka/Covers/CertifiedCover.lean) | An accepted rational cone-margin certificate produces an explicit ordinary finite presentation defining a metabelian group. |
| [CoverMargin](../Kourovka/Covers/CoverMargin.lean) | Rational numerical data extracted from an accepted finite cone cover. |
| [CoverSoundness](../Kourovka/Covers/CoverSoundness.lean) | Soundness of the actual finite Bieri–Strebel group presentation. |
| [ComputableCoverData](../Kourovka/Covers/ComputableCoverData.lean) | Uniform natural/list encoding of finite cover data and its explicit integer radius. Both dimensions are encoded one below their positive value. |
| [ComputableCoverWords](../Kourovka/Covers/ComputableCoverWords.lean) | Primitive recursive generation of cover relators on the natural alphabet. |
| [ComputableCoverBounds](../Kourovka/Covers/ComputableCoverBounds.lean) | Every generated natural-alphabet cover relator uses only its announced finite alphabet. Reduction, inversion, products and integer powers preserve this bound. |
| [ComputableCoverSemantics](../Kourovka/Covers/ComputableCoverSemantics.lean) | The natural-alphabet relators realize exactly the three ordinary cover families. |
| [ComputableLatticeBall](../Kourovka/Covers/ComputableLatticeBall.lean) | Primitive recursive enumeration of finite integer lattice balls. |

## Collection

| Module | Contents |
| --- | --- |
| [Collection](../Kourovka/Collection/Collection.lean) | Collection identities for the Bieri–Strebel finite presentations. The local reordering argument retains the literal order of every conjugating word; commutation is used only at lattice points within the specified budget. |
| [CollectionFinite](../Kourovka/Collection/CollectionFinite.lean) | Finite-budget collection. A block may be traversed whenever both endpoints belong to a coordinatewise solid lattice set. |
| [CollectionGeometry](../Kourovka/Collection/CollectionGeometry.lean) | Euclidean lattice geometry used by finite-radius collection. |
| [CollectionRadius](../Kourovka/Collection/CollectionRadius.lean) | Finite-radius Bieri–Strebel collection for the two word shapes used by the presentation enumerator. |

## Modules

| Module | Contents |
| --- | --- |
| [LaurentAction](../Kourovka/Modules/LaurentAction.lean) | The ring action describes how lifts of quotient elements conjugate the abelian kernel. The construction is independent of the chosen lifts. |
| [CommutatorModule](../Kourovka/Modules/CommutatorModule.lean) | Conjugation factors through the abelian quotient. Finite normal generators of the kernel become generators of its additive Laurent module. |
| [FiniteModuleGenerators](../Kourovka/Modules/FiniteModuleGenerators.lean) | These lemmas turn abstract module finiteness into finite data used in cover constructions. |
| [ValuationModule](../Kourovka/Modules/ValuationModule.lean) | The algebraic direction of Bieri–Strebel Proposition 2.1. A module finite over a valuation half-ring has a centralizing Laurent polynomial with strictly positive support. The determinant argument is supplied by the kernel-checked Nakayama lemma. |
| [TamenessCompactness](../Kourovka/Modules/TamenessCompactness.lean) | The finite extraction in the Bieri–Strebel centralizer criterion. Pointwise centralizing polynomials need not come from an a priori finite family. Compactness supplies a finite family while retaining its algebraic identities. |
| [SignedTameness](../Kourovka/Modules/SignedTameness.lean) | From directional module finiteness to finitely many signed centralizer polynomials. Tameness here retains its mathematical module-finiteness meaning; the claim that ordinary finite presentation implies tameness is separate. |
| [ModuleRealization](../Kourovka/Modules/ModuleRealization.lean) | Conversion of signed Laurent-module identities to the exact ordinary group relators. Negative tags retain the literal inverse ordered word. |

## Halfspaces

| Module | Contents |
| --- | --- |
| [HalfspaceGeometry](../Kourovka/Halfspaces/HalfspaceGeometry.lean) | Reordering lattice steps inside a thick strip. This supplies the path connectivity used in the Bieri–Strebel halfspace argument. |
| [HalfspaceGeneration](../Kourovka/Halfspaces/HalfspaceGeneration.lean) | Finite ordinary presentations force an abelian kernel to be generated by loops in one of two valuation halfspaces. |
| [HalfspaceRelators](../Kourovka/Halfspaces/HalfspaceRelators.lean) | Every relator of the Schreier presentation is confined to one of the two overlapping halfspaces. |
| [HalfspaceSplitting](../Kourovka/Halfspaces/HalfspaceSplitting.lean) | The algebraic obstruction in the Bieri–Strebel two-halfspace argument. Britton's lemma shows that twisting two elements outside the overlap produces noncommuting images. This is used with a split Schreier presentation. |
| [HalfspaceShift](../Kourovka/Halfspaces/HalfspaceShift.lean) | Moving a bounded halfspace cutoff to zero by an actual kernel conjugation. |
| [HalfspaceModule](../Kourovka/Halfspaces/HalfspaceModule.lean) | Clearing negative Laurent coefficients by a positive monomial, and the telescoping argument needed for finite generation by halfspace loops. |
| [HalfspaceLoopModule](../Kourovka/Halfspaces/HalfspaceLoopModule.lean) | Commutator expansion along genuine halfspace paths, followed by the positive-shift argument, proves finite generation over a valuation half-ring. |
| [HalfspaceLoops](../Kourovka/Halfspaces/HalfspaceLoops.lean) | The module generated by loops in a valuation halfspace. |
| [SchreierHeights](../Kourovka/Halfspaces/SchreierHeights.lean) | Height-controlled Schreier representatives and rewriting. |
| [SchreierKernel](../Kourovka/Halfspaces/SchreierKernel.lean) | The Schreier presentation is a presentation of the actual kernel inside the original ordinary presented group. |
| [SchreierPaths](../Kourovka/Halfspaces/SchreierPaths.lean) | Actual words realizing halfspace Schreier generators. |
| [BieriStrebelNecessity](../Kourovka/Halfspaces/BieriStrebelNecessity.lean) | The finite-presentation necessity direction of the Bieri–Strebel theorem. The proof uses the actual Schreier kernel presentation, the two-halfspace Britton obstruction, and the actual conjugation module of the kernel. |

## Cofinality

| Module | Contents |
| --- | --- |
| [CofinalCover](../Kourovka/Cofinality/CofinalCover.lean) | The actual central pullback used to replace an abelian quotient by a free abelian quotient. Both kernels and both surjective projections are explicit. |
| [LatticePullback](../Kourovka/Cofinality/LatticePullback.lean) | The central pullback, with its quotient expressed as the manuscript's integer lattice. Its finite presentation and finite Laurent module are actual constructions, independent of the tameness theorem. |
| [CofinalRealization](../Kourovka/Cofinality/CofinalRealization.lean) | A tame finite Laurent module with its actual group extension gives the finite ordinary covers in the enumeration. |
| [Cofinality](../Kourovka/Cofinality/Cofinality.lean) | Every actual finitely presented metabelian group is a quotient of one of the finite ordinary cover presentations, at every selected radius. |

## Enumeration

| Module | Contents |
| --- | --- |
| [ComputableEnumeration](../Kourovka/Enumeration/ComputableEnumeration.lean) | The actual primitive-recursive certificate predicate for metabelian ordinary finite presentations. |
| [EnumerationCofinality](../Kourovka/Enumeration/EnumerationCofinality.lean) | A finitely presented metabelian group is covered by finite Laurent data. A dyadic margin certificate supplies an effective radius for those data. |
| [EnumerationCorrectness](../Kourovka/Enumeration/EnumerationCorrectness.lean) | Soundness and completeness of the actual combined certificate checker, and the unconditional solution of the original recursive-enumerability target. |
| [EpimorphismEnumeration](../Kourovka/Enumeration/EpimorphismEnumeration.lean) | A direct metabelianity certificate: a checked finite cover and a finite epimorphism certificate onto the input presentation. The finite-cover construction supplies soundness, and cofinality supplies completeness. |
| [Main](../Kourovka/Enumeration/Main.lean) | This aggregate module preserves the alternative proof. For the shorter epimorphism-certificate route used by the paper, start with `Kourovka.Paper`. |

## Schreier

| Module | Contents |
| --- | --- |
| [Transversal](../Kourovka/Schreier/Transversal.lean) | A transversal chooses one word in each right coset of a subgroup of a free group. Its edges are labelled by pairs `(chosen representative, generator)`. The correction word attached to an edge lies in the subgroup. |
| [PathLifting](../Kourovka/Schreier/PathLifting.lean) | Edge labels may take values in any group. Reading a negative letter traverses its positive edge backwards. Adjacent inverse letters cancel, so path lifting descends from lists to the free group. Concatenation gives the cocycle identity. |
| [KernelPresentation](../Kourovka/Schreier/KernelPresentation.lean) | For a transversal of `L ≤ F(X)` containing the normal closure of `R`, the Schreier edges present `L / ⟨⟨R⟩⟩`. There are two relator families: lifts of original relators from every representative, and lifts of the section paths. |

## Theorem interface and verification

- [Paper](../Kourovka/Paper.lean): the certificate equivalence and recursive enumerability.
- [Completion](../Tests/Completion.lean): both complete targets with the group property expanded.
- [Presentation examples](../Tests/PresentationExamples.lean): valid and malformed inputs.
- [Cone examples](../Tests/ConeExamples.lean): cone-margin and finite-radius boundaries.
- [Audit](../Audit.lean): transitive axiom checks.
