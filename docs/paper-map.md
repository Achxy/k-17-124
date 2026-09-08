# Mathematical correspondence and verification

This file accompanies Finite presentations of metabelian groups: effective
enumeration via Laurent relations. The article presents the mathematics;
this companion records encoding and proof-verification details.

## Main statement

The reader-facing statements are in [Kourovka/Paper.lean](../Kourovka/Paper.lean).
Their proofs are assembled in namespace
`Kourovka.MetabelianEnumeration.EpimorphismEnumeration`:

- `check_primrec` proves primitive recursiveness of the two-input Boolean predicate.
- `check_correct` proves DefinesMetabelian(p) iff there exists c with check(p,c)=true.
- `kourovka_17_124_via_epimorphisms` deduces recursive enumerability.

[Tests/Completion.lean](../Tests/Completion.lean) independently expands the group property to well-formedness
of p and [a,b][c,d]=[c,d][a,b] for every a,b,c,d in the ordinary presented group.
These are quotient groups of free groups in the variety of all groups.

## Finite-data conventions

The article uses nonzero Laurent polynomials with nonzero coefficients and
an order on each finite support. This is a canonical subfamily of the formal
syntax, which uses ordered term lists and also permits repeated exponents,
zero coefficients and empty lists. For those general lists, D counts the
listed exponents with multiplicity; the ordered products are not normalized.
The radius formula and soundness argument apply to this larger syntax.
Completeness is supplied by the canonical polynomial subfamily.

Presentation decoding is total: failed decoding is assigned the empty
presentation. Successfully decoded words with out-of-range generator indices
fail the well-formedness predicate. The zero-generator branch accepts exactly
well-formed presentations and represents the trivial group.

For collection, the article states the two cases proved in CollectionRadius:
q(u)q(v) and q(u)^(-1)q(v)^(-1). It does not assert collection for arbitrary
semi-ordered words. For Fourier-Motzkin elimination, subtract gamma from the
constant coefficient to translate the article's inequalities to Row.eval <= 0.

## Statement-to-source map

All source paths below are relative to the repository root. The source files
contain the full hypotheses and conclusions; correspondence with the article was reviewed
by inspection. Lean checks the formal declarations, not natural-language TeX.

### The certificate theorem (`thm:main`)

Source: [Kourovka/Enumeration/EpimorphismEnumeration.lean](../Kourovka/Enumeration/EpimorphismEnumeration.lean).

- `Kourovka.MetabelianEnumeration.EpimorphismEnumeration.check_primrec`
- `Kourovka.MetabelianEnumeration.EpimorphismEnumeration.check_correct`
- `Kourovka.MetabelianEnumeration.EpimorphismEnumeration.kourovka_17_124_via_epimorphisms`

### Collection and the derived subgroup (`lem:collection`)

Source: [Kourovka/Collection/CollectionRadius.lean](../Kourovka/Collection/CollectionRadius.lean).

- `Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_radius`
- `Kourovka.MetabelianEnumeration.FiniteCover.Collection.collection_radius_inverse`

### Collection and the derived subgroup (`lem:collection`)

Source: [Kourovka/Collection/Collection.lean](../Kourovka/Collection/Collection.lean).

- `Kourovka.MetabelianEnumeration.FiniteCover.Collection.normalClosure_abelian`

### Tameness and signed Laurent relations (`lem:tameness`)

Source: [Kourovka/Halfspaces/BieriStrebelNecessity.lean](../Kourovka/Halfspaces/BieriStrebelNecessity.lean).

- `Kourovka.MetabelianEnumeration.BieriStrebelNecessity.tame_of_finite_presentation`

### Tameness and signed Laurent relations (`lem:tameness`)

Source: [Kourovka/Modules/SignedTameness.lean](../Kourovka/Modules/SignedTameness.lean).

- `Kourovka.MetabelianEnumeration.SignedTameness.finite_signed_centralizers`

### Rational cone margins (`lem:margin`)

Source: [Kourovka/Polyhedral/ConeVerifier.lean](../Kourovka/Polyhedral/ConeVerifier.lean).

- `Kourovka.MetabelianEnumeration.ConeVerifier.checkMargin_correct`
- `Kourovka.MetabelianEnumeration.ConeVerifier.coneCheck_correct`

### Rational cone margins (`lem:margin`)

Source: [Kourovka/Polyhedral/ConeMargin.lean](../Kourovka/Polyhedral/ConeMargin.lean).

- `Kourovka.MetabelianEnumeration.ConeVerifier.dyadic_margin_search_terminates`

### Rational cone margins (`lem:margin`)

Source: [Kourovka/Polyhedral/ComputableCone.lean](../Kourovka/Polyhedral/ComputableCone.lean).

- `Kourovka.MetabelianEnumeration.ComputableCone.checkMargin_primrec`

### The explicit radius (`eq:constants`)

Source: [Kourovka/Covers/ComputableCoverData.lean](../Kourovka/Covers/ComputableCoverData.lean).

- `Kourovka.MetabelianEnumeration.ComputableCoverData.radius_eq`
- `Kourovka.MetabelianEnumeration.ComputableCoverData.coneRadius_formula`
- `Kourovka.MetabelianEnumeration.ComputableCoverData.radius_primrec`

### Radius reduction (`lem:shrink`)

Source: [Kourovka/Polyhedral/Radius.lean](../Kourovka/Polyhedral/Radius.lean).

- `Kourovka.MetabelianEnumeration.vector_radius_shrink`

### Soundness of finite covers (`prop:sound`)

Source: [Kourovka/Covers/CoverSoundness.lean](../Kourovka/Covers/CoverSoundness.lean).

- `Kourovka.MetabelianEnumeration.FiniteCover.radius_step`
- `Kourovka.MetabelianEnumeration.FiniteCover.all_ordered_commute`
- `Kourovka.MetabelianEnumeration.FiniteCover.certified_cover_metabelian`

### Soundness of finite covers (`prop:sound`)

Source: [Kourovka/Covers/ComputableCoverSemantics.lean](../Kourovka/Covers/ComputableCoverSemantics.lean).

- `Kourovka.MetabelianEnumeration.ComputableCoverSemantics.checked_presentation_metabelian`

### Finite presentations of central extensions (`lem:central`)

Source: [Kourovka/Presentations/CentralExtensionPresentation.lean](../Kourovka/Presentations/CentralExtensionPresentation.lean).

- `Kourovka.MetabelianEnumeration.CentralExtension.finite_presentation_of_central_extension`

### Cofinality of finite covers (`prop:cofinal`)

Source: [Kourovka/Cofinality/Cofinality.lean](../Kourovka/Cofinality/Cofinality.lean).

- `Kourovka.MetabelianEnumeration.CofinalCover.finite_presentation_cover_cofinal`

### Cofinality of finite covers (`prop:cofinal`)

Source: [Kourovka/Enumeration/EnumerationCofinality.lean](../Kourovka/Enumeration/EnumerationCofinality.lean).

- `Kourovka.MetabelianEnumeration.ComputableEnumeration.encoded_cover_cofinal`

### Finite epimorphism certificates (`lem:epi`)

Source: [Kourovka/Certificates/EpimorphismSemantics.lean](../Kourovka/Certificates/EpimorphismSemantics.lean).

- `Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkEpi_correct`

### Finite epimorphism certificates (`lem:epi`)

Source: [Kourovka/Certificates/ComputableEpimorphism.lean](../Kourovka/Certificates/ComputableEpimorphism.lean).

- `Kourovka.MetabelianEnumeration.ComputableEpimorphism.checkEpi_primrec`

### The enumeration predicate (`eq:predicate`)

Source: [Kourovka/Enumeration/EpimorphismEnumeration.lean](../Kourovka/Enumeration/EpimorphismEnumeration.lean).

- `Kourovka.MetabelianEnumeration.EpimorphismEnumeration.checkData`
- `Kourovka.MetabelianEnumeration.EpimorphismEnumeration.check`

### Rational cone margins (`lem:margin`)

Source: [Kourovka/Polyhedral/FourierMotzkin.lean](../Kourovka/Polyhedral/FourierMotzkin.lean).

- `Kourovka.MetabelianEnumeration.FourierMotzkin.lower_constraint`
- `Kourovka.MetabelianEnumeration.FourierMotzkin.upper_constraint`
- `Kourovka.MetabelianEnumeration.FourierMotzkin.pair_constraint`
- `Kourovka.MetabelianEnumeration.FourierMotzkin.elimination_step`
- `Kourovka.MetabelianEnumeration.FourierMotzkin.rational_iff_real`
