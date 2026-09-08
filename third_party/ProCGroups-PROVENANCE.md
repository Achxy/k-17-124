# Historical ProCGroups Schreier source attribution

The initial export included four files in `Kourovka/Schreier` adapted from
[ProCGroups](https://github.com/n-yamaguchi-0729/ProCGroups/tree/6933dfe3f376833421ce10e782108b95ac84bda5),
commit `6933dfe3f376833421ce10e782108b95ac84bda5` (Apache License 2.0).
The license is preserved in `ProCGroups-LICENSE`. Upstream contains no NOTICE file.

Original base path: `Lean4/ProCGroups/ReidemeisterSchreier/Discrete/`.
`basic`, `congruence`, `operations` correspond respectively to
`Presentations/Relators/Basic.lean`, `Congruence.lean`, `Operations.lean`;
`rewriting` is `ReidemeisterSchreier/Rewriting.lean`.

In that export, module imports and declaration namespaces were local to this
standalone package, and compatibility adaptations targeted Lean 4.24/Mathlib 4.24.
The adapted sources were included in its ordinary build and transitive axiom audit.

Those four proof modules have since been replaced by the implementation described
in [source provenance](../docs/provenance.md). The table below and the accompanying
licence preserve the historical attribution. The former code remains in Git
history at commit `5627cc84341985db2708f408cc80203fba33fdd8`.

| Local file | Original source key | SHA-256 of original source bytes |
| --- | --- | --- |
| `RelatorBasic.lean` | `basic` | `b757b869a9a6def64ff11a42890f4373346153d3b6d8013b4c44c9ba268885f9` |
| `RelatorCongruence.lean` | `congruence` | `117f6e295757a55303cbb5f2ff5413634e2e5a309fb9b8f40ef2ae88d1c722d3` |
| `RelatorOperations.lean` | `operations` | `279c20baebefd9c973abcac6f5ac7567658ba84a7e8cd94be51a096ac74b937c` |
| `Rewriting.lean` | `rewriting` | `4f45a1071dd67f6b7c31b44f385e66038b6accc41252bcec355fae4ea853963b` |
