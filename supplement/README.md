# Supplement

Part of [The Hidden Microstructure of Shared Balance Concentrated Liquidity](../README.md).

[`master-equation-supplement.pdf`](./master-equation-supplement.pdf) holds material that the November 2026 revision of the paper cites and does not print. Its tables, figures, equations and statements are numbered S1, S2 and so on; numbers without an S are the paper's.

| Section | Contents | Cited from the paper as |
|---|---|---|
| 1 | Tables behind the simulations of the model | Tables S1 to S3 |
| 2 | The steps of the leftover by portfolio | Table S4, Figure S1 |
| 3 | The auxiliary indexers | |
| 4 | The Foundry suite scenario by scenario | |
| 5 | Coverage of the Lean formalisation by statement | |
| 6 | The first set of replays | Table S8 |
| 7 | Proofs of Propositions 4 and 5 and Lemma 3, and the statement on position size with its proof | Section 7, Proposition S1 |

The paper depends on Section 7 for three of its proofs, so the two documents belong together.

## Building

```bash
xelatex master-equation-supplement.tex   # three passes
```

The source is a single file that reads one figure from `figures/`. Numbers that refer to the paper are written into it as text, so it compiles without the paper. It is set in the paper's type and needs XeLaTeX and the fonts listed in [`../paper/README.md`](../paper/README.md).

## Licence

© K. R. Ryan, all rights reserved. See [`../LICENSE`](../LICENSE).
