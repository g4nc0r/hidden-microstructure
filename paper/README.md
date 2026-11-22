# Paper

Part of [The Hidden Microstructure of Shared Balance Concentrated Liquidity](../README.md).

| Version | Date | Files | SSRN |
|---|---|---|---|
| **The Hidden Microstructure of Shared Balance Concentrated Liquidity**, current | November 2026 revision | [`master-equation.pdf`](./master-equation.pdf), [`master-equation.tex`](./master-equation.tex) | [6745218](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=6745218) |

The current paper supersedes the versions of May and July 2026. [`changes-from-earlier-versions.pdf`](./changes-from-earlier-versions.pdf) lists the principal statements that differ, with their earlier and present forms. The paper itself carries no such list; its section on data and code availability points to this one.

The paper cites a supplement by table, figure, section and statement number (Tables S1 to S4 and S8, Figure S1, Section 7, Proposition S1). It is in [`../supplement/`](../supplement/).

The earlier versions are not kept in the tree. They are in the repository history: May 2026 at tag `v1.0.0`, July 2026 at commit `a39d5ef`.

## Building the current paper

```bash
xelatex master-equation.tex   # three passes
```

The source is a single file with its figures drawn in TikZ and pgfplots and its bibliography inline. It needs XeLaTeX and these fonts:

| Font | Used for | Source |
|---|---|---|
| EB Garamond | text | TeX Live, `ebgaramond` |
| Garamond-Math | mathematics | TeX Live, `garamond-math` |
| Cormorant Garamond, SemiBold and Medium Italic | title and section headings | Google Fonts, installed as a system font |
| Inconsolata | code | TeX Live, `inconsolata` |

## Licence

Paper PDFs and LaTeX sources © K. R. Ryan, all rights reserved. See [`../LICENSE`](../LICENSE).
