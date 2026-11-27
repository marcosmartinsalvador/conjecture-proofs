# What "new" means here, and what was searched

A result is called new when a search for an earlier solution found nothing. That is a
statement about the search, not a proof that nobody did it before. Each result's page
gives a grade:

- **Fairly sure**: the searches below found nothing.
- **Less sure**: they found nothing, but there is a stated reason for doubt.
- **No**: somebody else had it first. The page says who, and the result is listed as
  known.

## What was searched

Every result called new was checked on 26 or 27 November 2026, and again in a final
check on 27 November before release, against:

- **arXiv**: later versions of the source paper, its journal reference if any, and
  searches by the mathematical objects involved.
- **Public collections of machine-found proofs**, by arXiv number, author names and
  subject:
  `PrincipiaMathOrg/math-solutions`, `1337isnot1337/solved-conjectures` (including its
  work-in-progress branch), `openai/math`, `the-omega-institute/trureturing` (issues
  and pull requests as well as code), `senamakel/conjectures-lean`,
  `pro20541/dimitrov-conjectures-lean`.
- **All public GitHub issues, pull requests and code**, by arXiv number.
- **Mathlib**, and a general web search.
- **Registries of results**, in the final check: `palomar-registry.org`,
  `isitsolved.com` and Left to Solve (`GuillaumeBAUD-coder/open-math-agents`).

Results on problems from an established list had a further search of their own,
described on their page.

## What could not be searched

- No citation index and no journal database (MathSciNet, zbMATH, Google Scholar) was
  available, so "papers that cite the source" was covered only through arXiv and web
  search.
- Older printed literature was not combed.
- A search finds only what is public and indexed. Several groups work on conjectures
  of this kind with AI, and a proof that exists but has not been published cannot be
  found.

## What the searches changed

Eleven of the first twenty proofs found here turned out to have been done before, or
were published by someone else before this repository was public, mostly in public
collections of machine-found proofs rather than in papers. Those are the
"known results" on the front page. See [HISTORY.md](../HISTORY.md) for the record.

If you know of earlier work on anything listed as new, please
[open an issue](https://github.com/marcosmartinsalvador/conjecture-proofs/issues); the
result will be moved to the known results and credited.
