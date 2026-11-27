# History

What was added, corrected or reclassified, newest first. Nothing is removed from this
file.

## 2026-11-27

- **Palomar packages added** for three results (the Kourovka partial result, the
  Δ-primitive result and the cycle formula), under [`palomar/`](palomar/README.md).
  Each is the accepted Lean text with the `module` header the Palomar registry
  requires; no statement and no proof changed, and the results' own folders are
  untouched. Nothing has been submitted to Palomar.
- **Kourovka problem 20.52, the odd half**: accepted by the checker and reviewed. Listed
  as a partial result; the problem stays open.
  - Correction during review: the first working note said the problem had no
    literature. That was wrong. The review found the 2013 paper the question comes from
    (Buckley and MacHale), which already has every m below 512. The paper was then read
    in full, and the result was graded "fairly sure" to be new for the infinite family.
- **Stable consecutive patterns**: reviewed. Graded "less sure" to be new, for the two
  reasons given on its page.
- This repository was assembled from the private working repository. The Lean files
  were copied unchanged.
- **Comments tidied in two results** (the Δ-primitive result and the ultra-Euclidean
  ring result): out-of-date comments in their Lean files were rewritten. No statement
  and no proof changed; with comments removed the files are identical to before. Both
  were re-checked, and their pages show the new fingerprints.

## 2026-11-26

- Twenty results accepted by the checker over 25 and 26 November.
- **Reclassified as known, after review:** nine of them had been done before, in public
  collections of machine-found proofs or in earlier papers. They are kept as known
  results and credited to whoever was first.
- **Re-check against other collections of machine-found proofs.** Every result still
  called new was searched again in the places listed in
  [docs/prior-art.md](docs/prior-art.md). Two changes:
  - **Dimitrov's Conjecture 7** moved from new to known: another group's public record
    says it was proved and checked there twelve days earlier.
  - **Dimitrov's Conjecture 2** stays new but dropped to "less sure".

## 2026-11-25

- **Dimitrov's Conjecture 1** accepted by the checker: the first result, used to set up
  the checking process. It was later found to have a public Lean proof from
  September 2026 and is listed as known.
