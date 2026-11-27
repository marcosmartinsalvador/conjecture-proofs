# Before this repository is made public

Delete this file as the last step. Until every box is ticked, keep the repository
private.

## For the author

- [x] **Write the notice** at the top of `README.md` ("Status of this work"). In your
      own words. It should say:
  - the results are unrefereed: no mathematician outside has read them;
  - what you are confident of (the Lean checks) and what you are not (that nobody did
    it before; that every statement is read exactly as its authors meant);
  - that corrections are welcome, and how to send them.
- [x] **Write the AI disclosure** in `README.md` ("How these results were produced"). In
      your own words. It should say:
  - which AI model found and wrote the proofs, and through what tool;
  - how the agents were organised: one that proposes and proves, a separate one that
    reviews, and a checker that neither can change;
  - what you did yourself: built and ran the system, set the rules for what counts as
    a result, read the reports, decided what to publish;
  - what you did not do: you did not find or write the proofs;
  - which results, if any, you have studied and can explain yourself.
- [x] **Put your name** in `CITATION.cff` (two `TODO` fields), spelled as you want it
      shown.
- [ ] **Read every page under `conjectures/`** at least once. You are the person
      responsible for what they say.
- [ ] **Decide which results go public.** All 21 are here. If you would rather start
      with fewer, delete the folders you do not want and run
      `python3 scripts/build_index.py`.
- [ ] On GitHub: turn on "Keep my email addresses private" (Settings, Emails), and
      check that two-factor sign-in is on.
- [ ] Add a one-line description to the repository (suggestion: "Machine-checked proofs
      and disproofs of conjectures from recent mathematics papers, found with AI agents
      and verified in Lean 4").

## For a session with Lean installed

These need a machine that can run Lean; they could not be done where this package was
assembled.

- [x] From a fresh clone: `./setup.sh`, then `tools/check_lean.sh <folder>` for all 21
      folders. Done on 2026-11-27 by the automatic check on a GitHub machine: all 21
      printed `ACCEPTED` (27 minutes). The fingerprints quoted on each page match the
      files in this repository.
- [x] `make test-lean` passes. Done on 2026-11-27: 108 checks, all `ok`.
- [x] The automatic check has run green once (2026-11-27). It has since been split in
      two: `index.yml` on every push, and `lean.yml`, which re-checks only the results
      whose Lean files changed (everything, if the checker or the pinned versions
      change, or when started by hand from the Actions tab). The "only what changed"
      part ran on GitHub the same day: it picked the two changed results and both were
      accepted with the fingerprints on their pages.
- [x] **Stale comments in the Lean files tidied** (2026-11-27): two results changed,
      comments only, both re-checked, pages updated with the new fingerprints.
- [x] **Palomar packaging**, for the results the author chooses to register: a
      `Challenge.lean` and `Solution.lean` with `module` headers, a `comparator.json`,
      a `formalization.yaml`, checked locally with `lake comparator`, following
      https://palomar-registry.org/how-to-submit . Palomar asks for credible research
      interest, so start with the strongest results, not all 21.
      Done on 2026-11-27 for three results, under [`palomar/`](palomar/README.md): the
      Kourovka partial result, the Δ-primitive result and the cycle formula. All three
      were accepted by `lake comparator`.
- [ ] **Decide where the Palomar packages are submitted from.** Palomar refuses a
      repository in which any `.lean` file lacks the `module` header, and the 49 files
      under `conjectures/` lack it (the checker here refuses module files). Either
      submit from a small repository holding only the packages, or port every Lean
      file here. See [`palomar/README.md`](palomar/README.md).

## On the day

- [ ] Run the search for earlier solutions again for every result called new
      (`docs/prior-art.md` says where), and move anything that has been overtaken to
      the known results.
- [ ] Delete this file, commit, and tag the commit (`v1`).
- [ ] Switch the repository to public.
- [ ] Submit to Palomar, signed in with your own GitHub account.
- [ ] Optional: email the authors of the papers behind your best results, with a link
      to the result's page.
