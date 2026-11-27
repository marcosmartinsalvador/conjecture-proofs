# How results are checked

A result is listed in this repository only when three things hold: the checker prints
`ACCEPTED` for it, a review has compared its Lean statement with the source, and a
search for earlier solutions has been made and recorded. This page is about the first.

## What is pinned

| What | Version | Where it is pinned |
|---|---|---|
| Lean | 4.36.0 (commit `611c117bfaf7`) | `lean-toolchain`, and again inside `tools/check_lean.sh` |
| Mathlib | tag `v4.36.0` (commit `fc4f59e577fe`) | `lakefile.toml`, `lake-manifest.json`, and again inside `tools/check_lean.sh` |
| Mathlib's own dependencies | whatever that Mathlib commit pins | `lake-manifest.json` |

The checker does not trust the three project files. It carries its own copy of the two
commits and refuses to run if the installed tools differ, or if any package's source
files were edited.

## The files of a result

```
conjectures/<folder>/Statement.lean    defines  def Claim : Prop := ...
conjectures/<folder>/Proof.lean        proves   theorem result : Claim
conjectures/<folder>/<Name>.lean       optional helper files that Proof.lean imports
```

`Statement.lean` imports nothing from this repository, only Mathlib, so the statement
can be read on its own.

## What the checker does

`tools/check_lean.sh <folder>`:

1. Checks that Lean and Mathlib are the pinned ones, with unmodified sources.
2. Copies only this result's `.lean` files to a scratch directory, so that a proof
   cannot lean on another folder's files or on stale build output.
3. Refuses text that has no business in these files: `sorry`, `admit`, `native_decide`,
   declared axioms, and a list of commands that could run code at compile time. This
   scan is crude on purpose; it also fires inside comments.
4. Compiles `Statement.lean`, then `Proof.lean` and its helpers.
5. Writes its own file stating `theorem checker_generated_check : Claim := result`,
   compiles it, prints its axioms, and accepts only `propext`, `Classical.choice` and
   `Quot.sound`.
6. Loads the compiled files as data, without running any of their code, and checks
   that `Claim` is a plain definition of type `Prop` in this result's `Statement.lean`,
   that `result` is a theorem whose statement is literally `Claim`, that the axioms
   found by walking the proof terms are the allowed ones, and that `Statement.lean`
   declares no axiom and nothing opaque, partial or unsafe.
7. Replays every declaration of the result's files through the Lean kernel in a fresh
   process.

The header of [`tools/check_lean.sh`](../tools/check_lean.sh) describes each step and
its limits in full. [`tests/test_lean_checker.sh`](../tests/test_lean_checker.sh) is a
set of deliberately dishonest proof files that the checker must reject; run it with
`make test-lean` (about five minutes).

## Reading the output

```
ACCEPTED  slug=<folder>  result : Claim  (Claim as defined in conjectures/<folder>/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: <16 hex digits>   proof sha256: <16 hex digits>   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: <16 hex digits> (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

- **`statement sha256`, `proof sha256`**: the first 16 hex digits of the SHA-256 of
  `Statement.lean` and `Proof.lean`. They tie the output to exact files:
  `sha256sum conjectures/<folder>/Statement.lean` should begin with the same digits.
- **`checker`**: the same for `tools/check_lean.sh` itself. "(same as main)" records
  that the checker was byte-identical to the one on the main branch of the repository
  the work was done in, so a working branch could not have altered its own judge.
- **`sandbox: on`**: the proof files were compiled as an unprivileged user with no
  network and a read-only filesystem. This happens only on Linux when run as root;
  elsewhere the line says `sandbox: off`, and the result is the same.
- **`REVIEW.md`**: the working name of the review record. This repository does not
  carry those records in full; what each review concluded, and the reading choices it
  examined, are on the result's page under "What is proved here" and "Is it new?".

The blocks quoted on the result pages were produced in the private repository this work
was done in, before the files were copied here unchanged. Running the checker here
should reproduce them, apart from `sandbox` and the "(same as main)" note.

## What `ACCEPTED` does not mean

- It does not mean the Lean statement is a faithful reading of the source. That is a
  human-style judgement. Each result's page lists the reading choices so that anyone
  can disagree with them.
- It does not mean the result is new.
- It trusts Lean's kernel, the pinned Mathlib as compiled on the machine, and the
  three standard axioms, as almost all Lean mathematics does.

## A note on comments in the Lean files

The Lean files are byte-for-byte the files that were checked, comments included, so
that the fingerprints match. Their comments were written while the work was in
progress. A few refer to working notes that are not in this repository (`source.md`,
`REVIEW.md`), and one or two describe a state that later changed. The comments are not
part of what Lean checks. In the same way, the checker's own comments call it "the lane A
checker", its name in the repository the work was done in.

## Running it

```bash
./setup.sh
export PATH="$HOME/.elan/bin:$PATH"
tools/check_lean.sh <folder>
```

`./setup.sh` installs `elan`, the Lean toolchain (about 3 GB) and Mathlib with its
prebuilt cache (about 7 GB). On a 4-core machine it takes a few minutes; a check then
takes about half a minute. If you already have Lean, `lake exe cache get && lake build`
builds every result without the checker.
