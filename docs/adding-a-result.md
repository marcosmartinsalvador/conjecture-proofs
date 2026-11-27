# Adding a result

Every result is one folder under `conjectures/`. The front page is generated from the
folders, so adding a result never means editing a table by hand.

## The folder

```
conjectures/<folder>/
  README.md         the result's page (sections below)
  result.json       the data behind its row on the front page
  Statement.lean    def Claim : Prop := ...
  Proof.lean        theorem result : Claim
  <Name>.lean       optional helpers imported by Proof.lean
  ...               optional: a proof on paper, scripts that test the claim numerically
```

`<folder>` is lowercase with underscores and is also the Lean module name, so it must
start with a letter and contain only letters, digits and underscores.

## `result.json`

```json
{
  "slug": "<folder>",
  "title": "A short title",
  "kind": "full | partial | known",
  "outcome": "Proved | Disproved | ...",
  "summary": "One sentence saying what is established.",
  "source": "Authors, \"Title\", arXiv:XXXX.XXXXX (date), Conjecture N.",
  "url": "https://arxiv.org/abs/XXXX.XXXXX",
  "label": "lean",
  "checked": "YYYY-MM-DD",
  "rank": 12,
  "new": "fairly sure | less sure | no",
  "first_by": "only for kind \"known\": who had it first, and when"
}
```

- `kind`: `full` settles the statement as its source prints it. `partial` settles part
  of a question that stays open. `known` means someone else had it first.
- `rank` orders the front page, most significant first. Renumber when a new result
  belongs above existing ones.

## The page (`README.md`)

Use the same sections as the existing pages, in the same order:

1. Title, a one-line status, and the summary table.
2. **In plain words**: what the question is and what was established, for a reader who
   is not a specialist. For a partial result, say plainly what is not proved.
3. **The statement as printed**: the reference, and the conjecture quoted exactly.
   Quote the statement only; describe the definitions in your own words.
4. **What is proved here**: what `Claim` says, and every choice made in reading the
   source.
5. **Idea of the proof**: enough for a mathematician to see why it is true.
6. **Machine check**: the checker's output, pasted unchanged.
7. **Is it new?** (or **Who had it first**): the grade, the reasons, and anything that
   could not be searched.
8. **Files**.

## Before it is merged

1. `tools/check_lean.sh <folder>` prints `ACCEPTED`, and the page quotes that output.
2. A review by someone, or some session, that did not write the proof has compared
   `Statement.lean` with the source and searched for earlier solutions
   ([prior-art.md](prior-art.md) says where).
3. `python3 scripts/build_index.py` has been run, so the front page includes the new
   row. The automatic check fails if it has not.
   A second automatic check runs the checker on every result whose Lean files changed
   in the pull request; it must be green before merging.
4. A line is added to [HISTORY.md](../HISTORY.md).

## Changing or withdrawing a result

Nothing is deleted. If a result is found to be wrong, its page says so at the top, its
`kind` and `outcome` are changed to say what still stands, and HISTORY.md records what
happened and who found the problem. If earlier work turns up, the result becomes
`known` and `first_by` credits it.
