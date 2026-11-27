#!/usr/bin/env bash
# Tests that the lane A checker accepts honest results and REJECTS every cheat we
# could think of. Runs in a throwaway copy of the repo (it borrows .lake, the
# installed Mathlib, read-only). Needs ./setup.sh to have installed Lean. ~5 min.
#
# Many cheats are stopped twice: first by the checker's text scan, then again by
# the later steps. To prove the later steps hold on their own, the cheats are
# also run against a copy of the checker whose text scan is switched off
# ("no scan" below). That copy exists only inside this test.
set -uo pipefail
SRC="$(cd "$(dirname "$0")/.." && pwd)"
[[ -d "$SRC/.lake/packages/mathlib" ]] || { echo "Lean/Mathlib not installed: run ./setup.sh"; exit 2; }
T="$(mktemp -d)"; trap 'rm -rf "$T"' EXIT
mkdir -p "$T/tools" "$T/conjectures"
cp "$SRC/tools/check_lean.sh" "$T/tools/"
ln -s "$SRC/.lake" "$T/.lake"
sed 's/^scan () {.*$/&\n  return 0/' "$T/tools/check_lean.sh" > "$T/tools/check_noscan.sh"
chmod +x "$T/tools/check_noscan.sh"
grep -q '^  return 0$' "$T/tools/check_noscan.sh" || { echo "could not build the no-scan copy"; exit 2; }
# and a copy that believes it is not root, to exercise the path without a sandbox
sed 's/&& "$(id -u)" -eq 0 \]\]/\&\& 1 -eq 0 ]]/' "$T/tools/check_lean.sh" > "$T/tools/check_nosandbox.sh"
chmod +x "$T/tools/check_nosandbox.sh"
grep -q '&& 1 -eq 0 \]\]' "$T/tools/check_nosandbox.sh" || { echo "could not build the no-sandbox copy"; exit 2; }
fail=0

expect () {  # expected_exit label slug [checker] [options...]
  local want="$1" label="$2" slug="$3" chk="${4:-check_lean.sh}"; shift 3; shift 2>/dev/null || true
  "$T/tools/$chk" "$slug" "$@" >"$T/out.txt" 2>&1; local got=$?
  if [[ $got -eq $want ]]; then echo "ok    $label"
  else echo "FAIL  $label (exit $got, wanted $want)"; sed 's/^/        /' "$T/out.txt" | head -12; fail=1; fi
}
both () {  # label slug : rejected by the real checker AND by the copy without the text scan
  expect 1 "$1" "$2"
  expect 1 "    ...and again with the text scan off" "$2" check_noscan.sh
}
says () {  # pattern label : the last output must contain the pattern
  if grep -qE "$1" "$T/out.txt"; then echo "ok    $2"
  else echo "FAIL  $2"; sed 's/^/        /' "$T/out.txt" | head -12; fail=1; fi
}
put () {  # slug File  (content on stdin)
  mkdir -p "$T/conjectures/$1"; cat > "$T/conjectures/$1/$2.lean"
}
# a statement that is true and easy, and one that is false
true_stmt ()  { put "$1" Statement <<'EOF'
import Mathlib.Order.Basic

/-- Two plus two is four. -/
def Claim : Prop := (2 : Nat) + 2 = 4
EOF
}
false_stmt () { put "$1" Statement <<'EOF'
import Mathlib.Order.Basic

/-- Zero is one. False, so nothing honest proves it. -/
def Claim : Prop := (0 : Nat) = 1
EOF
}

# ============================================================ honest results
put honest Statement <<'EOF'
import Mathlib

/-- There are infinitely many primes. (Uses the axiom of choice somewhere below;
the words "partial order", "local ring" and "syntax" in a comment are harmless.) -/
def Claim : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ p.Prime
EOF
put honest Lemmas <<'EOF'
import conjectures.honest.Statement

theorem bigger_prime (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime := Nat.exists_infinite_primes n
EOF
put honest Proof <<'EOF'
import conjectures.honest.Statement
import conjectures.honest.Lemmas

theorem result : Claim := fun n => bigger_prime n
EOF
expect 0 "accepts an honest result (statement, helper file, proof)" honest
says "^ACCEPTED  slug=honest " "...and says ACCEPTED for that slug"
says "axioms: Classical.choice Quot.sound propext" "...and names the three standard axioms it rests on"
says "files:Statement Lemmas Proof" "...and lists the files it compiled"
SANDBOX=off; grep -q "sandbox: on" "$T/out.txt" && SANDBOX=on
echo "note  sandbox is $SANDBOX on this machine"

true_stmt plain
put plain Proof <<'EOF'
import conjectures.plain.Statement

theorem result : Claim := rfl
EOF
expect 0 "accepts an honest result that needs no axioms" plain
says "axioms: none" "...and reports no axioms"

# a statement with its own definitions: structure, recursion, an instance
put rich Statement <<'EOF'
import Mathlib

structure Pt where
  x : ℕ
  y : ℕ
deriving DecidableEq

def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

def collatzSteps (n : ℕ) (fuel : ℕ) : ℕ :=
  if fuel = 0 then 0 else if n ≤ 1 then 0 else
    1 + collatzSteps (if n % 2 = 0 then n / 2 else 3 * n + 1) (fuel - 1)
termination_by fuel
decreasing_by omega

instance : Add Pt := ⟨fun a b => ⟨a.x + b.x, a.y + b.y⟩⟩

def Claim : Prop := fib 10 = 55 ∧ (⟨1, 2⟩ + ⟨3, 4⟩ : Pt) = ⟨4, 6⟩ ∧ collatzSteps 1 5 = 0
EOF
put rich Proof <<'EOF'
import conjectures.rich.Statement

theorem result : Claim := by
  refine ⟨by decide, rfl, ?_⟩
  unfold collatzSteps
  simp
EOF
expect 0 "accepts a statement with its own structure, recursive defs and instance" rich

# ============================================================ unfinished proofs
false_stmt c_sorry
put c_sorry Proof <<'EOF'
import conjectures.c_sorry.Statement

theorem result : Claim := by sorry
EOF
both "rejects sorry" c_sorry

false_stmt c_sorryax
put c_sorryax Proof <<'EOF'
import conjectures.c_sorryax.Statement

theorem result : Claim := sorryAx _ false
EOF
both "rejects sorryAx used directly (no warning is printed for it)" c_sorryax

# ============================================================ axioms
false_stmt c_axiom
put c_axiom Proof <<'EOF'
import conjectures.c_axiom.Statement

axiom zero_is_one : (0 : Nat) = 1
theorem result : Claim := zero_is_one
EOF
both "rejects an axiom in Proof.lean" c_axiom

false_stmt c_axiom2
put c_axiom2 Proof <<'EOF'
import conjectures.c_axiom2.Statement

namespace Quiet axiom
  zero_is_one : (0 : Nat) = 1 end Quiet
theorem result : Claim := Quiet.zero_is_one
EOF
expect 1 "rejects an axiom written so the text scan misses it" c_axiom2
says "axioms that are not allowed" "...because of the axiom, not the wording"

false_stmt c_helper_axiom
put c_helper_axiom Lib <<'EOF'
import conjectures.c_helper_axiom.Statement

axiom everything : ∀ p : Prop, p
EOF
put c_helper_axiom Proof <<'EOF'
import conjectures.c_helper_axiom.Lib

theorem result : Claim := everything _
EOF
both "rejects an axiom in a helper file" c_helper_axiom

false_stmt c_helper_sorry
put c_helper_sorry Lib <<'EOF'
import conjectures.c_helper_sorry.Statement

theorem everything : ∀ p : Prop, p := by sorry
EOF
put c_helper_sorry Proof <<'EOF'
import conjectures.c_helper_sorry.Lib

theorem result : Claim := everything _
EOF
both "rejects sorry in a helper file" c_helper_sorry

# ------------------------------------------------ hidden in Statement.lean
put c_stmt_axiom Statement <<'EOF'
import Mathlib.Order.Basic

axiom handy : (0 : Nat) = 1
def Claim : Prop := (0 : Nat) = 1
EOF
put c_stmt_axiom Proof <<'EOF'
import conjectures.c_stmt_axiom.Statement

theorem result : Claim := handy
EOF
both "rejects an axiom in Statement.lean" c_stmt_axiom

put c_stmt_axiom_unused Statement <<'EOF'
import Mathlib.Order.Basic

axiom unused : (0 : Nat) = 1
def Claim : Prop := (2 : Nat) + 2 = 4
EOF
put c_stmt_axiom_unused Proof <<'EOF'
import conjectures.c_stmt_axiom_unused.Statement

theorem result : Claim := rfl
EOF
both "rejects an axiom in Statement.lean even when the proof does not use it" c_stmt_axiom_unused

put c_stmt_sorry Statement <<'EOF'
import Mathlib.Order.Basic

def bound : Nat := sorry
def Claim : Prop := bound = bound
EOF
put c_stmt_sorry Proof <<'EOF'
import conjectures.c_stmt_sorry.Statement

theorem result : Claim := rfl
EOF
both "rejects sorry inside a definition in Statement.lean" c_stmt_sorry

put c_stmt_sorry2 Statement <<'EOF'
import Mathlib.Order.Basic

theorem handy : (0 : Nat) = 1 := sorryAx _ false
def Claim : Prop := (0 : Nat) = 1
EOF
put c_stmt_sorry2 Proof <<'EOF'
import conjectures.c_stmt_sorry2.Statement

theorem result : Claim := handy
EOF
both "rejects a sorried lemma in Statement.lean" c_stmt_sorry2

put c_stmt_opaque Statement <<'EOF'
import Mathlib.Order.Basic

opaque mystery : Nat → Prop
def Claim : Prop := ∀ n, mystery n → mystery n
EOF
put c_stmt_opaque Proof <<'EOF'
import conjectures.c_stmt_opaque.Statement

theorem result : Claim := fun _ h => h
EOF
both "rejects an opaque definition in Statement.lean" c_stmt_opaque

put c_stmt_partial Statement <<'EOF'
import Mathlib.Order.Basic

def loops (n : Nat) : Nat := n
namespace Quiet partial def spin (n : Nat) : Nat := spin (n + 1)
end Quiet
def Claim : Prop := loops 1 = 1
EOF
put c_stmt_partial Proof <<'EOF'
import conjectures.c_stmt_partial.Statement

theorem result : Claim := rfl
EOF
expect 1 "rejects a partial definition in Statement.lean that the text scan misses" c_stmt_partial

put c_stmt_unsafe Statement <<'EOF'
import Mathlib.Order.Basic

unsafe def shortcut (n : Nat) : Nat := n
def Claim : Prop := (2 : Nat) + 2 = 4
EOF
put c_stmt_unsafe Proof <<'EOF'
import conjectures.c_stmt_unsafe.Statement

theorem result : Claim := rfl
EOF
both "rejects an unsafe definition in Statement.lean" c_stmt_unsafe

true_stmt c_stmt_local
put c_stmt_local Defs <<'EOF'
def two : Nat := 2
EOF
put c_stmt_local Statement <<'EOF'
import conjectures.c_stmt_local.Defs

def Claim : Prop := two + two = 4
EOF
put c_stmt_local Proof <<'EOF'
import conjectures.c_stmt_local.Statement

theorem result : Claim := rfl
EOF
both "rejects a Statement.lean that pulls its definitions from another local file" c_stmt_local

put c_stmt_notation Statement <<'EOF'
import Mathlib.Order.Basic

notation "ℙ" => True
def Claim : Prop := ℙ
EOF
put c_stmt_notation Proof <<'EOF'
import conjectures.c_stmt_notation.Statement

theorem result : Claim := trivial
EOF
expect 1 "rejects custom notation in Statement.lean" c_stmt_notation

put c_claim_type Statement <<'EOF'
import Mathlib.Order.Basic

def Claim : Type := Nat
EOF
put c_claim_type Proof <<'EOF'
import conjectures.c_claim_type.Statement

def result : Claim := (0 : Nat)
EOF
both "rejects a Claim that is not a Prop" c_claim_type

put c_claim_univ Statement <<'EOF'
import Mathlib.Order.Basic

universe u
def Claim : Prop := ∀ (α : Type u) (a : α), a = a
EOF
put c_claim_univ Proof <<'EOF'
import conjectures.c_claim_univ.Statement

theorem result : Claim := fun _ _ => rfl
EOF
both "rejects a Claim with a universe parameter (fix the universe in the statement)" c_claim_univ

# ============================================================ proving something else
false_stmt c_true
put c_true Proof <<'EOF'
import conjectures.c_true.Statement

theorem result : True := trivial
EOF
both "rejects  theorem result : True" c_true

false_stmt c_redefine
put c_redefine Proof <<'EOF'
import Mathlib.Order.Basic

def Claim : Prop := True
theorem result : Claim := trivial
EOF
both "rejects a Proof.lean that defines its own Claim instead of importing the statement" c_redefine

false_stmt c_redefine_ns
put c_redefine_ns Proof <<'EOF'
import conjectures.c_redefine_ns.Statement

namespace Mine
def Claim : Prop := True
theorem result : Claim := trivial
end Mine
open Mine
EOF
both "rejects a Claim and result redefined inside a namespace" c_redefine_ns

false_stmt c_export
put c_export Proof <<'EOF'
import conjectures.c_export.Statement

namespace Mine
def Claim : Prop := True
theorem result : Claim := trivial
end Mine
export Mine (result Claim)
EOF
both "rejects a namespaced Claim and result exported to the top level" c_export

false_stmt c_shadow
put c_shadow Proof <<'EOF'
import conjectures.c_shadow.Statement

namespace Mine
def Claim : Prop := True
end Mine
open Mine in
theorem result : Mine.Claim := trivial
EOF
both "rejects a result about a different Claim" c_shadow

true_stmt c_def
put c_def Lib <<'EOF'
import conjectures.c_def.Statement

theorem result : Claim := rfl
EOF
put c_def Proof <<'EOF'
import conjectures.c_def.Lib
EOF
both "rejects a result that lives in a helper file, not in Proof.lean" c_def

# syntax tricks: make the word `Claim` mean True in every file that comes after
false_stmt c_token
put c_token Proof <<'EOF'
import conjectures.c_token.Statement

notation "Claim" => True
theorem result : Claim := trivial
EOF
both "rejects a Proof.lean that turns the word Claim into notation for True" c_token
says "not literally|does not give" "...and says why"

# the same idea aimed at the checker's own  #print axioms  line
false_stmt c_print
put c_print Proof <<'EOF'
import conjectures.c_print.Statement
import Lean
open Lean Elab Command

axiom zero_is_one : (0 : Nat) = 1
theorem result : Claim := zero_is_one

elab_rules : command
  | `(#print axioms $_) => logInfo "'checker_generated_check' does not depend on any axioms"
EOF
both "rejects a Proof.lean that rewrites what  #print axioms  prints" c_print
says "axioms that are not allowed|zero_is_one" "...and the axiom is still found from the proof terms"

# ============================================================ extra axioms, compiler trust
put c_native Statement <<'EOF'
import Mathlib.Order.Basic

def Claim : Prop := (2 : Nat) ^ 10 = 1024
EOF
put c_native Proof <<'EOF'
import conjectures.c_native.Statement

theorem result : Claim := by native_decide
EOF
both "rejects native_decide" c_native

put c_native2 Statement <<'EOF'
import Mathlib.Order.Basic

def Claim : Prop := (2 : Nat) ^ 10 = 1024
EOF
put c_native2 Proof <<'EOF'
import conjectures.c_native2.Statement

theorem result : Claim := by unfold Claim; decide +native
EOF
expect 1 "rejects  decide +native  (same thing, different spelling)" c_native2
says "axioms that are not allowed" "...because of the axiom it brings in"

put c_reducebool Statement <<'EOF'
import Mathlib.Order.Basic

def Claim : Prop := (2 : Nat) ^ 10 = 1024
EOF
put c_reducebool Proof <<'EOF'
import conjectures.c_reducebool.Statement

theorem result : Claim := of_decide_eq_true (Lean.ofReduceBool (decide ((2 : Nat) ^ 10 = 1024)) true rfl)
EOF
both "rejects the compiler-trust axiom used by hand" c_reducebool

# ============================================================ filed under another slug
true_stmt easy
put easy Proof <<'EOF'
import conjectures.easy.Statement

theorem result : Claim := rfl
EOF
expect 0 "accepts the easy conjecture used by the next tests" easy

false_stmt hard
cp "$T/conjectures/easy/Proof.lean" "$T/conjectures/hard/Proof.lean"
both "rejects a proof of one conjecture filed under another" hard
sed 's/conjectures\.easy/conjectures.hard/' "$T/conjectures/easy/Proof.lean" > "$T/conjectures/hard/Proof.lean"
both "rejects it again when the import is changed to the new slug" hard

# a proof that imports the easy statement next to its own
false_stmt hard2
put hard2 Proof <<'EOF'
import conjectures.easy.Statement

theorem result : Claim := rfl
EOF
cp "$T/conjectures/easy/Statement.lean" "$T/conjectures/hard2/Easy.lean"
both "rejects a proof that reaches for another conjecture's files" hard2

# a second statement smuggled in as a helper and proved instead
false_stmt hard3
put hard3 Easy <<'EOF'
import Mathlib.Order.Basic

def Claim : Prop := (2 : Nat) + 2 = 4
EOF
put hard3 Proof <<'EOF'
import conjectures.hard3.Easy

theorem result : Claim := rfl
EOF
both "rejects a proof of a look-alike Claim kept in a helper file" hard3

# ============================================================ getting past the kernel
# A custom tactic closes the goal with a term of the wrong type, and an option
# tells Lean not to kernel-check the declaration. Nothing is reported as an axiom.
false_stmt c_skipkernel
put c_skipkernel Proof <<'EOF'
import conjectures.c_skipkernel.Statement
import Lean
open Lean Elab Tactic

elab "close_anyway" : tactic => do (← getMainGoal).assign (mkConst ``True.intro)

set_option debug.skipKernelTC true in
theorem result : Claim := by close_anyway
EOF
both "rejects a declaration slipped past the kernel (skipKernelTC)" c_skipkernel
says "kernel does not accept|replayed" "...and it is the kernel replay that catches it"

# ============================================================ running code while compiling
MARK1="$T/pwned"; MARK2="/tmp/bb25_lean_checker_test_$$"; MARK3="$T/conjectures/c_io/pwned"
true_stmt c_io
put c_io Proof <<EOF
import conjectures.c_io.Statement
import Lean
open Lean Elab Command

run_cmd do
  for f in ["$MARK1", "$MARK2", "$MARK3"] do
    try IO.FS.writeFile f "written by a proof file" catch _ => pure ()

theorem result : Claim := rfl
EOF
expect 1 "rejects a proof file that runs its own code while compiling" c_io
if [[ $SANDBOX == on ]]; then
  expect 0 "    with the text scan off the (otherwise honest) proof passes..." c_io check_noscan.sh
  if [[ -e "$MARK1" || -e "$MARK2" || -e "$MARK3" ]]; then echo "FAIL  ...but its code wrote outside the sandbox"; fail=1
  else echo "ok    ...and its code could not write anywhere outside the sandbox"; fi
else
  echo "skip  sandbox test (needs Linux, root, unshare, setpriv)"
fi
rm -f "$MARK1" "$MARK2" "$MARK3"

# the same, through a tactic hook, written with no word that the text scan knew
# when this was found (it ran, and wrote files, when compiled outside the sandbox)
true_stmt c_sneak
sed -i 's/import Mathlib.Order.Basic/import Mathlib/' "$T/conjectures/c_sneak/Statement.lean"
put c_sneak Proof <<EOF
import conjectures.c_sneak.Statement

open Lean Aesop in
def sneaky : RuleTac := fun _ => do
  for f in ["$MARK1", "$MARK2", "$MARK3"] do
    try writeModule (← getEnv) f catch _ => pure ()
  throwError "no"

attribute [aesop safe tactic] sneaky

theorem result : Claim := by
  first
    | (have h : ∀ f : ℕ → ℕ, f 0 = f 1 := by aesop); exact absurd (h id) (by decide)
    | rfl
EOF
expect 1 "rejects code run through an aesop rule (words added to the scan after it got through)" c_sneak
if [[ $SANDBOX == on ]]; then
  expect 0 "    with the text scan off the (otherwise honest) proof passes..." c_sneak check_noscan.sh
  if [[ -e "$MARK1" || -e "$MARK2" || -e "$MARK3" ]]; then echo "FAIL  ...but its code wrote outside the sandbox"; fail=1
  else echo "ok    ...and its code could not write anywhere outside the sandbox"; fi
fi
rm -f "$MARK1" "$MARK2" "$MARK3"

# start-up code that prints the answer the checker's own file is expected to
# print, then stops Lean before that file is looked at. This does fool step 4.
false_stmt c_spoof
put c_spoof Proof <<'EOF'
import conjectures.c_spoof.Statement
import Lean

initialize
  IO.println "'checker_generated_check' does not depend on any axioms"
  (← IO.getStdout).flush
  IO.Process.exit 0

axiom zero_is_one : (0 : Nat) = 1
theorem result : Claim := zero_is_one
EOF
both "rejects start-up code that prints the expected answer and stops Lean (axiom underneath)" c_spoof
says "axioms that are not allowed: zero_is_one" "...caught by walking the proof terms, after step 4 was fooled"

false_stmt c_spoof2
put c_spoof2 Proof <<'EOF'
import conjectures.c_spoof2.Statement
import Lean
open Lean Elab Tactic

initialize
  IO.println "'checker_generated_check' does not depend on any axioms"
  (← IO.getStdout).flush
  IO.Process.exit 0

elab "close_anyway" : tactic => do (← getMainGoal).assign (mkConst ``True.intro)

set_option debug.skipKernelTC true in
theorem result : Claim := by close_anyway
EOF
both "rejects the same start-up trick with an unchecked proof and no axiom at all" c_spoof2
says "kernel does not accept" "...caught by the kernel replay, after steps 4 and 5 saw nothing wrong"

# the proof file tries to swap the compiled statement for an easier one
false_stmt c_swap
put c_swap Proof <<'EOF'
import conjectures.c_swap.Statement
import Lean
open Lean Elab Command

run_cmd do
  let some lp ← IO.getEnv "LEAN_PATH" | pure ()
  let lib := (lp.splitOn ":").head!
  let target : System.FilePath := lib / "conjectures" / "c_swap" / "Statement.olean"
  let donor : System.FilePath := lib / "conjectures" / "c_swap" / "Easy.olean"
  try IO.FS.writeBinFile target (← IO.FS.readBinFile donor) catch _ => pure ()

theorem result : Claim := rfl
EOF
put c_swap Easy <<'EOF'
import Mathlib.Order.Basic

def Claim : Prop := (0 : Nat) = 0
EOF
sed -i '1a import conjectures.c_swap.Easy' "$T/conjectures/c_swap/Proof.lean"
both "rejects a proof file that tries to swap the compiled statement" c_swap

# ============================================================ without the sandbox
# (what happens on a machine that is not Linux-as-root)
expect 0 "without a sandbox an honest result is still accepted..." plain check_nosandbox.sh
says "sandbox: off" "...the report says the sandbox was off"
says "WARNING: no sandbox" "...and warns about it"
expect 1 "without a sandbox sorry is still rejected" c_sorry check_nosandbox.sh
expect 1 "without a sandbox the unchecked proof is still rejected" c_skipkernel check_nosandbox.sh
expect 2 "--require-sandbox refuses to run without one" plain check_nosandbox.sh --require-sandbox

# ============================================================ files and names
true_stmt c_noproof
expect 1 "rejects a missing Proof.lean" c_noproof
expect 1 "rejects a slug with no folder" nothing_here
expect 2 "refuses a slug that is not a plain name" "../honest"
expect 2 "refuses a slug with a dot" "honest.Proof"

true_stmt c_symlink
ln -s "$T/conjectures/easy/Proof.lean" "$T/conjectures/c_symlink/Proof.lean"
expect 1 "rejects a symlinked Proof.lean" c_symlink

true_stmt c_module
put c_module Proof <<'EOF'
module
import conjectures.c_module.Statement

theorem result : Claim := rfl
EOF
expect 1 "rejects a file that uses the module system" c_module

true_stmt c_circle
put c_circle A <<'EOF'
import conjectures.c_circle.B
EOF
put c_circle B <<'EOF'
import conjectures.c_circle.A
EOF
put c_circle Proof <<'EOF'
import conjectures.c_circle.Statement
import conjectures.c_circle.A

theorem result : Claim := rfl
EOF
expect 1 "rejects helper files that import each other in a circle" c_circle

true_stmt c_error
put c_error Proof <<'EOF'
import conjectures.c_error.Statement

theorem result : Claim := by simp [this_lemma_does_not_exist]
EOF
both "rejects a proof that does not compile" c_error

# ============================================================ the checker itself
( cd "$T" && git init -q . && git add tools/check_lean.sh \
  && git -c user.name=t -c user.email=t@t commit -q -m checker ) >/dev/null 2>&1
expect 0 "accepts with --trusted-ref when the checker matches that ref" easy check_lean.sh --trusted-ref HEAD
says "same as HEAD" "...and says so"
cp "$T/tools/check_noscan.sh" "$T/tools/check_lean.sh"
expect 2 "refuses to run a checker that differs from the trusted ref" easy check_lean.sh --trusted-ref HEAD
cp "$SRC/tools/check_lean.sh" "$T/tools/check_lean.sh"

mkdir -p "$T/bare/tools" "$T/bare/conjectures"; cp "$SRC/tools/check_lean.sh" "$T/bare/tools/"
cp -r "$T/conjectures/easy" "$T/bare/conjectures/"
"$T/bare/tools/check_lean.sh" easy >"$T/out.txt" 2>&1; got=$?
if [[ $got -eq 2 ]]; then echo "ok    refuses to judge without the pinned Mathlib"
else echo "FAIL  judged without Mathlib (exit $got)"; fail=1; fi

exit $fail
