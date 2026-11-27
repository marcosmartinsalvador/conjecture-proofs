#!/usr/bin/env bash
# check_lean.sh - THE lane A checker. A conjecture is machine-checked only if this
# script prints ACCEPTED. (Whether Statement.lean says what the paper meant is a
# separate, human-style judgement: conjectures/<slug>/REVIEW.md.)
#
#   tools/check_lean.sh <slug> [--trusted-ref <git-ref>] [--require-sandbox] [--fresh]
#
# The files are conjectures/<slug>/Statement.lean  (defines `def Claim : Prop := ...`)
#           and conjectures/<slug>/Proof.lean      (proves  `theorem result : Claim`),
# plus optional helper files conjectures/<slug>/<Name>.lean that Proof.lean imports.
#
# What it does
#   0. Checks the tools are the pinned ones: the Lean commit and the Mathlib commit
#      written below, and every Mathlib dependency at the commit Mathlib itself pins,
#      all with unmodified sources. The pins live in this file on purpose.
#   1. Copies ONLY this slug's .lean files to a scratch directory. Nothing else in
#      the repository is visible to the build, so a proof cannot lean on another
#      slug's files or on stale build output.
#   2. Refuses text that has no business in these files (see BANNED_* below).
#      Crude on purpose: it also fires inside comments and strings.
#   3. Compiles Statement.lean, then Proof.lean and the helpers it imports, with the
#      pinned `lean` against the pinned Mathlib ("the project builds").
#   4. Writes ITS OWN file
#          import conjectures.<slug>.Statement
#          import conjectures.<slug>.Proof
#          theorem checker_generated_check : Claim := result
#          #print axioms checker_generated_check
#      compiles it, and accepts only propext, Classical.choice, Quot.sound.
#   5. Runs its own Lean program (embedded below) that loads the compiled files as
#      DATA, without running any of their code or syntax, and checks:
#        - `Claim` is a plain def of type Prop declared in this slug's Statement.lean;
#        - `result` is a theorem declared in this slug's Proof.lean whose statement
#          is literally `Claim`;
#        - the axioms under `result`, found by walking the proof terms, are allowed;
#        - Statement.lean declares no axiom, no opaque/partial/unsafe constant,
#          nothing resting on sorry, and imports no local file.
#      Step 4 can be fooled by a proof file that redefines syntax, or whose start-up
#      code prints the expected line and stops Lean (both are in the tests); step 5
#      cannot, because it never runs or parses anything the slug's files define.
#   6. Replays every declaration of the slug's files through the Lean kernel in a
#      fresh process (`leanchecker`), which catches declarations that were slipped
#      into the environment without being checked. With --fresh it replays
#      everything, Mathlib included, from an empty environment (slow).
#
# Sandbox. Compiling a Lean file runs whatever code that file contains. On Linux as
# root (the cloud sessions) every step that touches the slug's files runs as user
# `nobody`, with no network, in its own process namespace, with the whole
# filesystem read-only except one scratch directory. Elsewhere the sandbox is off,
# the ACCEPTED block says so, and step 2 is the only guard against a proof file
# that tampers with the machine. Step 2 is a word list and cannot be complete (the
# tests include a file with no banned word that still ran code, before the words
# it used were added). --require-sandbox turns "off" into an error.
#
# Known limits: the installed Lean and the compiled Mathlib under .lake/ are
# trusted as they are on this machine (re-check results in a fresh session); and
# a proof file that does get to run code can leave a hand-made compiled file in
# the sandbox, which steps 5-6 re-check as data but must first load with Lean's
# own loader, which is not hardened against deliberately malformed files.
#
# --trusted-ref REF: refuse to run unless this script is byte-identical to the
# one at REF. Use `--trusted-ref main` when judging a branch.
#
# Exit code 0 = ACCEPTED, 1 = REJECTED, 2 = usage or setup error.
set -uo pipefail
export LC_ALL=C

PIN_TOOLCHAIN="leanprover/lean4:v4.36.0"
PIN_LEAN_GITHASH="611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9"
PIN_MATHLIB_REV="fc4f59e577feb1a4956671bc04ac18aaaf8cd842"   # Mathlib tag v4.36.0
ALLOWED_AXIOMS="propext Classical.choice Quot.sound"

ROOT="$(cd -P "$(dirname "$0")/.." && pwd -P)"
SELF="$(cd -P "$(dirname "$0")" && pwd -P)/$(basename "$0")"
SLUG="${1:-}"; shift 2>/dev/null || true
REF=""; REQUIRE_SANDBOX=0; FRESH=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --trusted-ref) REF="${2:-}"; [[ -n "$REF" ]] || { echo "--trusted-ref needs a ref" >&2; exit 2; }; shift 2 ;;
    --require-sandbox) REQUIRE_SANDBOX=1; shift ;;
    --fresh) FRESH=1; shift ;;
    *) echo "unknown option $1" >&2; exit 2 ;;
  esac
done
[[ "$SLUG" =~ ^[A-Za-z][A-Za-z0-9_]{0,63}$ ]] || {
  echo "usage: check_lean.sh <slug> [--trusted-ref REF] [--require-sandbox] [--fresh]" >&2
  echo "       a slug is letters, digits and _ only, starting with a letter" >&2; exit 2; }

setup_error () { echo "SETUP ERROR: $*" >&2; echo "            see conjectures/SETUP.md (usually: ./setup.sh)" >&2; exit 2; }
rejected ()    { echo "REJECTED: $*"; exit 1; }

# --- this script against the trusted ref
if [[ -n "$REF" ]]; then
  git -C "$ROOT" cat-file -e "$REF:tools/check_lean.sh" 2>/dev/null \
    || setup_error "ref $REF has no tools/check_lean.sh to compare with"
  [[ "$(git -C "$ROOT" show "$REF:tools/check_lean.sh" | sha256sum)" == "$(sha256sum < "$SELF")" ]] \
    || setup_error "this checker differs from the one at $REF; run that one"
fi

# --- 0. the pinned tools
TC=""
cand="${ELAN_HOME:-$HOME/.elan}/toolchains/leanprover--lean4---v4.36.0"
[[ -x "$cand/bin/lean" ]] && TC="$(cd -P "$cand" && pwd -P)"
[[ -n "$TC" ]] || setup_error "Lean toolchain $PIN_TOOLCHAIN is not installed"
[[ "$("$TC/bin/lean" --githash 2>/dev/null)" == "$PIN_LEAN_GITHASH" ]] \
  || setup_error "the lean binary in $TC is not commit $PIN_LEAN_GITHASH"
[[ -x "$TC/bin/leanchecker" ]] || setup_error "leanchecker is missing from the toolchain"

[[ -d "$ROOT/.lake/packages/mathlib" ]] || setup_error "Mathlib is not there (.lake/packages/mathlib)"
PKGS="$(cd -P "$ROOT/.lake/packages" && pwd -P)"
check_pkg () {  # name expected-rev
  local d="$PKGS/$1"
  [[ -d "$d/.git" ]] || setup_error "package $1 is missing"
  [[ "$(git -C "$d" rev-parse HEAD 2>/dev/null)" == "$2" ]] || setup_error "package $1 is not at the pinned commit $2"
  [[ -z "$(git -C "$d" status --porcelain 2>/dev/null | head -1)" ]] || setup_error "package $1 has modified or added source files"
}
check_pkg mathlib "$PIN_MATHLIB_REV"
DEPS="$(python3 -I -c '
import json, re, sys
m = json.load(open(sys.argv[1]))
for p in m["packages"]:
    n, r = p["name"], p["rev"]
    assert re.fullmatch(r"[A-Za-z0-9_]+", n) and re.fullmatch(r"[0-9a-f]{40}", r)
    print(n, r)
' "$PKGS/mathlib/lake-manifest.json")" || setup_error "cannot read Mathlib's own manifest"
LIBDIRS="$PKGS/mathlib/.lake/build/lib/lean"
PKGNAMES="mathlib"
while read -r name rev; do
  [[ -n "$name" ]] || continue
  check_pkg "$name" "$rev"
  LIBDIRS="$LIBDIRS $PKGS/$name/.lake/build/lib/lean"
  PKGNAMES="$PKGNAMES $name"
done <<< "$DEPS"
[[ -f "$PKGS/mathlib/.lake/build/lib/lean/Mathlib.olean" ]] || setup_error "Mathlib is not built (no Mathlib.olean)"

# --- 1. this slug's files, and only these
DIR="$ROOT/conjectures/$SLUG"
[[ -d "$DIR" && ! -L "$DIR" ]] || rejected "conjectures/$SLUG does not exist"
for need in Statement Proof; do
  [[ -f "$DIR/$need.lean" ]] || rejected "conjectures/$SLUG/$need.lean does not exist"
done

WORK="$(mktemp -d)"; chmod 755 "$WORK"
cleanup () { chmod -R u+rwX "$WORK" 2>/dev/null; rm -rf "$WORK"; }
trap cleanup EXIT
SRC="$WORK/src/conjectures/$SLUG"; LIB="$WORK/lib"; RW="$WORK/rw"; CHK="$WORK/chk"
mkdir -p "$SRC" "$LIB/conjectures/$SLUG" "$RW" "$CHK" "$WORK/tc" "$WORK/pkgs" "$WORK/log"

MODS=""
for f in "$DIR"/*.lean; do
  b="$(basename "$f" .lean)"
  [[ -f "$f" && ! -L "$f" ]] || rejected "conjectures/$SLUG/$b.lean is not a regular file"
  [[ "$b" =~ ^[A-Za-z][A-Za-z0-9_]*$ ]] || rejected "file name $b.lean: use letters, digits and _ only, starting with a letter"
  cp "$f" "$SRC/$b.lean"
  MODS="$MODS $b"
done
if find "$DIR" -mindepth 2 -name '*.lean' | grep -q .; then
  rejected "conjectures/$SLUG has .lean files in subfolders; keep them directly in conjectures/$SLUG"
fi
chmod -R a+rX "$WORK/src"

# --- 2. text that has no business here (fires inside comments and strings too)
L='(^|[^A-Za-z0-9_'"'"'])'; R='($|[^A-Za-z0-9_'"'"'])'
# Everywhere. First the words that leave a proof unfinished or trust the compiler
# (steps 4-6 catch these anyway; this just says so early). Then every way we know
# of making a file run its own code while it is being compiled, which without the
# sandbox is the only guard there is.
BANNED_ALL='sorry|sorryAx|admit|native_decide|ofReduceBool|reduceBool|trustCompiler'
BANNED_ALL="$BANNED_ALL"'|unsafe|unsafeCast|implemented_by|extern|skipKernelTC|run_cmd|run_elab|run_meta|run_tac|by_elab|initialize|builtin_initialize|elab|elab_rules|simproc|dsimproc|simproc_decl|include_str|IO|BaseIO|EIO|MetaM|TacticM|CoreM|TermElabM|CommandElabM|DelabM|Elab|Meta|Delaborator|addDecl|addDeclCore|modifyEnv|setEnv|getEnv|saveModuleData|writeModule|evalConst|evalExpr|RuleTac|SingleRuleTac|SimpleRuleTac|TacGen|polyrith'
# `axiom name :` as a declaration (so "the axiom of choice" in a comment is fine)
BANNED_AXIOM='axiom[[:space:]]+[^[:space:]]+[[:space:]]*[:({[]'
# Statement.lean only, at the start of a line: commands that could make the
# statement read differently from what it says, or hide part of it
BANNED_STMT='opaque|partial|macro|macro_rules|syntax|notation|notation3|infix|infixl|infixr|prefix|postfix|declare_syntax_cat|binder_predicate|set_option|attribute|local|scoped|unseal|seal|irreducible_def'
scan () {  # label regex files...
  local label="$1" re="$2"; shift 2
  if grep -nE "$re" "$@" /dev/null > "$WORK/log/banned.txt"; then
    echo "REJECTED: $label"
    sed -e "s|^$SRC/||" -e 's/^/    /' "$WORK/log/banned.txt" | cut -c1-200 | head -20
    exit 1
  fi
}
ALLFILES=(); for b in $MODS; do ALLFILES+=("$SRC/$b.lean"); done
scan "banned text (it counts inside comments and strings too):" "${L}(${BANNED_ALL})${R}" "${ALLFILES[@]}"
scan "banned text (it counts inside comments and strings too):" "${L}${BANNED_AXIOM}" "${ALLFILES[@]}"
scan "banned text (it counts inside comments and strings too):" '#eval|#exit|#loogle|#leansearch|#moogle|#statesearch|#search|debug\.|@\[[^]]*(init|export|extern|implemented_by|tactic|command_elab|term_elab|macro|builtin|app_delab|delab|unexpand)' "${ALLFILES[@]}"
scan "the module system is not accepted here (plain files only):" '^[[:space:]]*module([[:space:]]|$)|import[[:space:]]+all[[:space:]]|(public|meta)[[:space:]]+import' "${ALLFILES[@]}"
scan "Statement.lean may not use these commands (a line may not start with them, even in a comment):" "^[[:space:]]*(@\[[^]]*\][[:space:]]*)*((private|protected|noncomputable|nonrec)[[:space:]]+)*(${BANNED_STMT})${R}" "$SRC/Statement.lean"

# local imports: only this slug's own files, and none at all in Statement.lean
local_imports () {  # file -> helper names, one per line
  grep -oE 'import[[:space:]]+[^[:space:]]+' "$1" | sed -E 's/^import[[:space:]]+//' \
    | grep -E '^(«)?conjectures' || true
}
for b in $MODS; do
  while read -r imp; do
    [[ -n "$imp" ]] || continue
    if [[ "$imp" =~ ^conjectures\.${SLUG}\.([A-Za-z][A-Za-z0-9_]*)$ ]]; then
      [[ -f "$SRC/${BASH_REMATCH[1]}.lean" ]] || rejected "$b.lean imports $imp, which is not a file of this conjecture"
      [[ "$b" != Statement ]] || rejected "Statement.lean imports a local file ($imp); it must stand on its own"
    else
      rejected "$b.lean imports $imp; only this conjecture's own files (conjectures.$SLUG.*) may be imported"
    fi
  done <<< "$(local_imports "$SRC/$b.lean")"
done

# --- the sandbox
cat > "$WORK/sandbox_inner.sh" <<'EOF'
#!/bin/bash
# args: WORK TC PKGS RW -- command...
WORK="$1"; TC="$2"; PKGS="$3"; RW="$4"; shift 5
mount --make-rprivate / || exit 97
mount --bind "$TC" "$WORK/tc" || exit 97
mount --bind "$PKGS" "$WORK/pkgs" || exit 97
mount --bind "$RW" "$RW" || exit 97
awk '{print $5}' /proc/self/mountinfo | while read -r mp; do
  mp="$(printf '%b' "$mp")"
  [[ "$mp" == "$RW" ]] && continue
  mount -o remount,bind,ro "$mp" 2>/dev/null
done
cd "$RW" || exit 97
exec setpriv --reuid=65534 --regid=65534 --clear-groups --no-new-privs \
     --bounding-set=-all --inh-caps=-all -- "$@"
EOF
chmod 755 "$WORK/sandbox_inner.sh"

SANDBOX=off; TCX="$TC"; PKGX="$PKGS"
in_sandbox () {  # command...   (cwd = $RW, clean environment)
  if [[ $SANDBOX == on ]]; then
    unshare --mount --net --pid --ipc --fork --kill-child --mount-proc -- \
      "$WORK/sandbox_inner.sh" "$WORK" "$TC" "$PKGS" "$RW" -- \
      env -i PATH="$WORK/tc/bin:/usr/bin:/bin" HOME="$RW" TMPDIR="$RW" LEAN_PATH="$LEAN_PATH_X" "$@"
  else
    ( cd "$RW" && env -i PATH="$TC/bin:/usr/bin:/bin" HOME="$RW" TMPDIR="$RW" LEAN_PATH="$LEAN_PATH_X" "$@" )
  fi
}
fresh_rw () { chmod -R u+rwX "$RW" 2>/dev/null; rm -rf "$RW"; mkdir -p "$RW"; if [[ $SANDBOX == on ]]; then chown 65534:65534 "$RW"; fi; chmod 755 "$RW"; }

LEAN_PATH_X=""
if [[ "$(uname -s)" == Linux && "$(id -u)" -eq 0 ]] && command -v unshare >/dev/null && command -v setpriv >/dev/null; then
  SANDBOX=on; fresh_rw
  # the downloaded Mathlib cache unpacks its files owner-only; `nobody` must be able to read them
  for d in $LIBDIRS; do
    if [[ -n "$(find "$d" ! -perm -o+r -print -quit 2>/dev/null)" ]]; then chmod -R a+rX "$d"; fi
  done
  # self-test: we are nobody, the toolchain runs, and nothing but $RW can be written
  probe='[ "$(id -u)" = 65534 ] && head -c 8 "$0/pkgs/mathlib/.lake/build/lib/lean/Mathlib.olean" >/dev/null && lean --githash && touch ./ok && ! touch "$0/src/x" 2>/dev/null && ! touch "$0/lib/x" 2>/dev/null && ! touch "$0/chk/x" 2>/dev/null && ! touch /tmp/x_$$ 2>/dev/null && ! touch "$1/x" 2>/dev/null'
  if [[ "$(in_sandbox bash -c "$probe" "$WORK" "$ROOT" 2>/dev/null | tail -1)" == "$PIN_LEAN_GITHASH" && -f "$RW/ok" ]]; then
    TCX="$WORK/tc"; PKGX="$WORK/pkgs"
  else
    SANDBOX=off
  fi
fi
if [[ $SANDBOX == off && $REQUIRE_SANDBOX -eq 1 ]]; then
  setup_error "the sandbox is not available here (needs Linux, root, unshare, setpriv) and --require-sandbox was given"
fi
LEAN_PATH_X="$LIB"
for n in $PKGNAMES; do LEAN_PATH_X="$LEAN_PATH_X:$PKGX/$n/.lake/build/lib/lean"; done

# --- 3. compile
compile () {  # module-name  -> $LIB/conjectures/$SLUG/<name>.olean, log in $WORK/log/<name>.txt
  local b="$1"; fresh_rw
  in_sandbox lean -R "$WORK/src" -o "$RW/out.olean" "$SRC/$b.lean" > "$WORK/log/$b.txt" 2>&1; local rc=$?
  [[ $rc -eq 0 ]] || return 1
  # a clean compile prints nothing but warnings; `sorry` is a warning, so look for it
  if grep -qE "declaration uses .?sorry" "$WORK/log/$b.txt"; then echo "(the file uses sorry)" >> "$WORK/log/$b.txt"; return 1; fi
  [[ -f "$RW/out.olean" && ! -L "$RW/out.olean" ]] || { echo "(no compiled output)" >> "$WORK/log/$b.txt"; return 1; }
  install -m 644 "$RW/out.olean" "$LIB/conjectures/$SLUG/$b.olean"
}
show_log () { sed -e "s|$WORK/src/||g" -e 's/^/    /' "$WORK/log/$1.txt" | cut -c1-300 | head -40; }

compile Statement || { echo "REJECTED: Statement.lean does not compile cleanly:"; show_log Statement; exit 1; }
STMT_SHA="$(sha256sum "$LIB/conjectures/$SLUG/Statement.olean" | cut -c1-64)"

declare -A STATE=( [Statement]=done )
BUILT="Statement"
build () {  # helper-or-Proof, dependencies first
  local b="$1" imp
  case "${STATE[$b]:-}" in
    done) return 0 ;;
    busy) rejected "the files of this conjecture import each other in a circle (at $b.lean)" ;;
  esac
  STATE[$b]=busy
  while read -r imp; do
    [[ -n "$imp" ]] || continue
    build "${imp##*.}"
  done <<< "$(local_imports "$SRC/$b.lean")"
  compile "$b" || { echo "REJECTED: $b.lean does not compile cleanly:"; show_log "$b"; exit 1; }
  STATE[$b]=done; BUILT="$BUILT $b"
}
build Proof
[[ "$(sha256sum "$LIB/conjectures/$SLUG/Statement.olean" | cut -c1-64)" == "$STMT_SHA" ]] \
  || rejected "the compiled statement changed while the proof was being compiled"

# --- 4. the checker's own statement of the result
cat > "$CHK/Check.lean" <<EOF
import conjectures.${SLUG}.Statement
import conjectures.${SLUG}.Proof
theorem checker_generated_check : Claim := result
#print axioms checker_generated_check
EOF
chmod -R a+rX "$CHK" "$LIB"
fresh_rw
in_sandbox lean "$CHK/Check.lean" > "$WORK/log/check.txt" 2>&1 \
  || { echo "REJECTED: Proof.lean does not give  result : Claim  for conjectures/$SLUG/Statement.lean:"
       sed -e "s|$CHK/||g" -e 's/^/    /' "$WORK/log/check.txt" | cut -c1-300 | head -30; exit 1; }
PRINTED="$(tr '\n' ' ' < "$WORK/log/check.txt" | sed -E 's/[[:space:]]+/ /g; s/^ //; s/ $//')"
if [[ "$PRINTED" == "'checker_generated_check' does not depend on any axioms" ]]; then
  AX4=""
elif [[ "$PRINTED" =~ ^\'checker_generated_check\'\ depends\ on\ axioms:\ \[([A-Za-z0-9_.,\ ]+)\]$ ]]; then
  AX4="$(echo "${BASH_REMATCH[1]}" | tr -d ',' | tr ' ' '\n' | sort | tr '\n' ' ' | sed 's/ $//')"
else
  echo "REJECTED: unexpected output from the checker's own file:"; sed 's/^/    /' "$WORK/log/check.txt" | cut -c1-300 | head -30; exit 1
fi
for a in $AX4; do
  [[ " $ALLOWED_AXIOMS " == *" $a "* ]] || { echo "REJECTED: the proof depends on axioms that are not allowed:"; sed 's/^/    /' "$WORK/log/check.txt" | cut -c1-300 | head -30; exit 1; }
done

# --- 5. the checker's own inspection of the compiled files, as data
cat > "$CHK/Verify.lean" <<'EOF'
import Lean
open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure AxState where
  visited : NameSet := {}
  axioms  : Array Name := #[]
  missing : Array Name := #[]

/-- Every axiom reachable from `root`, found by walking the kernel terms themselves
(no cached tables, no environment extensions). -/
partial def axiomsOf (kenv : Kernel.Environment) (root : Name) : AxState :=
  go root {}
where
  go (n : Name) (s : AxState) : AxState :=
    if s.visited.contains n then s else
    let s := { s with visited := s.visited.insert n }
    match kenv.find? n with
    | none => { s with missing := s.missing.push n }
    | some ci =>
      let s := if ci matches .axiomInfo _ then { s with axioms := s.axioms.push n } else s
      let s := goExpr ci.type s
      match ci with
      | .defnInfo v   => goExpr v.value s
      | .thmInfo v    => goExpr v.value s
      | .opaqueInfo v => goExpr v.value s
      | .inductInfo v => v.ctors.foldl (fun s c => go c s) s
      | .recInfo v    => v.rules.foldl (fun s r => goExpr r.rhs s) s
      | _ => s
  goExpr (e : Expr) (s : AxState) : AxState :=
    e.getUsedConstants.foldl (fun s c => go c s) s

def fmtNames (ns : Array Name) : String :=
  " ".intercalate (ns.qsort Name.lt |>.toList.map toString)

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

unsafe def run (slug : String) : IO UInt32 := do
  let slugRoot := (`conjectures).str slug
  let stmtMod := slugRoot.str "Statement"
  let proofMod := slugRoot.str "Proof"
  initSearchPath (← findSysroot)
  -- loadExts := false: nothing from the imported files is executed
  let env ← importModules #[{ module := stmtMod }, { module := proofMod }] {} (loadExts := false)
  let kenv := env.toKernelEnv
  let mut problems : Array String := #[]
  let names := env.header.moduleNames
  let some stmtIdx := names.idxOf? stmtMod | throw <| IO.userError "statement module not loaded"
  let modOf (n : Name) : Option Name := (env.getModuleIdxFor? n).bind fun i => names[i.toNat]?
  -- local modules: this slug only, plain files, and the statement imports none of them
  for h : i in [0:names.size] do
    let m := names[i]
    if (`conjectures).isPrefixOf m then
      unless slugRoot.isPrefixOf m do
        problems := problems.push s!"a module of another conjecture is imported: {m}"
      if let some d := env.header.moduleData[i]? then
        if d.isModule then
          problems := problems.push s!"{m} uses the `module` system, which this checker does not accept"
        if m == stmtMod then
          for imp in d.imports do
            if (`conjectures).isPrefixOf imp.module then
              problems := problems.push s!"Statement.lean imports a local file: {imp.module}"
  -- everything Statement.lean declares
  let mut stmtCount := 0
  for (n, ci) in kenv.constants.map₁ do
    if (env.getModuleIdxFor? n).map (·.toNat) == some stmtIdx then
      stmtCount := stmtCount + 1
      match ci with
      | .axiomInfo _  => problems := problems.push s!"Statement.lean declares an axiom: {n}"
      | .opaqueInfo _ => problems := problems.push s!"Statement.lean declares an opaque (or partial) constant: {n}"
      | .quotInfo _   => problems := problems.push s!"Statement.lean declares a quotient primitive: {n}"
      | _ => pure ()
      -- Lean itself adds an unsafe twin `f._unsafe_rec` for a recursive `f`; it is never
      -- part of a statement (the kernel does not let a safe constant mention an unsafe one)
      let compilerTwin := match n with
        | .str p "_unsafe_rec" => (kenv.find? p).any (!·.isUnsafe)
        | _ => false
      if (ci.isUnsafe || ci.isPartial) && !compilerTwin then
        problems := problems.push s!"Statement.lean declares an unsafe or partial constant: {n}"
      let s := axiomsOf kenv n
      let bad := s.axioms.filter (!allowedAxioms.contains ·)
      unless bad.isEmpty do
        problems := problems.push s!"Statement.lean: {n} depends on {fmtNames bad}"
      unless s.missing.isEmpty do
        problems := problems.push s!"Statement.lean: {n} refers to unknown constants {fmtNames s.missing}"
  -- Claim
  match kenv.find? `Claim with
  | none => problems := problems.push "there is no constant `Claim`"
  | some ci =>
    unless modOf `Claim == some stmtMod do
      problems := problems.push s!"`Claim` is declared in {modOf `Claim}, not in this conjecture's Statement.lean"
    unless ci matches .defnInfo _ do
      problems := problems.push s!"`Claim` must be a plain `def`, but is a {kindOf ci}"
    unless ci.type == .sort .zero do
      problems := problems.push "`Claim` does not have type `Prop`"
    unless ci.levelParams.isEmpty do
      problems := problems.push "`Claim` has universe parameters"
  -- result
  let mut axs : Array Name := #[]
  match kenv.find? `result with
  | none => problems := problems.push "there is no constant `result`"
  | some ci =>
    unless modOf `result == some proofMod do
      problems := problems.push s!"`result` is declared in {modOf `result}, not in this conjecture's Proof.lean"
    unless ci matches .thmInfo _ do
      problems := problems.push s!"`result` must be a `theorem`, but is a {kindOf ci}"
    unless ci.type == .const `Claim [] do
      problems := problems.push "the statement of `result` is not literally `Claim`"
    unless ci.levelParams.isEmpty do
      problems := problems.push "`result` has universe parameters"
    let s := axiomsOf kenv `result
    axs := s.axioms
    let bad := s.axioms.filter (!allowedAxioms.contains ·)
    unless bad.isEmpty do
      problems := problems.push s!"`result` depends on axioms that are not allowed: {fmtNames bad}"
    unless s.missing.isEmpty do
      problems := problems.push s!"`result` refers to unknown constants {fmtNames s.missing}"
  IO.println s!"VERIFY statement-constants: {stmtCount}"
  IO.println s!"VERIFY axioms: {fmtNames axs}"
  for p in problems do IO.println s!"VERIFY problem: {p}"
  if problems.isEmpty then
    IO.println "VERIFY verdict: OK"
    return 0
  else
    IO.println "VERIFY verdict: FAIL"
    return 1

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [slug] =>
    try run slug
    catch e =>
      IO.println s!"VERIFY problem: {e}"
      IO.println "VERIFY verdict: FAIL"
      return 1
  | _ => IO.println "VERIFY verdict: FAIL (usage)"; return 2
EOF
chmod -R a+rX "$CHK"
fresh_rw
in_sandbox lean --run "$CHK/Verify.lean" "$SLUG" > "$WORK/log/verify.txt" 2>&1; VRC=$?
if [[ $VRC -ne 0 ]] || grep -q '^VERIFY problem' "$WORK/log/verify.txt" \
   || [[ "$(tail -1 "$WORK/log/verify.txt")" != "VERIFY verdict: OK" ]]; then
  echo "REJECTED: the compiled files do not hold up:"
  { grep '^VERIFY problem' "$WORK/log/verify.txt" || tail -20 "$WORK/log/verify.txt"; } | sed -e 's/^VERIFY problem: //' -e 's/^/    /' | cut -c1-300 | head -30
  exit 1
fi
AX5="$(grep -m1 '^VERIFY axioms:' "$WORK/log/verify.txt" | sed -e 's/^VERIFY axioms: *//' | tr ' ' '\n' | sort | tr '\n' ' ' | sed -E 's/^ +//; s/ +$//')"
for a in $AX5; do
  [[ " $ALLOWED_AXIOMS " == *" $a "* ]] || rejected "the proof depends on an axiom that is not allowed: $a"
done
[[ "$AX4" == "$AX5" ]] || rejected "the two axiom reports disagree: [#print axioms: $AX4] against [proof terms: $AX5]"

# --- 6. kernel replay in a fresh process
for b in $BUILT; do
  fresh_rw
  in_sandbox leanchecker "conjectures.$SLUG.$b" > "$WORK/log/replay.txt" 2>&1 \
    || { echo "REJECTED: the Lean kernel does not accept $b.lean when its declarations are replayed:"
         sed 's/^/    /' "$WORK/log/replay.txt" | cut -c1-300 | head -20; exit 1; }
done
REPLAY="slug files"
if [[ $FRESH -eq 1 ]]; then
  fresh_rw
  in_sandbox leanchecker --fresh "conjectures.$SLUG.Proof" > "$WORK/log/replay.txt" 2>&1 \
    || { echo "REJECTED: full replay from an empty environment failed:"
         sed 's/^/    /' "$WORK/log/replay.txt" | cut -c1-300 | head -20; exit 1; }
  REPLAY="everything, from an empty environment"
fi
[[ "$(sha256sum "$LIB/conjectures/$SLUG/Statement.olean" | cut -c1-64)" == "$STMT_SHA" ]] \
  || rejected "the compiled statement changed during checking"

echo "ACCEPTED  slug=${SLUG}  result : Claim  (Claim as defined in conjectures/${SLUG}/Statement.lean)"
echo "          axioms: ${AX5:-none}   kernel replay: ${REPLAY}   sandbox: ${SANDBOX}"
echo "          statement sha256: $(sha256sum "$DIR/Statement.lean" | cut -c1-16)   proof sha256: $(sha256sum "$DIR/Proof.lean" | cut -c1-16)   files:${BUILT}"
echo "          lean: ${PIN_TOOLCHAIN#*:} (${PIN_LEAN_GITHASH:0:12})   mathlib: ${PIN_MATHLIB_REV:0:12}   checker: $(sha256sum < "$SELF" | cut -c1-16)${REF:+ (same as $REF)}"
echo "          not checked here: that Claim says what the paper says. That is REVIEW.md."
if [[ $SANDBOX == off ]]; then
  echo "          WARNING: no sandbox on this machine, so the proof files were compiled with full access to it."
  echo "                   Re-run on a cloud session (Linux, root) before relying on this."
fi
exit 0
