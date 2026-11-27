#!/usr/bin/env bash
# Installs what is needed to check the proofs: elan, the pinned Lean toolchain, and
# Mathlib with its prebuilt cache. Safe to run repeatedly. Needs about 10 GB of disk
# and access to github.com, releases.lean-lang.org and cache.mathlib.org.
# The versions are pinned in lean-toolchain, lake-manifest.json and tools/check_lean.sh.
set -uo pipefail
export DEBIAN_FRONTEND=noninteractive
cd "$(dirname "$0")"
SUDO=""; [ "$(id -u)" -eq 0 ] || SUDO="sudo"
apt_get () { command -v apt-get >/dev/null && { $SUDO apt-get install -y -qq "$@" >/dev/null 2>&1 \
  || { $SUDO apt-get update -qq >/dev/null 2>&1; $SUDO apt-get install -y -qq "$@" >/dev/null 2>&1; }; }; }

lean_setup () {
  local ver elan_home tc url tmp os arch
  ver="$(sed -E 's/.*:v//' lean-toolchain)"                       # e.g. 4.36.0
  elan_home="${ELAN_HOME:-$HOME/.elan}"
  tc="$elan_home/toolchains/leanprover--lean4---v$ver"
  export PATH="$elan_home/bin:$PATH"

  # 1. elan (the Lean version manager)
  if [ ! -x "$elan_home/bin/elan" ]; then
    curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none >/dev/null 2>&1 || { echo "Lean: could not install elan (network?)"; return 1; }
  fi

  # 2. the pinned toolchain. elan fetches from release.lean-lang.org; if that host
  #    is blocked, unpack the same archive from releases.lean-lang.org by hand.
  if [ ! -x "$tc/bin/lean" ]; then
    echo "Lean: installing toolchain v$ver ..."
    if ! elan toolchain install "leanprover/lean4:v$ver" >/dev/null 2>&1 || [ ! -x "$tc/bin/lean" ]; then
      command -v zstd >/dev/null || apt_get zstd
      os="$(uname -s)"; arch="$(uname -m)"
      case "$os-$arch" in
        Linux-x86_64)  url="lean-$ver-linux.tar.zst" ;;
        Linux-aarch64) url="lean-$ver-linux_aarch64.tar.zst" ;;
        Darwin-arm64)  url="lean-$ver-darwin_aarch64.tar.zst" ;;
        Darwin-x86_64) url="lean-$ver-darwin.tar.zst" ;;
        *) echo "Lean: no prebuilt toolchain for $os-$arch"; return 1 ;;
      esac
      tmp="$(mktemp -d)"
      curl -sSfL -o "$tmp/lean.tar.zst" "https://releases.lean-lang.org/lean4/v$ver/$url" \
        || { echo "Lean: could not download the toolchain (is releases.lean-lang.org allowed?)"; rm -rf "$tmp"; return 1; }
      rm -rf "$tc"; mkdir -p "$tc"
      zstd -dc "$tmp/lean.tar.zst" | tar -xf - -C "$tc" --strip-components=1 \
        || { echo "Lean: could not unpack the toolchain"; rm -rf "$tmp" "$tc"; return 1; }
      rm -rf "$tmp"
    fi
  fi
  "$tc/bin/lean" --version | cut -c1-60

  # 3. Mathlib and its prebuilt cache (needs github.com and cache.mathlib.org).
  #    `lake exe cache get` clones the pinned packages on first use, then downloads
  #    compiled files instead of building Mathlib for hours.
  if [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then
    echo "Lean: fetching Mathlib and its prebuilt cache (a few minutes) ..."
    mkdir -p .lake
    if ! lake exe cache get > .lake/setup-cache.log 2>&1 \
       || [ ! -f .lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean ]; then
      echo "Lean: Mathlib cache download failed (is cache.mathlib.org allowed?). Last lines of .lake/setup-cache.log:"
      tr '\r' '\n' < .lake/setup-cache.log | tail -5
      return 1
    fi
  fi
  # the cache unpacks its files owner-only; the checker's sandbox reads them as `nobody`
  chmod -R a+rX .lake/packages 2>/dev/null
  echo "Lean: Mathlib ready. Put Lean on your PATH with:  export PATH=\"$elan_home/bin:\$PATH\""
}
lean_setup || { echo "Lean setup did not finish. See docs/verification.md"; exit 1; }
