#!/usr/bin/env bash
# Run leanprover/comparator against this repository's proof of Dickson's classification,
# mirroring the lean-eval pipeline (pattern: rkirov/jacobian-claude): same toolchain, the
# comparator/ workspace's Challenge.lean (the independently-auditable statement),
# Solution.lean (the bridge), and the real comparator (statement match + permitted-axiom
# check + kernel replay via lean4export).
#
# Trust required: the Lean kernel, Mathlib, comparator/Challenge.lean (READ IT), and
# comparator itself. The proofs in ClassificationOfSubgroups are NOT trusted — comparator
# re-checks them independently via lean4export + the kernel, in a landrun sandbox.
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WS="$HERE/comparator"
TOOLCHAIN_TAG=$(sed -e 's/^leanprover\/lean4://' "$WS/lean-toolchain" | tr -d '[:space:]')
WORK="${COMPARATOR_WORK:-$HOME/.cache/dickson-comparator}"
mkdir -p "$WORK"

# comparator + lean4export pinned to the SAME toolchain that built the library, so
# lean4export can read its `.olean`s (the export format is toolchain-locked).
if [ ! -d "$WORK/comparator" ]; then
  git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
    https://github.com/leanprover/comparator "$WORK/comparator"
fi
if [ ! -d "$WORK/lean4export" ]; then
  git clone --branch "$TOOLCHAIN_TAG" --depth 1 \
    https://github.com/leanprover/lean4export "$WORK/lean4export"
fi
(cd "$WORK/comparator" && lake build)
(cd "$WORK/lean4export" && lake build)

# landrun sandbox binary, wrapped to grant the dynamic loader the read+exec paths its
# -ldd resolution can miss.
if [ ! -x "$WORK/landrun-bin" ]; then
  curl -sL -o "$WORK/landrun-bin" \
    https://github.com/Zouuup/landrun/releases/download/v0.1.14/landrun-linux-amd64
  chmod +x "$WORK/landrun-bin"
fi
EXTRA=""
for d in /lib64 /lib /usr/lib /nix/store; do
  [ -e "$d" ] && EXTRA="$EXTRA --rox $d"
done
printf '#!/usr/bin/env bash\nexec "%s/landrun-bin"%s "$@"\n' "$WORK" "$EXTRA" \
  > "$WORK/landrun"
chmod +x "$WORK/landrun"
export COMPARATOR_LANDRUN="$WORK/landrun"
export PATH="$WORK/lean4export/.lake/build/bin:$WORK:$PATH"

# Build the workspace (Challenge spec, Solution bridge, Submission → library) and run.
cd "$WS"
lake build Challenge Solution Submission
exec lake env "$WORK/comparator/.lake/build/bin/comparator" config.json
