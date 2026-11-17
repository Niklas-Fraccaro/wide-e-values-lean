#!/bin/sh
set -eu

cd "$(dirname "$0")"
toolchain=$(lean --print-prefix)
build_toolchain=$(mktemp -d "${TMPDIR:-/tmp}/wide-e-lean.XXXXXX")
trap 'rm -rf "$build_toolchain"' EXIT

# Lake normally enables asynchronous elaboration. Use the sequential settings
# of the pinned strict source replay without changing the installed toolchain.
mkdir "$build_toolchain/bin"
for entry in "$toolchain"/*; do
    name=${entry##*/}
    if [ "$name" != "bin" ]; then
        ln -s "$entry" "$build_toolchain/$name"
    fi
done
for entry in "$toolchain"/bin/*; do
    name=${entry##*/}
    if [ "$name" != "lean" ]; then
        ln -s "$entry" "$build_toolchain/bin/$name"
    fi
done

export WIDEE_LEAN_BIN="$toolchain/bin/lean"
cat > "$build_toolchain/bin/lean" <<'EOF'
#!/bin/sh
exec "$WIDEE_LEAN_BIN" -j1 -DElab.async=false "$@"
EOF
chmod +x "$build_toolchain/bin/lean"

if [ "$#" -eq 0 ]; then
    set -- build
fi
LAKE_OVERRIDE_LEAN=true LEAN_SYSROOT="$build_toolchain" "$toolchain/bin/lake" "$@"
