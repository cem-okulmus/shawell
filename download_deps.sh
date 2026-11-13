#!/usr/bin/env bash
# Downloads DLV and Oxigraph binaries into bin/ for the current OS and architecture.
# With --clingo, also sets up a Python virtual environment in bin/clingo-venv with
# clingo installed (run as: bin/clingo-venv/bin/python -m clingo).
# Safe to re-run: existing binaries are left in place unless --force is passed.
#
# Usage: download_deps.sh [--force] [--clingo]
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BIN_DIR="${SCRIPT_DIR}/bin"
FORCE=0
WITH_CLINGO=0
for arg in "$@"; do
    case "${arg}" in
        --force)  FORCE=1 ;;
        --clingo) WITH_CLINGO=1 ;;
        -h|--help)
            echo "Usage: $(basename "$0") [--force] [--clingo]"
            echo "  --force   re-download / rebuild even if already present"
            echo "  --clingo  also install clingo into a virtual environment (needs Python >= 3.10)"
            exit 0
            ;;
        *)
            echo "ERROR: unknown option '${arg}' (expected --force and/or --clingo)" >&2
            exit 1
            ;;
    esac
done

mkdir -p "${BIN_DIR}"

# ------------------------------------------------------------------
# Helpers
# ------------------------------------------------------------------
download() {
    local url="$1" dest="$2" insecure="${3:-0}"
    if command -v curl &>/dev/null; then
        local flags="-fL --progress-bar"
        [[ "${insecure}" -eq 1 ]] && flags="${flags} -k"
        curl ${flags} -o "${dest}" "${url}"
    elif command -v wget &>/dev/null; then
        local flags="-q --show-progress"
        [[ "${insecure}" -eq 1 ]] && flags="${flags} --no-check-certificate"
        wget ${flags} -O "${dest}" "${url}"
    else
        echo "ERROR: neither curl nor wget found." >&2
        exit 1
    fi
}

# ------------------------------------------------------------------
# OS / arch detection
# ------------------------------------------------------------------
OS=""
ARCH=""

case "$(uname -s)" in
    Linux*)  OS="linux"  ;;
    Darwin*) OS="macos"  ;;
    *)
        echo "ERROR: unsupported OS '$(uname -s)'" >&2
        exit 1
        ;;
esac

case "$(uname -m)" in
    x86_64|amd64) ARCH="x86_64" ;;
    aarch64|arm64) ARCH="arm64"  ;;
    *)
        echo "ERROR: unsupported architecture '$(uname -m)'" >&2
        exit 1
        ;;
esac

echo "Platform: ${OS}/${ARCH}"

# ------------------------------------------------------------------
# DLV  (no GitHub API — pinned to latest known release 2.1.2)
# ------------------------------------------------------------------
DLV_VERSION="2.1.2"
DLV_BASE="https://www.mat.unical.it/DLV2/releases/${DLV_VERSION}"
DLV_DEST="${BIN_DIR}/dlv"
DLV_URL=""

case "${OS}-${ARCH}" in
    linux-x86_64)   DLV_URL="${DLV_BASE}/dlv-${DLV_VERSION}-linux-x86_64" ;;
    linux-arm64)
        echo "WARNING: DLV has no Linux ARM64 binary — skipping DLV download." >&2
        ;;
    macos-x86_64)   DLV_URL="${DLV_BASE}/dlv-${DLV_VERSION}-macos-x86_64" ;;
    macos-arm64)    DLV_URL="${DLV_BASE}/dlv-${DLV_VERSION}-arm64" ;;
esac

if [[ -n "${DLV_URL}" ]]; then
    if [[ -f "${DLV_DEST}" && "${FORCE}" -eq 0 ]]; then
        echo "DLV:      already present at ${DLV_DEST} (use --force to re-download)"
    else
        echo "DLV:      downloading ${DLV_VERSION}..."
        # mat.unical.it has an expired TLS certificate; insecure flag required
        download "${DLV_URL}" "${DLV_DEST}" 1
        chmod +x "${DLV_DEST}"
        echo "          -> ${DLV_DEST}"
    fi
fi

# ------------------------------------------------------------------
# clingo  (optional; pinned PyPI wheel in a virtual environment)
#
# There is no standalone clingo binary to download: the wheel provides a
# Python package, started as `<venv>/bin/python -m clingo`.
# Kept before the Oxigraph section, which exits when the GitHub API fails.
# ------------------------------------------------------------------
CLINGO_VENV="${BIN_DIR}/clingo-venv"
CLINGO_REQS="${SCRIPT_DIR}/clingo-requirements.txt"

# Prints the first interpreter that is Python >= 3.10 (required by the pinned cffi).
find_python() {
    local candidate
    for candidate in python3 python; do
        if command -v "${candidate}" &>/dev/null \
            && "${candidate}" -c 'import sys; sys.exit(sys.version_info < (3, 10))' &>/dev/null; then
            echo "${candidate}"
            return 0
        fi
    done
    return 1
}

# Called inside `if ! ...`, which disables `set -e` for the whole body:
# every step that may fail needs its own explicit `|| return 1`.
install_clingo() {
    local venv_python="${CLINGO_VENV}/bin/python"
    local python

    if [[ "${FORCE}" -eq 0 ]] && "${venv_python}" -m clingo --version &>/dev/null; then
        echo "clingo:   already present in ${CLINGO_VENV} (use --force to rebuild)"
        return 0
    fi

    if [[ ! -f "${CLINGO_REQS}" ]]; then
        echo "clingo:   ${CLINGO_REQS} not found" >&2
        return 1
    fi
    if ! python="$(find_python)"; then
        echo "clingo:   no Python >= 3.10 found (tried python3, python)" >&2
        return 1
    fi

    echo "clingo:   creating virtual environment with $("${python}" --version 2>&1)..."
    rm -rf "${CLINGO_VENV}"
    # On Debian/Ubuntu without python3-venv this fails and leaves a half-made directory.
    "${python}" -m venv "${CLINGO_VENV}" || { rm -rf "${CLINGO_VENV}"; return 1; }

    echo "clingo:   installing pinned wheels..."
    # --only-binary: fail on platforms without a wheel instead of attempting a source build.
    "${venv_python}" -m pip install --quiet --disable-pip-version-check \
        --only-binary=:all: --require-hashes -r "${CLINGO_REQS}" \
        || { rm -rf "${CLINGO_VENV}"; return 1; }

    "${venv_python}" -m clingo --version &>/dev/null || { rm -rf "${CLINGO_VENV}"; return 1; }
    echo "          -> ${venv_python} -m clingo"
}

CLINGO_FAILED=0
if [[ "${WITH_CLINGO}" -eq 1 ]] && ! install_clingo; then
    CLINGO_FAILED=1
    echo "WARNING: clingo was not installed; it is only needed for the stable-model semantics." >&2
    echo "         Install Python >= 3.10 with the venv module (Debian/Ubuntu: python3-venv)" >&2
    echo "         and re-run, or put a clingo executable on PATH." >&2
fi

# ------------------------------------------------------------------
# Oxigraph  (latest release via GitHub API)
# ------------------------------------------------------------------
echo "Oxigraph: querying GitHub for latest release..."
OXIGRAPH_TAG=""
if command -v curl &>/dev/null; then
    OXIGRAPH_TAG=$(curl -fsSL "https://api.github.com/repos/oxigraph/oxigraph/releases/latest" \
        | grep '"tag_name"' \
        | sed 's/.*"tag_name": *"\(.*\)".*/\1/')
elif command -v wget &>/dev/null; then
    OXIGRAPH_TAG=$(wget -qO- "https://api.github.com/repos/oxigraph/oxigraph/releases/latest" \
        | grep '"tag_name"' \
        | sed 's/.*"tag_name": *"\(.*\)".*/\1/')
fi

if [[ -z "${OXIGRAPH_TAG}" ]]; then
    echo "ERROR: could not determine latest Oxigraph version from GitHub." >&2
    exit 1
fi

OXIGRAPH_DEST="${BIN_DIR}/oxigraph"
OXIGRAPH_ASSET=""

case "${OS}-${ARCH}" in
    linux-x86_64)   OXIGRAPH_ASSET="oxigraph_${OXIGRAPH_TAG}_x86_64_linux_gnu" ;;
    linux-arm64)    OXIGRAPH_ASSET="oxigraph_${OXIGRAPH_TAG}_aarch64_linux_gnu" ;;
    macos-x86_64)   OXIGRAPH_ASSET="oxigraph_${OXIGRAPH_TAG}_x86_64_apple" ;;
    macos-arm64)    OXIGRAPH_ASSET="oxigraph_${OXIGRAPH_TAG}_aarch64_apple" ;;
    *)
        echo "ERROR: no Oxigraph binary for ${OS}/${ARCH}" >&2
        exit 1
        ;;
esac

OXIGRAPH_URL="https://github.com/oxigraph/oxigraph/releases/download/${OXIGRAPH_TAG}/${OXIGRAPH_ASSET}"

if [[ -f "${OXIGRAPH_DEST}" && "${FORCE}" -eq 0 ]]; then
    echo "Oxigraph: already present at ${OXIGRAPH_DEST} (use --force to re-download)"
else
    echo "Oxigraph: downloading ${OXIGRAPH_TAG}..."
    download "${OXIGRAPH_URL}" "${OXIGRAPH_DEST}"
    chmod +x "${OXIGRAPH_DEST}"
    echo "          -> ${OXIGRAPH_DEST}"
fi

echo ""
echo "Done. Dependencies ready in ${BIN_DIR}/"

if [[ "${OS}" == "macos" ]]; then
    echo ""
    echo "NOTE (macOS): if macOS blocks the binaries, run:"
    echo "  xattr -d com.apple.quarantine ${BIN_DIR}/dlv ${BIN_DIR}/oxigraph"
fi

# Binaries are in place, but report the clingo failure to the caller.
[[ "${CLINGO_FAILED}" -eq 0 ]] || exit 2
