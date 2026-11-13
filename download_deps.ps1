# download_deps.ps1
# Downloads DLV and Oxigraph binaries into bin/ for Windows.
# With -Clingo, also sets up a Python virtual environment in bin\clingo-venv with
# clingo installed (run as: bin\clingo-venv\Scripts\python.exe -m clingo).
# Safe to re-run: existing binaries are left in place unless -Force is passed.
#
# Usage: download_deps.ps1 [-Force] [-Clingo]

param(
    [switch]$Force,
    [switch]$Clingo
)

$ErrorActionPreference = "Stop"

$ScriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$BinDir    = Join-Path $ScriptDir "bin"

if (-not (Test-Path $BinDir)) {
    New-Item -ItemType Directory -Path $BinDir | Out-Null
}

# ------------------------------------------------------------------
# Download helper
#
# Prefers curl.exe (ships with Windows 10 1803+, handles TLS reliably).
# Falls back to System.Net.WebClient for older systems.
# SkipCertCheck bypasses certificate validation (needed for mat.unical.it).
# ------------------------------------------------------------------
function Get-File {
    param(
        [string]$Url,
        [string]$Dest,
        [switch]$SkipCertCheck
    )

    if (Get-Command curl.exe -ErrorAction SilentlyContinue) {
        $curlArgs = @("-fL", "--progress-bar", "-o", $Dest, $Url)
        if ($SkipCertCheck) { $curlArgs = @("-k") + $curlArgs }
        & curl.exe @curlArgs
        if ($LASTEXITCODE -ne 0) { throw "curl.exe failed with exit code $LASTEXITCODE" }
        return
    }

    # Fallback: WebClient with TLS 1.2 forced (Windows PowerShell 5 defaults to TLS 1.0/1.1)
    $origProtocol = [Net.ServicePointManager]::SecurityProtocol
    $origCallback = [Net.ServicePointManager]::ServerCertificateValidationCallback
    [Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12
    if ($SkipCertCheck) {
        [Net.ServicePointManager]::ServerCertificateValidationCallback = { $true }
    }
    try {
        $wc = New-Object System.Net.WebClient
        $wc.DownloadFile($Url, $Dest)
    } finally {
        [Net.ServicePointManager]::SecurityProtocol = $origProtocol
        [Net.ServicePointManager]::ServerCertificateValidationCallback = $origCallback
    }
}

# ------------------------------------------------------------------
# Architecture detection
# ------------------------------------------------------------------
$Arch = switch ($env:PROCESSOR_ARCHITECTURE) {
    "AMD64"  { "x86_64" }
    "ARM64"  { "arm64"  }
    default  { throw "Unsupported architecture: $($env:PROCESSOR_ARCHITECTURE)" }
}

Write-Host "Platform: windows/$Arch"

# ------------------------------------------------------------------
# DLV  (pinned to latest known release 2.1.2)
# ------------------------------------------------------------------
$DlvVersion = "2.1.2"
$DlvBase    = "https://www.mat.unical.it/DLV2/releases/$DlvVersion"
$DlvDest    = Join-Path $BinDir "dlv.exe"

if ($Arch -eq "x86_64") {
    $DlvUrl = "$DlvBase/dlv-$DlvVersion-win64.exe"

    if ((Test-Path $DlvDest) -and -not $Force) {
        Write-Host "DLV:      already present at $DlvDest (use -Force to re-download)"
    } else {
        Write-Host "DLV:      downloading $DlvVersion..."
        Get-File -Url $DlvUrl -Dest $DlvDest -SkipCertCheck
        Write-Host "          -> $DlvDest"
    }
} else {
    Write-Warning "DLV has no Windows ARM64 binary - skipping DLV download."
}

# ------------------------------------------------------------------
# clingo  (optional; pinned PyPI wheel in a virtual environment)
#
# There is no standalone clingo binary to download: the wheel provides a
# Python package, started as `<venv>\Scripts\python.exe -m clingo`.
# Kept before the Oxigraph section, which throws when the GitHub API fails.
# ------------------------------------------------------------------
$ClingoVenv = Join-Path $BinDir "clingo-venv"
$ClingoReqs = Join-Path $ScriptDir "clingo-requirements.txt"

# Returns the command (as an array) of the first interpreter that is
# Python >= 3.10 (required by the pinned cffi), or $null.
# Running it also filters out the Microsoft Store stub named python.exe.
function Find-Python {
    $ErrorActionPreference = "Continue"   # native stderr must not throw
    $candidates = @(
        @("py", "-3"),
        @("python"),
        @("python3")
    )
    foreach ($candidate in $candidates) {
        $exe  = $candidate[0]
        $rest = @($candidate | Select-Object -Skip 1)
        if (-not (Get-Command $exe -ErrorAction SilentlyContinue)) { continue }
        try {
            & $exe @rest -c "import sys; sys.exit(sys.version_info < (3, 10))" *> $null
        } catch {
            continue
        }
        if ($LASTEXITCODE -eq 0) { return ,$candidate }
    }
    return $null
}

# Returns $true on success. Native output is piped to Out-Host so that it
# does not become part of the return value.
function Install-Clingo {
    $ErrorActionPreference = "Continue"   # native stderr must not throw; exit codes are checked
    $venvPython = Join-Path $ClingoVenv "Scripts\python.exe"

    if (-not $Force -and (Test-Path $venvPython)) {
        & $venvPython -m clingo --version *> $null
        if ($LASTEXITCODE -eq 0) {
            Write-Host "clingo:   already present in $ClingoVenv (use -Force to rebuild)"
            return $true
        }
    }

    if (-not (Test-Path $ClingoReqs)) {
        Write-Host "clingo:   $ClingoReqs not found"
        return $false
    }
    $python = Find-Python
    if (-not $python) {
        Write-Host "clingo:   no Python >= 3.10 found (tried py -3, python, python3)"
        return $false
    }
    $pyExe  = $python[0]
    $pyArgs = @($python | Select-Object -Skip 1)

    $version = (& $pyExe @pyArgs --version 2>&1 | Out-String).Trim()
    Write-Host "clingo:   creating virtual environment with $version..."
    if (Test-Path $ClingoVenv) { Remove-Item -Recurse -Force $ClingoVenv }
    & $pyExe @pyArgs -m venv $ClingoVenv 2>&1 | Out-Host
    if ($LASTEXITCODE -ne 0 -or -not (Test-Path $venvPython)) {
        if (Test-Path $ClingoVenv) { Remove-Item -Recurse -Force $ClingoVenv }
        return $false
    }

    Write-Host "clingo:   installing pinned wheels..."
    # --only-binary: fail on platforms without a wheel (e.g. Windows ARM64)
    # instead of attempting a source build.
    & $venvPython -m pip install --quiet --disable-pip-version-check `
        --only-binary=:all: --require-hashes -r $ClingoReqs 2>&1 | Out-Host
    if ($LASTEXITCODE -ne 0) {
        Remove-Item -Recurse -Force $ClingoVenv
        return $false
    }

    & $venvPython -m clingo --version *> $null
    if ($LASTEXITCODE -ne 0) {
        Remove-Item -Recurse -Force $ClingoVenv
        return $false
    }
    Write-Host "          -> $venvPython -m clingo"
    return $true
}

$ClingoFailed = $false
if ($Clingo -and -not (Install-Clingo)) {
    $ClingoFailed = $true
    Write-Warning "clingo was not installed; it is only needed for the stable-model semantics."
    Write-Warning "Install Python >= 3.10 (https://www.python.org/downloads/) and re-run, or put a clingo executable on PATH."
}

# ------------------------------------------------------------------
# Oxigraph  (latest release via GitHub API)
# ------------------------------------------------------------------
Write-Host "Oxigraph: querying GitHub for latest release..."
$OxigraphRelease = Invoke-RestMethod -Uri "https://api.github.com/repos/oxigraph/oxigraph/releases/latest"
$OxigraphTag     = $OxigraphRelease.tag_name

if (-not $OxigraphTag) {
    throw "Could not determine latest Oxigraph version from GitHub."
}

$OxigraphDest  = Join-Path $BinDir "oxigraph.exe"
$OxigraphAsset = switch ($Arch) {
    "x86_64" { "oxigraph_${OxigraphTag}_x86_64_windows_msvc.exe" }
    "arm64"  { "oxigraph_${OxigraphTag}_aarch64_windows_msvc.exe" }
}
$OxigraphUrl = "https://github.com/oxigraph/oxigraph/releases/download/$OxigraphTag/$OxigraphAsset"

if ((Test-Path $OxigraphDest) -and -not $Force) {
    Write-Host "Oxigraph: already present at $OxigraphDest (use -Force to re-download)"
} else {
    Write-Host "Oxigraph: downloading $OxigraphTag..."
    Get-File -Url $OxigraphUrl -Dest $OxigraphDest
    Write-Host "          -> $OxigraphDest"
}

Write-Host ""
Write-Host "Done. Dependencies ready in $BinDir"

# Binaries are in place, but report the clingo failure to the caller.
if ($ClingoFailed) { exit 2 }
