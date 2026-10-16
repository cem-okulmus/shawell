# download_deps.ps1
# Downloads DLV and Oxigraph binaries into bin/ for Windows.
# Safe to re-run: existing binaries are left in place unless -Force is passed.

param(
    [switch]$Force
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
