package main

import (
	"fmt"
	"net"
	"net/http"
	"os"
	"os/exec"
	"runtime"
	"time"
)

// StartOxigraph launches an Oxigraph SPARQL server subprocess on a free local port,
// waits until it is ready, and returns a connected SparqlEndpoint along with a cleanup
// function that stops the process and removes its temp storage directory.
//
// The oxigraph binary is resolved by checking PATH first, then bin/oxigraph.
func StartOxigraph(debug bool) (ep *SparqlEndpoint, cleanup func(), err error) {
	binary, err := findOxigraph()
	if err != nil {
		return nil, nil, err
	}

	port, err := freePort()
	if err != nil {
		return nil, nil, fmt.Errorf("finding free port: %w", err)
	}

	tmpDir, err := os.MkdirTemp("", "shawell-oxigraph-*")
	if err != nil {
		return nil, nil, fmt.Errorf("creating temp dir: %w", err)
	}

	addr := fmt.Sprintf("127.0.0.1:%d", port)
	cmd := exec.Command(binary, "serve", "--location", tmpDir, "--bind", addr)
	if debug {
		cmd.Stdout = os.Stderr
		cmd.Stderr = os.Stderr
	}

	if err = cmd.Start(); err != nil {
		os.RemoveAll(tmpDir)
		return nil, nil, fmt.Errorf("starting oxigraph: %w", err)
	}

	cleanup = func() {
		cmd.Process.Kill() //nolint:errcheck
		cmd.Wait()         //nolint:errcheck
		os.RemoveAll(tmpDir)
	}

	baseURL := fmt.Sprintf("http://%s", addr)
	if err = waitForOxigraph(baseURL); err != nil {
		cleanup()
		return nil, nil, err
	}

	ep = GetSparqlEndpoint(
		baseURL+"/query",
		baseURL+"/update",
		"", "",
		debug,
		true,
		"",
	)
	return ep, cleanup, nil
}

func findOxigraph() (string, error) {
	if path, err := exec.LookPath("oxigraph"); err == nil {
		return path, nil
	}
	local := "bin/oxigraph"
	if runtime.GOOS == "windows" {
		local = "bin/oxigraph.exe"
	}
	if _, err := os.Stat(local); err == nil {
		return local, nil
	}
	return "", fmt.Errorf("oxigraph binary not found in PATH or %s; "+
		"needs to be downloaded from https://github.com/oxigraph/oxigraph/releases,"+
		" the included download_deps.sh can set it up easily", local)
}

func freePort() (int, error) {
	l, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		return 0, err
	}
	defer l.Close()
	return l.Addr().(*net.TCPAddr).Port, nil
}

// waitForOxigraph polls the query endpoint until it responds successfully or 15 seconds elapse.
func waitForOxigraph(baseURL string) error {
	deadline := time.Now().Add(15 * time.Second)
	client := &http.Client{Timeout: 500 * time.Millisecond}
	probe := baseURL + "/query?query=ASK+%7B%7D"

	for time.Now().Before(deadline) {
		resp, err := client.Get(probe)
		if err == nil {
			resp.Body.Close()
			if resp.StatusCode < 500 {
				return nil
			}
		}
		time.Sleep(100 * time.Millisecond)
	}
	return fmt.Errorf("oxigraph did not respond within 15 seconds")
}
