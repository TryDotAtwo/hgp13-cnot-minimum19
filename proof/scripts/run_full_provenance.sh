#!/bin/sh
set -eu
cd /work/outputs/hgp13-arxiv
out=evidence/full_provenance_2026-09-27
mkdir -p "$out"
printf 'source_sha256 ' > "$out/provenance.txt"
sha256sum hgp13_verify.cpp >> "$out/provenance.txt"
printf 'compiler ' >> "$out/provenance.txt"
g++ --version | head -n 1 >> "$out/provenance.txt"
printf 'compile_command g++ -O3 -std=c++17 -pthread hgp13_verify.cpp -o %s/verifier.bin\n' "$out" >> "$out/provenance.txt"
g++ -O3 -std=c++17 -pthread hgp13_verify.cpp -o "$out/verifier.bin"
printf 'binary_sha256 ' >> "$out/provenance.txt"
sha256sum "$out/verifier.bin" >> "$out/provenance.txt"
printf 'start_utc ' >> "$out/provenance.txt"
date -u '+%Y-%m-%dT%H:%M:%SZ' >> "$out/provenance.txt"
set +e
"$out/verifier.bin" 2 > "$out/run.txt" 2> "$out/stderr.txt"
rc=$?
set -e
printf 'exit_code %s\n' "$rc" >> "$out/provenance.txt"
printf 'end_utc ' >> "$out/provenance.txt"
date -u '+%Y-%m-%dT%H:%M:%SZ' >> "$out/provenance.txt"
printf 'run_sha256 ' >> "$out/provenance.txt"
sha256sum "$out/run.txt" >> "$out/provenance.txt"
test "$rc" -eq 0
