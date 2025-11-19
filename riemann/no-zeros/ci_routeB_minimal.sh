#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

TARGETS=(
  rh.academic_framework.DiagonalFredholm.Determinant
  rh.RS.Det2Outer
  rh.RS.RouteB_Final
  rh.RS.RouteBPinnedRemovable
  rh.Proof.Main
  rh.Cert.KxiWhitney_RvM
  rh.analytic_number_theory.VinogradovKorobov
)

echo "[ci_routeB] Building all targets (including VK integration)..."

for target in "${TARGETS[@]}"; do
  echo "[ci_routeB] building $target"
  lake build "$target"
  echo "[ci_routeB] $target ✅"
  echo
done
