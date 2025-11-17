#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

TARGETS=(
  rh.academic_framework.DiagonalFredholm.Determinant
  rh.RS.Det2Outer
  rh.RS.RouteB_Final
  rh.RS.RouteBPinnedRemovable
  rh.Proof.Main
)

echo "[ci_routeB] VK_SANDBOX=${VK_SANDBOX:-0}"

if [[ "${VK_SANDBOX:-0}" == "1" ]]; then
  TARGETS+=(rh.analytic_number_theory.VinogradovKorobov)
fi

for target in "${TARGETS[@]}"; do
  echo "[ci_routeB] building $target"
  lake build "$target"
  echo "[ci_routeB] $target ✅"
  echo
done
