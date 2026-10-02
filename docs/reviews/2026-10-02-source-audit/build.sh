#!/usr/bin/env bash
set -euo pipefail
audit_dir="$(cd -- "$(dirname -- "$0")" && pwd)"
audit_tmp_root="${ARCHON_HORIZON_TMP:-${TMPDIR:-/tmp}}"
mkdir -p "$audit_tmp_root"
audit_build_dir="$(mktemp -d "$audit_tmp_root/ageo-source-audit-tex.XXXXXX")"
cd "$audit_dir"
for audit_pass in 1 2 3; do
  xelatex -interaction=nonstopmode -halt-on-error -file-line-error \
    -output-directory="$audit_build_dir" report.tex >"$audit_build_dir/pass-$audit_pass.stdout"
done
if rg -n 'Missing character:|LaTeX Warning: (Reference|There were undefined references)|Overfull \\[hv]box' "$audit_build_dir/report.log"; then
  echo "Report validation failed; inspect $audit_build_dir/report.log" >&2
  exit 1
fi
cp "$audit_build_dir/report.pdf" "$audit_dir/report.pdf"
echo "PDF: $audit_dir/report.pdf"
echo "Build log (scratch): $audit_build_dir/report.log"
