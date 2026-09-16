# Blueprint graph configuration

`hgraph.yaml` limits graph synchronization to this project's Lean sources. Do not
index the project root: it contains `.lake`, including mathlib and other external
dependencies. External libraries remain available through `horizon search`.

Horizon reads `ArakelovGeometry/hgraph/config.yaml`, which links to this versioned
configuration. The generated `hgraph/` directory is excluded from Horizon's ledger.
If that directory is recreated, restore the link from the workspace root:

```sh
mkdir -p ArakelovGeometry/hgraph
ln -s ../blueprint/hgraph.yaml ArakelovGeometry/hgraph/config.yaml
horizon blueprint --json
```

Run `horizon blueprint --json` after blueprint updates to refresh the dashboard
cache before serving it. The configured graph inputs must never include `.lake`.
