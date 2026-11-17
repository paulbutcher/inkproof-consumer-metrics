# inkproof-consumer-metrics

A headless server-metrics consumer of Inkproof.Core and Inkproof.Scale: irregular scrapes, failed and missing scrapes, and gaps the consumer declares, aggregated into pyramids and mapped to pixel coordinates. It exists to exercise the libraries from their releases as an outside user would. [DESIGN.md](DESIGN.md) describes it.

## What it does

- Decide whether two scrapes are too far apart, or straddle a restart, to be joined: `Metrics.GapPolicy`, `GapPolicy.isGap`.
- Split a series of scrapes (with failed scrapes as missing readings) into gap-separated segments: `GapPolicy.segment`, `Metrics.Scrapes`.
- Build a chart of first, high, low and last readings per segment that answers range queries over time: `Metrics.chart`, `Metrics.summarise`, `Metrics.inWindow`.
- Map a time and reading window onto a pixel grid: `Metrics.View`, with `View.xScale`, `View.yScale` and `View.columnStart`.
- Render a chart into pixel columns, one extent (first, top, bottom, last in pixel coordinates, or none for an empty window) per segment: `View.render`, `View.column`, `View.extent`, `Metrics.Extent`.

The theorems in `API.lock` state what each of these computes.

## Using it

Require it at the current release, v0.1.1:

```lean
require «inkproof-consumer-metrics» from git "https://github.com/paulbutcher/inkproof-consumer-metrics" @ "v0.1.1"
```

`lake build` builds it and its proofs; `lake test` runs the tests.
