# inkproof-consumer-metrics design

A headless application that charts server metrics with Inkproof.Core and Inkproof.Scale, used only through their released public API, to check that their specifications fit a real domain and leak no domain assumptions (VAL-3, VAL-2 in `REQUIREMENTS.md` in `inkproof-coordination`). Everything about metrics lives here; where the libraries make something awkward, the finding is a request on the library, never a workaround.

## Packages and modules

- The package requires `inkproof-core` and `inkproof-scale` at release tags only (`scripts/check-pins.sh`), imports no `Internal` module, and publishes no API, so it has no `API.lock`.
- `Metrics.Scrapes` holds the domain: timestamps and readings, and the gap policy. `Metrics.Chart` aggregates and maps to pixels. `Metrics.Proofs` proves what each of them computes by applying the libraries' theorems.
- Tests live in the same package: `MetricsTest`, run by `lake test` through `testDriver`.

## Domain

- Timestamps are seconds since the epoch and readings are numbers, both `Rat`: exposition formats write decimals, which `Rat` holds exactly, and Scale's theorems cover ordered fields, not `Float`.
- A scrape that ran but returned nothing is a `none` reading (CORE-2); a scrape that never ran is an absent point. Aggregates skip `none`, so a failed scrape never shows as a value.
- `GapPolicy` decides where a line must break: adjacent scrapes more than `staleAfter` apart, or a target restart after one scrape and no later than the next. It reaches Core as the predicate of `Segmented.splitWhere`; Core never infers a gap (CORE-3).

## Charting

- `chart` builds a `SegmentedPyramid` of first/maximum/minimum/last per segment, enough to draw one pixel column of a line.
- A `View` is a time window over pixel columns and a reading range over pixel rows. Its x-scale maps the window onto `[0, columns]`, and column `c` holds the times the x-scale maps into `[c, c + 1)`; its y-scale maps readings onto `[height, 0]`, since screen y grows downwards.
- `render` gives, for each column, one optional `Extent` per segment: the screen y of the first, highest, lowest and last reading there, or `none` where the segment has no reading in the column. Drawing is out of scope.

## Proofs and tests

- `Metrics.Proofs` applies Core's `getElem_query`, `fold_prod`, the aggregates' `fold_get` theorems and `mem_breaks_splitWhere`, and Scale's endpoint, inverse and monotonicity theorems, to this consumer's types, discharging every hypothesis. A hypothesis it cannot reasonably discharge is a request on the library.
- The tests generate irregular scrapes with skipped and failed runs, stalls, restarts and repeated timestamps, and compare every column with a naive computation that splits segments and assigns columns itself. They check that mapped readings keep their order and land on screen, and cover empty and single-sample series, all-failed runs and gaps at either end.
