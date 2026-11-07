# inkproof-consumer-metrics

A headless server-metrics consumer of Inkproof.Core and Inkproof.Scale: irregular scrapes, failed and missing scrapes, and gaps the consumer declares, aggregated into pyramids and mapped to pixel coordinates. It exists to exercise the libraries from their releases as an outside user would. [DESIGN.md](DESIGN.md) describes it.

`lake build` builds it and its proofs; `lake test` runs the tests.
