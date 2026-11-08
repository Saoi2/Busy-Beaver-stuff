# Current proof project

**Skelet #10 nonhalting is now proved in Metamath over I-Delta-0.**
Machine: 1RB0RA_0LC1RA_1RE1LD_1LC0LD_---0RB, completing E0 by 1RZ.
The final label is skelet17-ladder-skelet10-no-blank-halting-history.
Read skelet17_research/SKELET10_NONHALTING.md for the definitions, case
combination, explicit induction formula, global contradiction and blank
start. Its final premises are just the original ordinary history, blank
initial tape and final halt condition, without supplied invariants.

All active mathematical proofs are in
skelet17_research/idelta0_machines.mm. It contains 1,031,962,351 bytes,
150,764 proved assertions, 270 named interfaces and the original 93
trusted declarations. All 266 preceding interfaces are preserved exactly.
The many private proof nodes are syntax, equality and natural-deduction
bookkeeping, not that many independent machine results. The preserved
introductory index inside the source describes an earlier checkpoint;
this README, STATUS.md and current reports give the latest state.

The cycler, translated cycler, counter, bouncer, four-state fractal and
Finned #3 also have complete individual blank-start nonhalting proofs.
Skelet #17 remains unfinished. No complete Busy Beaver classification,
independence result or proof-theoretic lower bound follows from this work.

The newest proof combines all three numerical boundary cases, proves a
bounded greatest-index lemma, excludes a boundary in a halting history,
and derives an initial boundary from the blank tape. It reuses four
existing induction constructions and adds one explicit bounded maximum
induction. Five constructions occur in its final dependency closure.

The official Metamath kernel verifies every proof in the standalone file.
Independent reconstructions check the new theorem formulas. Streaming
exact-interface and dependency audits preserve the trusted core and old
interfaces while avoiding whole-proof parsing in Python. Generator and
scoping tools are untrusted conveniences. See AUDIT_WORKFLOW.md and the
machine-readable reports in skelet17_research/.

Historical inputs remain for reproduction. All new formal results are
in the same canonical file; no second active proof library is needed.
REPRODUCING_SKELET10_ENDPOINT.md gives the append-stage bases and steps.
A fresh whole-project generation or whole-file simplification was not
rerun during this extension.
