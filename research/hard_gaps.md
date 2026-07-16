# RH Hard Gaps

Date: 2026-07-17

The canonical DAG is `research/hard_gap_dag.md`. This compatibility file records the same fixed
hard-gap identifiers used by the v2 loop protocol.

| gap_id | canonical node | current status |
| --- | --- | --- |
| G1 | M1/D | complete |
| G2 | M1 | complete |
| G3 | M2 | open |
| G4 | B1 | complete; fixed source frontier F0-F5 publicly Lean-checked |
| G8 | H6-E | open; the exact local pair law and adjacent bound `(gap^2)'<=8` compile, but `OBS-H6-ADJACENT-GAP-EIGHT-01` proves this generic bound is sharp and supplies no height-uniform backward interval; theta-specific continuation, repeated-zero control, collision exclusion, and the time-zero endpoint remain unproved |

Future attempt logs must copy `hard_gap_before`, `hard_gap_after`, and `hard_gap_delta` from
`research/hard_gap_dag.md`, not from self-created local targets.
