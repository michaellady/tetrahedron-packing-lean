# Converge review of the tetrahedron packing extension

Review base `02da1d6`. The snapshot covers 11 changed or added files, with
the shared checker and exact replay supplied as context.

**Changes requested for the general-purpose GSD export.** The Lean proof and
the shipped benchmark controls passed the review checks.

## Verified findings

1. **Major — large lattice translations change exported particle size.**
   [The exporter](benchmarks/write_gsd.py#L13) converts absolute vertices to
   float before deriving edge length and centered shapes. This can discard
   the small differences that encode a tetrahedron. For periods `2^26 I`,
   the four regular vertices at signed offsets of magnitude 3 from
   `(2^54 + 16, 2^54 + 16, 2^54 + 16)` have squared edge length 72.
   The output length of the box is 5,931,641.5 instead of approximately
   7,908,855.47, and the stored local shape has squared edge length 1.125
   instead of 1. Its image
   indices fit int32, so the current range checks accept it. Codex also
   reproduced a deformation after an exact lattice translation on a
   different input. Compute local vertices and centered or wrapped
   coordinates in exact arithmetic before the float conversion.
2. **Medium — a singular period matrix can become a thin 3D box.**
   [The rank test](benchmarks/write_gsd.py#L28) uses the floating-point
   determinant after normalizing the period matrix. For period columns
   `(2,3,5)`, `(7,11,13)`, and `(9,14,18)`, the third is exactly the sum of
   the first two. The exporter accepted the input and produced
   `Lz = 2.2204460e-16`. This is an input-validation failure on the export
   path. The exact certificate path requires full rank and rejects the input.
   Test the exact determinant before conversion. Apply
   a separate numerical check for whether a full-rank input is representable
   in the simulator.
3. **Low — optimized Python skips fixture validation.**
   [The replay command](benchmarks/check.py#L56) uses assertions for the
   coordinate correspondence, the positive separation test and the expected
   duplicate. In a temporary fixture copy, replacing `ceg.json` with the
   duplicate made plain Python fail. Running it under `python3 -O` exited
   successfully and printed density 4000/4671 after 40 checks. Use explicit
   error branches for checks that govern the command's exit status.
4. **Low — the incremental build can reuse an old JSON proof.**
   [The fixture theorem](TetrahedronPacking/PublishedInput.lean#L30) reads
   data with `include_str`. A Lean 4.19 scratch package replayed a build
   after I changed only its included file. Running Lean directly failed on
   the current bytes. The [benchmark instructions](benchmarks/README.md#check-the-exact-geometry-in-lean)
   already include a direct Lean invocation as a workaround. A build
   dependency for the fixtures would also make the default build catch the
   change.
5. **Low — the exporter accepts geometrically irregular input.**
   [The edge check](benchmarks/write_gsd.py#L19) uses a relative tolerance
   of `1e-10`. Moving one vertex of the reference tetrahedron by
   `10^-12` along one axis produced three different exact squared edge
   lengths and still exported. The exact regularity check used by the
   certificate generator can also validate input to the exporter.
6. **Low — the approximant replay's source can drift.**
   [The command](benchmarks/README.md#scientific-use-and-a-second-published-structure)
   downloads the latest arXiv PDF and extracts fixed page numbers. A later
   version could change pagination or table formatting. The current
   download matches [arXiv v1](https://arxiv.org/abs/1012.5138v1), and both
   downloaded copies have SHA-256
   `56be93178c3d9944f55e0e664b46e8750b0500545bc88826d9f67c96a286f433`.
   Pin the v1 URL and check the expected count and density on replay.

## Independent rechecks

- `lake build` passed. Direct checking of `PublishedInput.lean` and
  `CellScreening.lean` passed, with only `propext`, `Classical.choice` and
  `Quot.sound` in the reported axiom sets.
- The exact Python replay returned 308 separations for the published cell
  at density 4000/4671. It reported the duplicate at pair 0 and 1, shift
  `(0,-3,0)`.
- HOOMD-blue 7.2.2 reported zero overlaps for the expanded positive fixture
  and one overlap for the expanded duplicate control.
- The rational approximant replay returned 3,558 separations and the
  expected density of 0.847865909437. This check used the published
  82-particle table.

The Lean `CellInput` type permits additional values in its internal
representation, including zero as a unit denominator. The JSON reader
filters those values and the generated certificate checks positivity.
The density theorem operates in integer numerator units, so this is a
representation distinction. The generated certificate and HPMC controls
were exercised manually. The default build currently exercises only the
Lean library.

## Findings ruled out

Composer reported that the default build omits the two new proof modules
because the umbrella module does not import them. The
[Lake configuration](lakefile.toml#L9) includes all submodules through its
library glob. Running the default `lake build` prints both
`publishedInput_spatial_density` and `regular_record_screen`. The separate
incremental JSON issue still applies because fixture bytes are outside
the module dependency graph.

## CONVERGE LOG

Reviewed with Converge PR #12 at `4ab0168`.

| Round | Author | Verdict | Issues raised | Issues conceded |
|-------|--------|---------|---------------|-----------------|
| 1 | Codex | Prose captured | 2 exporter findings | — |
| 1 | Muse | Prose captured | 4 findings | — |
| 2 | Codex | Some fail | Translation damage | — |
| 2 | Muse | Some fail | Translation damage, singular input | — |
| 2 | Composer 2.5 | Some fail | Optimized Python validation | — |
| 3 | Codex | Some fail | Translation damage, singular input | — |
| 3 | Composer 2.5 | Some fail | Exporter correctness, fixture replay and reproducibility | — |

- Round 1, `c46c22c363e3b85d73e6c45eef3958dd`. Codex and Muse returned
  prose. The packet omitted the JSON response schema, so Converge could not
  merge those findings. Antigravity using native `gemini-4-neon-xhigh`,
  Claude, Composer 2.5 and Grok Build timed out.
- Round 2, `990052c61e1e82d3de17f015fa8b394a`. All three reviewers
  returned valid JSON. The merge flagged all three candidates. I reproduced
  each case before assigning severity.
- Round 3, `03492b24faee2a3f8a1fe50f886c1670`. Codex and Composer 2.5
  reviewed the full change with the corrected response schema. Converge
  merged both verdicts as `some_fail`. I verified the findings against the
  worktree and reproduced the two exporter failures.

## Antigravity follow-up

Converge PR #12 invoked native Antigravity 1.5.15 in plan mode with
`--sandbox`. The session's PATH selected the native binary and the
model was supplied through `CONVERGE_AGY_MODEL`.

- Gemini 4 Argon High passed the transport probe
  (`761d142c45c2fc62903d23536d3931ca`).
- The same model completed a focused exporter review
  (`6757c6c26de9516536f6984360872519`). Its raw verdict confirmed both
  the large-translation error and the singular-matrix acceptance.
  Converge's merge grouped them because they share a 12-byte text
  fragment. The raw verdict retains both findings.
- Gemini 4 Neon XHigh completed the Lean and fixture packet
  (`1bf989939e4dd83be59d4c615608316d`) in about 7 minutes 45 seconds.
  Its raw and merged verdicts both report no findings.
- Gemini 4 Argon High independently reviewed the same packet and reported
  no findings (`94e0d7bc1980f79d14238092038946a4`).
- The broader Python packet on Neon XHigh timed out after 15 minutes
  (`52765f5e18e8d31345dc0c0c761c8a02`). The focused Argon High exporter
  verdict above completed successfully.

## Exporter fixes

The exporter now checks congruence and period rank exactly. It computes the
centroids, local offsets, lattice images and wrapped positions with
rational arithmetic before projecting into the simulator frame. This
addresses findings 1, 2 and 5.

The [regression tests](benchmarks/test_write_gsd.py) reproduced the
large-translation and singular-matrix inputs. The translated geometry now
matches the original up to the expected image indices, and the singular
input is rejected. HOOMD-blue 7.2.2 again reported zero overlaps for the
expanded positive fixture and one for the expanded duplicate control.

## Reproducibility fixes

The fixture replay now uses explicit failure paths. It passed with
`python3 -O` and rejected each fixture substitution under the same flag.
Lake now tracks both JSON files as byte-level inputs. In warm scratch
builds, adding one space to either fixture caused Lake to rerun
`PublishedInput.lean` and reject the corresponding equality theorem.

The approximant replay pins arXiv v1 and verifies the PDF checksum before
extracting the table. The unexpanded replay checks the exact reference
density and all 3,558 separations. The pinned source passed, a modified PDF
failed the checksum, and a one-digit change to the extracted box length
failed the density check. These changes address findings 3, 4 and 6.
