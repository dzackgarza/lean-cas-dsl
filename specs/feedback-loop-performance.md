# Feedback-loop performance: how to find and fix the cost that matters

This document is the procedure for performance work on the development loop. It applies when a
loop run of the active task exceeds its bound. It does not apply to the final runtime performance
work, which comes after all functionality (constitution C21). The rules "Timing
history" and "Timing triage" of constitution C24 are the authority; this document makes them
operational.

## The bound, the expected time of a check, and the margin

- The bound of the focused loop is 300 s: the rebuild of the edited owner and its dependents, and
  the run of the unchanged public consumer (`AGENTS.md`, `CONTRIBUTING.md` "Feedback loops"; the
  owner's rule that a tier-1 loop over five minutes is a defect).
- Every task check has an expected time: the sum of the medians, in `timing/runs.jsonl`, of the
  passing runs of each test module and acceptance file that the check runs. A target with no
  passing record uses one small module or one named statement. Measure a new module on its first executable revision. A check whose expected time is
  over 300 s is a defective check: it is cut down before the task starts, never optimized into
  the bound inside the task.
- Run time varies with host load. For a target with at least three passing records, its spread is
  the ratio of its slowest passing run to its median; with fewer records, the spread is 1.3 (the
  median spread of the ten targets with three or more passing runs on 2026-11-27, whose slowest
  runs were 1.28 times their median at the median and up to 2.0 times).
- The current focused command must pass its assertions and finish within 300 s for task
  closure. On an overrun, keep the result and inspect the exact selectors, fixtures and
  commands they launch. Compare each with the active task's required observation (SPEC004–SPEC006).
  If the command includes another task's work or a complete milestone file, correct the task
  check first. Assign those assertions to their owner, retain their full inputs there, and
  measure the corrected focused command. T300's complete unchanged RX09 reporting control
  belongs to KM0. Use the corrected measurement to decide whether a contingency applies.
  For a correctly scoped overrun, check competing jobs and repeat on comparable inputs.
  If the runner refuses a repeat after an overrun, measure the same selection with `just slow`
  and the reason for the repeat. Return to the ordinary command for closure.
  If the median of three comparable runs exceeds 300 s, investigate the largest measured cost
  under its contingency task. For a median within the observed spread of the limit, check host
  contention first. Above that margin, start with the measured phase breakdown. The spread
  determines where to investigate. The closure bound stays 300 s.
- A contingency ends when the three-run median is at most 300 s and the current focused run
  passes within the bound. Record complete milestone workloads as long runs.
- A change between two medians that is smaller than the spread is noise: do not act on it, and do
  not report it as a gain.

## Step 1: measure the whole loop first

Before any change, collect the timing of one complete loop run of the active task, phase by
phase, from the records of the timing history (`timing/runs.jsonl` and its phase fields; module
and statement records where they exist):

| Phase | What it covers |
| --- | --- |
| Build | rebuild of the edited module and every module that imports it; native compilation of test executables |
| Startup | container command, Lean process and imports, protocol peers, engines such as Sage |
| Execution | elaboration and run of the test module or statements: reading, lowering, preparation, dispatch, admission, binding |
| Acceptance | the acceptance files of the check, statement by statement |
| Harness | logging, file writes, sequential module runs, waiting on locks |

If a phase has no record, add the record first (one row per phase is enough). Do not guess where
the time goes.

## Step 2: write the ordered problem list

Write the triage table of the constitution for the loop: operation, cost per call, multiplying
factors, aggregate cost, priority, proposed remedy, remaining measured cost. The aggregate is the
cost per call times its actual multipliers: calls per statement, statements per file, files per
check, repetitions, rebuilt importers.

Sort the table by aggregate cost and classify each row by magnitude:

| Class | Aggregate per loop | Action |
| --- | --- | --- |
| Hours | 1 h or more | The loop is broken. Stop and treat it as a structural defect: a full rebuild, an exponential data size, a hang. |
| Minutes | 1 min to 1 h | The candidates. Work on the largest first. |
| Seconds | 1 s to 1 min | Only when its multiplier puts it in the minutes class, or when it is all that remains above the target. |
| Milliseconds | under 1 s | Ignore in loop work. |

A cost that grows faster than its input (for example a request that expands to millions of nodes
and compresses to about a thousand) is first, whatever its present size, because it grows with
every larger statement.

## Step 3: fix the top row, then measure again

- Work only on the top row. Prefer a structural remedy that removes the cost (stop a repeated
  computation, share a repeated subgraph, reuse a process, cut an import fan-out, move an
  aggregate target out of the focused loop) over a local speed-up of the same work.
- Keep the public consumer, its inputs and its expectations unchanged. A remedy that changes what
  is checked is not a remedy.
- After the change, repeat Step 1 on the same inputs and update the table with the remaining
  measured cost.
- Stop when the contingency meets the closure conditions above. Every remaining row
  goes to the final performance work, with its measurement. Then return to the active task.

## Step 4: reassess when the gains are small

Stop and start again from Step 1 with a fresh, complete measurement when any of these holds:

- two consecutive remedies each changed the median by less than the spread (the change was noise);
- the recent work changed costs in the seconds or milliseconds class while the loop is still
  minutes over the target;
- the largest row of the new table is not the row that the last remedy addressed.

Small gains on a loop that is minutes over its bound mean that the dominant cost is somewhere
else, or that it is structural (rebuild scope, data size, process startup). Climbing further on
the same row does not converge.

## Where the work is recorded

- The triage table is a file of the run's evidence, committed with the remedy, and its
  conclusion goes into the commit message: the row, its cost before and after, and the
  remaining rows.
- The remedy belongs to the contingency task of its cost area (plan, M0). It is never done under
  the name of a functional task, and a functional task never waits for it: the worker does the
  contingency task first and then returns to the active task.

## Defective and replacement practice

| Defective | Replacement |
| --- | --- |
| Write a check that runs a whole suite or many modules, then optimize to fit it. | Sum the medians of what the check runs before writing it; over 300 s, cut the check. |
| Optimize the first slow thing that a trace shows. | Measure the whole loop by phase, sort by aggregate cost, fix the top row. |
| Spend hours to bring a 310 s loop to 300 s. | Check load and repeat the same focused command. Use the median to decide whether to start contingency work. |
| Report a 2 % gain as progress. | A change smaller than the spread is noise. |
| Keep tuning one phase while each step gains seconds. | After two small gains, re-measure the whole loop and rebuild the table. |
| Optimize inside a functional task, or leave an over-bound loop as a recorded row. | Do the cost area's contingency task first, measured first, then return to the task. |
