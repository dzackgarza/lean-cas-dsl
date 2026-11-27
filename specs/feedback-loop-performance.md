# Feedback-loop performance: how to find and fix the cost that matters

This document is the procedure for performance work on the development loop. It applies when a
loop run of the active task exceeds its bound. It does not apply to the final runtime performance
work, which comes after all functionality (constitution C21). The rules "Timing
history" and "Timing triage" of constitution C24 are the authority; this document makes them
operational.

## The bound and its margin

- The bound of the focused loop is 300 s: the rebuild of the edited owner and its dependents, and
  the run of the unchanged public consumer (`AGENTS.md`, `CONTRIBUTING.md` "Feedback loops").
- A loop is over the bound only when the median of its last three runs on the same inputs is more
  than 360 s (the bound plus 20 %). One slow run is noise until two more confirm it.
- A contingency task ends when the median of three runs is at most 300 s. The gap between the
  trigger (360 s) and the target (300 s) is deliberate: a loop at 301 s or 310 s needs no work.
- A difference between two measurements of less than 10 % or less than 5 s is noise. Do not act
  on it, and do not report it as a gain.

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
- Stop when the loop meets the target (median of three runs at most 300 s). Every remaining row
  goes to the final performance work, with its measurement. Then return to the active task.

## Step 4: reassess when the gains are small

Stop and start again from Step 1 with a fresh, complete measurement when any of these holds:

- two consecutive remedies each removed less than 10 % of the excess over the target, or less than
  30 s;
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
| Optimize the first slow thing that a trace shows. | Measure the whole loop by phase, sort by aggregate cost, fix the top row. |
| Spend hours to bring a 310 s loop to 300 s. | 310 s is under the 360 s trigger: no work. |
| Report a 2 % gain as progress. | Below 10 % or 5 s is noise. |
| Keep tuning one phase while each step gains seconds. | After two small gains, re-measure the whole loop and rebuild the table. |
| Optimize inside a functional task, or leave an over-bound loop as a recorded row. | Do the cost area's contingency task first, measured first, then return to the task. |
