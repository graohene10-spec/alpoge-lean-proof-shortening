# Lean proof shortening

Shorter proofs for the initial dependency slice of Levent Alpöge's Lean formalization, announced on 20 November 2026. [Upstream release](https://alpo.ge/remark.pdf)

## Source files

Each path under `src/` contains one complete Lean module. Where several edits to a module passed a joint check, the file contains those edits together. [Verification index](verification.tsv) lists the included candidates, the nonblank lines saved, and the file's SHA-256. [Snapshot](snapshot.json) records the export totals.

To use these files, start with the original release and copy the files into the matching paths under its `src/` directory. The original `lean.tar.gz` has SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. Use Lean `v4.33.1` and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`.

## Verification

For checked rows, verification uses the imports from the pinned upstream build. Multiple edits to a file were checked together; single edits use their individual verification record. The checks compare the elaborated types and axiom reports of edited declarations and reject new warnings. These results cover the modules individually, not the whole overlay as a single build.

Rows marked `module recheck pending` contain proposed structural refactors. Their SHA-256 identifies the candidate source; the original candidate IDs and the downstream smoke result are inherited from the base snapshot, not new verification of these files. Use the base snapshot for those modules until the recheck passes.

## 中文说明

`src/` 按原工程目录存放完整的 Lean 文件，每个模块只保留一份。将已核验文件放入原工程的同名位置即可使用。标为 `module recheck pending` 的文件是待复验的结构改写，复验前使用基线版本。核验明细见 [verification.tsv](verification.tsv)，导出统计见 [snapshot.json](snapshot.json)。
