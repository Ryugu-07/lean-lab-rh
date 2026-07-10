# optional-tooling

- Date: 2026-07-08
- Scope: LeanDojo and lean-mcp-like tooling.

## LeanDojo

- Installed: `lean-dojo==4.20.0` in `.venv` with Python 3.12.13.
- Dependencies added: Homebrew `python@3.12` and `wget`.
- Import smoke test: passed.
- Programmatic trace smoke test: failed against Lean 4.31.0 because LeanDojo's bundled `ExtractData.lean` no longer typechecks with this Lean version.
- Status: installed, but not usable as the main project interaction layer for the current Lean 4.31.0 toolchain.

## Lean LSP MCP

- Installed: `lean-lsp-mcp==0.28.0` in `.venv`.
- Server startup: passed with `--lean-project-path /Users/karasuakamatsu/lean-lab`.
- Tool listing: passed; server exposed 23 tools.
- Diagnostics smoke test: `LeanLab/HelloProof.lean` returned success with no diagnostics.
- `lean_run_code` smoke test: passed for `example : 2 + 2 = 4 := by norm_num`.
- Goal-state smoke test: `lean_goal` on the hello proof returned `⊢ 2 + 2 = 4`.
- Status: usable as the current agent-facing goal/diagnostic tool.
