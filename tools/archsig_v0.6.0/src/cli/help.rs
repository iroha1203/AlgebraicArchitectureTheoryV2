//! サブコマンドのヘルプ文言（AC3 統一 CLI）。

pub const HELP: &str = "ArchSig: check inputs and answer questions from Atom definitions, Law and ArchMap.
Usage: archsig <check|run|reobserve|digest|inspect|evidence|law-fibers|version> [options]
  check       Validate inputs without computing questions; saving is optional
  run         Compute answers; saving is optional
  reobserve   Evaluate previous and current inputs in one process
  digest      Print vocabulary manifests and canonical SHA-256 digests
  inspect     Inspect definitions/law/archmap declarations or saved result directories
  evidence    Verify selected atoms against local source bytes
  law-fibers  Check an explicitly enumerated finite evaluation table
  version     Print product and semantics versions as JSON
Use archsig help COMMAND (or COMMAND --help) for options.
Common options: --project FILE, --format json|pretty|human, --detail concise|full,
  --max-file-bytes N, --verbose, --progress, --flag=value.
Example (no files are written):
  archsig run --atom-definition counter.atoms.json --law counter.law --archmap counter.archmap.json --ask 'n=evaluate(CountCheck.amount,s=@v/s)'
--help, -h: show help; --version: show version.";

pub const RUN_HELP: &str = "Usage: archsig run --atom-definition D --law L --archmap A --ask 'ID=QUESTION' [options]
  --atom-definition D      Atom definition file (required unless --project, repeatable)
  --law L                  Law file (required unless --project)
  --archmap A              Observations file (required unless --project)
  --ask 'ID=QUESTION'      Question (repeatable; quote $ references)
  --ask-file PATH          Read one question per line (`-` for stdin; ignores blanks and # comments)
  --project FILE           Explicit archsig.project/1 manifest JSON
  --out NEW_DIRECTORY      Save full result and inputs (optional; never overwrite by default)
  --create-parents         Create missing parent directories for --out
  --overwrite              Safely replace an existing --out directory after staging
  --no-fsync               Skip fsync calls when writing --out artifacts
  --reuse DIRECTORY        Recheck an earlier result (optional)
  --format MODE            Output format: json (default), pretty, or human
  --detail LEVEL           Output detail level: concise or full
  --max-file-bytes N       Bound input/artifact file reads in bytes (default: 67108864)
  --shigure-limit KEY=N    Override a SHIGURE resource limit (repeatable)
  --verbose, --progress    Print execution phase and question progress to stderr
  --help, -h               Show this help
Answers and warnings: stdout; execution errors: stderr.
Exit: 0 established, 1 refuted, 2 undetermined, 64 usage, 65 invalid input,
69 unsupported version, 70 internal, 74 I/O, 130 SIGINT, 141 broken pipe, 143 SIGTERM.
Example:
  archsig run --atom-definition counter.atoms.json --law counter.law --archmap counter.archmap.json --ask 'n=evaluate(CountCheck.amount,s=@v/s)'";

pub const REOBSERVE_HELP: &str = "Usage: archsig reobserve [--before-atom-definition D ...] [--before-law L] --before-archmap A --before-ask 'ID=QUESTION' --atom-definition D --law L --archmap A --ask 'ID=QUESTION' [options]
Omitted --before-atom-definition or --before-law inherits the current-side files.
Supports --ask-file PATH, --before-ask-file PATH, --alignment JSON, --out NEW_DIRECTORY,
--create-parents, --overwrite, --no-fsync, --format json|pretty|human, --detail concise|full,
--max-file-bytes N, --shigure-limit KEY=N, --verbose, --progress.
The output contains separate previous and current evaluations. Exit status reflects the current evaluation or an execution failure.";

pub const CHECK_HELP: &str =
    "Usage: archsig check --atom-definition D --law L [--archmap A] [--out NEW_DIRECTORY] [options]
  --atom-definition D      Atom definition file (required unless --project, repeatable)
  --law L                  Law file (required unless --project)
  --archmap A              Observations file (optional)
  --project FILE           Explicit archsig.project/1 manifest JSON
  --out NEW_DIRECTORY      Save checked declarations and inputs (optional)
  --create-parents         Create missing parent directories for --out
  --overwrite              Safely replace an existing --out directory
  --no-fsync               Skip fsync calls when writing --out artifacts
  --format MODE            Output format: json (default), pretty, or human
  --max-file-bytes N       Bound input file reads in bytes (default: 67108864)
  --verbose, --progress    Print execution progress to stderr
  --help, -h               Show this help
Validation status: stdout; execution errors: stderr.
Example: archsig check --atom-definition counter.atoms.json --law counter.law";

pub const DIGEST_HELP: &str = "Usage: archsig digest --atom-definition D [--atom-definition D ...] [options]
  --atom-definition D      Atom definition file (required unless --project, repeatable)
  --project FILE           Explicit archsig.project/1 manifest JSON
  --format MODE            Output format: json (default), pretty, or human
  --max-file-bytes N       Bound input file reads in bytes (default: 67108864)
  --verbose, --progress    Print progress to stderr
  --help, -h               Show this help
Print checked vocabulary manifests and canonical SHA-256 digests directly without bootstrap Law files.";

pub const INSPECT_HELP: &str = "Usage:
  archsig inspect --atom-definition D [--law L] [--archmap A] [options]
  archsig inspect --project FILE [--format MODE] [options]
  archsig inspect --result DIR [--answer ID ...] [--evidence] [--format MODE] [options]
Options:
  --atom-definition D      Atom definition file (repeatable)
  --law L                  Law file (optional; inspect ordinary & SHIGURE declarations)
  --archmap A              ArchMap file (optional; inspect snapshots, subjects & missing slots)
  --project FILE           Explicit archsig.project/1 manifest JSON
  --result DIR             Saved result directory containing result.json
  --answer ID              Select specific answer ID from saved result (repeatable)
  --evidence               Include full proof/node evidence in --result output
  --format MODE            Output format: json (default), pretty, or human
  --max-file-bytes N       Bound input/result file reads in bytes (default: 67108864)
  --verbose, --progress    Print progress to stderr
  --help, -h               Show this help";

pub const EVIDENCE_HELP: &str =
    "Usage: archsig evidence --archmap A --atom SNAPSHOT/ATOM [--source ID=FILE ...] [options]
  --archmap A              ArchMap JSON (required)
  --atom ID                Select snapshot/atom (required, repeatable, distinct)
  --source ID=FILE         Bind a source ID to a local file (repeatable, distinct)
  --format MODE            Output format: json (default), pretty, or human
  --max-file-bytes N       Bound file reads in bytes (default: 67108864)
  --verbose, --progress    Print progress to stderr
  --help, -h               Show this help
Expand explicit references and verify SHA256, UTF-8 byte spans and excerpts.
Revision provenance, coverage, meaning and Law fidelity remain reading obligations.
Result: stdout; errors: receipt JSON/text on stderr. No files are written.
Exit: 0 verified bytes, 64 usage, 65 invalid input, 70 internal, 74 I/O,
130 SIGINT, 141 broken pipe, 143 SIGTERM.";

pub const FIBERS_HELP: &str = "Usage: archsig law-fibers --table TABLE [options]
  --table TABLE            Explicit finite evaluation table JSON (required)
  --format MODE            Output format: json (default), pretty, or human
  --max-file-bytes N       Bound table file read in bytes (default: 67108864)
  --verbose, --progress    Print progress to stderr
  --help, -h               Show this help
Compute counterexamples, partitions and descent on the supplied table.
Complete enumeration and faithful equality tokens are caller obligations; no Law DSL evaluation.
Result: stdout; errors: receipt JSON/text on stderr. No files are written.
Exit: 0 adequate on table (including vacuous), 1 counterexamples, 64 usage,
65 invalid input, 70 internal, 74 I/O, 130 SIGINT, 141 broken pipe, 143 SIGTERM.";

pub const VERSION_HELP: &str = "Usage: archsig version (or archsig --version) [--format json|pretty|human]\nPrint product and semantics versions.";
