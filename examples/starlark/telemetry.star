# Starlark analysis script for JSONL process telemetry inside a secure enclave.
# Expected record schema (one JSON object per line):
# {
#   "timestamp": "2026-11-26T00:50:12Z",
#   "pid": 4812,
#   "ppid": 1024,
#   "process": "bash",
#   "argv": ["bash", "-c", "echo aGVsbG8= | base64 -d | sh"],
#   "exit_code": 0,
#   "strings": ["aGVsbG8=", "/bin/sh"]
# }

# The record's type, from the schema above, and the type of a finding.
# type Record = {timestamp: str, pid: int, ppid: int, process: str, argv: list[str], exit_code: int, strings: list[str]}
# type Finding = {matched: bool, rule: str, severity: str, pid: int, ppid: int, timestamp: str, process: str, exit_code: int, matched_argv: list[str]}

SUSPICIOUS_SHELLS = {"sh": True, "bash": True, "zsh": True, "dash": True, "powershell": True, "pwsh": True}
ENCODED_MARKERS = ["-enc", "-encodedcommand", "base64", "frombase64string"]

def _contains_encoded_pattern(argv, strings):
    # type: (list[str], list[str]) -> bool
    for arg in argv:
        low_arg = arg.lower()
        for marker in ENCODED_MARKERS:
            if marker in low_arg:
                return True

    for s in strings:
        low_s = s.lower()
        for marker in ENCODED_MARKERS:
            if marker in low_s:
                return True

    return False

def analyze_record(record):
    # type: (Record) -> list[Finding]
    proc_name = record["process"].lower()
    argv = record["argv"]
    strings = record["strings"]
    exit_code = record["exit_code"]

    # Pattern: shell or scripting runtime invoked with encoded execution markers
    matched = proc_name in SUSPICIOUS_SHELLS and _contains_encoded_pattern(argv, strings)
    finding = {
        "matched": True,
        "rule": "encoded_shell_execution",
        "severity": "high",
        "pid": record["pid"],
        "ppid": record["ppid"],
        "timestamp": record["timestamp"],
        "process": record["process"],
        "exit_code": exit_code,
        "matched_argv": argv,
    }

    # The finding, or none: inty types a dict literal as a record, so the two
    # outcomes can't be differently-shaped dicts. A list (rather than
    # `Finding | None`) needs no None test where it's used, which inty can't
    # narrow on in a loop.
    return [finding] if matched else []

def process_stream(records):
    # type: (list[Record]) -> {records_scanned: int, matches_found: int, findings: list[Finding]}
    findings = []  # type: list[Finding]
    total_seen = 0

    for rec in records:
        total_seen += 1
        findings.extend(analyze_record(rec))

    return {
        "records_scanned": total_seen,
        "matches_found": len(findings),
        "findings": findings,
    }
