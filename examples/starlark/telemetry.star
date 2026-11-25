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

SUSPICIOUS_SHELLS = {"sh": True, "bash": True, "zsh": True, "dash": True, "powershell": True, "pwsh": True}
ENCODED_MARKERS = ["-enc", "-encodedcommand", "base64", "frombase64string"]

def _contains_encoded_pattern(argv, strings):
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
    proc_name = record.get("process", "").lower()
    argv = record.get("argv", [])
    strings = record.get("strings", [])
    exit_code = record.get("exit_code", 0)

    # Pattern: shell or scripting runtime invoked with encoded execution markers
    matched = proc_name in SUSPICIOUS_SHELLS and _contains_encoded_pattern(argv, strings)
    finding = {
        "matched": True,
        "rule": "encoded_shell_execution",
        "severity": "high",
        "pid": record.get("pid"),
        "ppid": record.get("ppid"),
        "timestamp": record.get("timestamp"),
        "process": record.get("process"),
        "exit_code": exit_code,
        "matched_argv": argv,
    }

    # A finding, or None for no match: inty types a dict literal as a record,
    # so the two outcomes can't be differently-shaped dicts.
    return finding if matched else None

def process_stream(records):
    findings = []
    total_seen = 0

    for rec in records:
        total_seen += 1
        res = analyze_record(rec)
        if res != None:
            findings.append(res)

    return {
        "records_scanned": total_seen,
        "matches_found": len(findings),
        "findings": findings,
    }
