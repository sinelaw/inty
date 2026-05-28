# `Literal["...", "..."]` declares the exact strings allowed.
# Passing one outside the set is a static error — no typo can slip
# through to a `raise ValueError` at runtime.

LogLevel = Literal["debug", "info", "warn", "error"]

def log(level: LogLevel, msg: str) -> None:
    pass

log("info", "starting up")
log("warm", "uh oh")   # typo for "warn"
