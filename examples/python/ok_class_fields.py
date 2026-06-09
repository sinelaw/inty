# Class bodies accept field declarations. A bare `name: T` declares the
# field's type without an initialiser; `name: T = expr` checks the
# initialiser against the declared type; and a declared field that is
# also assigned in `__init__` constrains that assignment.

class Account:
    # Annotation-only declarations: typed by the annotation alone.
    owner: str
    balance: int

    def __init__(self, owner: str):
        # The `__init__` assignments are checked against the declarations
        # above (order in the body does not matter).
        self.owner = owner
        self.balance = 0

    def deposit(self, amount: int) -> int:
        return self.balance + amount


# Field with a matching initialiser (no `__init__` needed).
class Config:
    name: str = "app"
    retries: int = 3


def describe(a: Account) -> str:
    return a.owner


acc = Account("ada")
total = acc.deposit(100)
who = describe(acc)
cfg = Config()
