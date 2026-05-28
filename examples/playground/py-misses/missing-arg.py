# A required parameter must be supplied — either positionally or by
# name. Forgetting one is a static error.

def transfer(src, dst, amount):
    return {"from": src, "to": dst, "amount": amount}

# Forgot `dst`. Python: TypeError at the call site. Inty: caught.
r = transfer(src="checking", amount=50)
