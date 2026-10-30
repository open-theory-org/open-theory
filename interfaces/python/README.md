# python: `opentheory` SDK

```python
import sys; sys.path.insert(0, "interfaces/python")
from opentheory import verify
r = verify("/tmp/cert")
print(r.accepted, r.level, r.claim, r.reason)
```

A thin wrapper around `verifier/core`, using only the standard library. Packaging for pip comes later.
