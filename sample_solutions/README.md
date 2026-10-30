# Sample solutions

Bunch of sample solutions from various models.

## Inclusion

Only successful attempts are included in the collection, meaning multiple sessions might be needed to get a valid proof, and harder problems will only have solutions by a few stronger models.

## Prompt structure

### First prompt

#### Syntax

```txt
<instructions>:
<problem>
```

#### `<instructions>`

Lean:
1. `Complete the following lean 4 proof`
1. `Complete the following lean 4 proof and golf it to the smallest size possible`
1. `Complete the following lean 4 proof without using native_decide`
1. `Complete the following lean 4 proof without using native_decide and golf it to the smallest size possible`

Rocq:
1. `Complete the following rocq 9.1 proof`

#### `<problem>`

Lean:
```txt
import Mathlib

...
```

Rocq:
```txt
...
```

### Follow-up prompt

#### Errors

```txt
Line <Number> error(s):
...

Line <Number> error(s):
...
```

#### Refusal

The model refuses to attempt the task or provides a low-effort response, typically citing difficulties with completion or flagging practical constraints, such as not having access to a Lean environment. In such cases, follow-up prompts would include a mix of affirmations that the task is doable and an explicit request for a proper, full-effort attempt or continuation.
