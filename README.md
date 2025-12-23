# Hoare Verifier (HoVer)

this program takes a program written in (a subset of) python annotated with pre, post, and invariant conditions. It generates verification conditions and uses z3-solver to check if a program is valid.

# Usage and Installation

I recommend using uv (the python package manager). Simply

```
uv run -m hover /path/to/program
```

this will install all dependencie and run the program. Otherwise to use regular python with install dependencies (z3-solver, pytest) that are in pyproject.toml and run

```
python -m hover /path/to/program
```

example

```
uv run -m hover examples/absolute_value.py
```

# Supported Syntax
Each program must have a pre and post condition marked by `# pre` and `# post` comments. They can be placed anywhere in program. 

**integer values**: any and all assigned variables must be integer values. 

**expressions**: arithmetic (+, -, *) and comparison (<, <=, ==, >=, >) are supported

**statements**: we only support the following statements

- **assignments** (as explained above)
- **if-else conditionals** support if-else (elif is not supported)
- **while**: supported, but must be preceded by an magic comment `# inv: <boolean>`

some default samples are listed in `examples/sample/` and more examples are written in `examples/`

note that examples started with `invalid_` are invalid programs and will have an output of `Unverified`

# Code Analysis 
source code is located in `hover/`

First, `parser.py` defines a helper function that parses the pre, post, and inv (using tokenizer) magic comments. It returns a dictionary for pre, post and the invariants.

`ast_to_ir.py` defines a class that uses pyhon's abstract syntax tree and converts the expressions and statements recursively into the internal representations in `ir.py`. The internal representations are used because ast is wrapped in unnecessary syntax. 

`ir_to_z3.py` defines a fucntion that converts our internal represntations into z3 expressions such that we can put them into z3 to solve. 

`vc_generator.py` defines a class that recursively generates the weakest preconditions of a statement given its post condition. 

lastly, `verify.py` defines a function where given the source code, the annotations (for invariants), precondition string, and postcondition string, verifies the program. It

1. translates the abstract syntax tree (ast) into our internal representations (ir) and parses
2. then, we parse the pre condition and post condition strings with ast and translate them into internal representations (ir)
3. from there, we generate the verification conditions. 
4. then, for each verification condition, we convert the ir to z3, and push it to our solver
5. we check to see if z3 can find a counterexample
6. if no counterexample is found, the program is verified, otherwise it is unverified and we print the found counterexample. 

in `__main__.py` using `sys.argv` we get the program arguments, read the source code, parse the annotations, and then pass in the details into the `verify_program` function. 

# example hoare logic code 


## Examples

Below is a detailed breakdown of the examples provided in the `examples/` directory. Each example includes pre-conditions, post-conditions, and sometimes loop invariants, which are used by the Hoare Logic Verifier (HoVer) to prove correctness.

### Verified Examples

These programs are successfully verified because their logic guarantees that the post-conditions are met if the pre-conditions are true.

*   **`absolute_value.py`**
    *   **Pre-condition**: `True` (the program can start in any state).
    *   **Post-condition**: `res >= 0 and (res == x or res == -x)`. The result `res` must be non-negative and equal to either the original `x` or its negation.
    *   **Explanation**: The code uses an `if` statement to check if `x` is non-negative. If it is, `res` is set to `x`. If `x` is negative, `res` is set to `-x`. In both cases, `res` becomes the absolute value of `x`, satisfying the post-condition.

*   **`in_place_swap.py`**
    *   **Pre-condition**: `x == A and y == B`. We assume `x` and `y` start with some initial values `A` and `B`.
    *   **Post-condition**: `x == B and y == A`. After execution, `x` should hold `B` and `y` should hold `A`.
    *   **Explanation**: This classic algorithm swaps two variables without a temporary variable.
        1.  `x = x + y` makes `x` the sum of the original values (`A + B`).
        2.  `y = x - y` becomes `y = (A + B) - B`, which sets `y` to `A`.
        3.  `x = x - y` becomes `x = (A + B) - A`, which sets `x` to `B`.
        The sequence of operations correctly swaps the initial values, thus satisfying the post-condition.

*   **`max_of_two.py`**
    *   **Pre-condition**: `True`.
    *   **Post-condition**: `res >= a and res >= b and (res == a or res == b)`. The result `res` must be greater than or equal to both `a` and `b`, and it must be one of them.
    *   **Explanation**: The code checks if `a` is greater than `b`. If so, `res` is assigned `a`; otherwise, `res` is assigned `b`. This logic directly ensures that `res` holds the maximum of the two values, fulfilling the post-condition.

*   **`multiplication.py`**
    *   **Pre-condition**: `y >= 0`. The multiplier `y` must be non-negative.
    *   **Post-condition**: `z == x * y`. The result `z` must equal the product of `x` and `y`.
    *   **Invariant**: `z == x * count and count <= y`. The loop invariant states that `z` is always the product of `x` and the current `count`, and `count` never exceeds `y`.
    *   **Explanation**: This program calculates `x * y` by adding `x` to `z` for `y` times.
        - The invariant holds initially (`z = 0`, `count = 0`).
        - Each iteration, `z` increases by `x` and `count` increases by 1, maintaining `z == x * count`.
        - The loop terminates when `count == y`. At this point, the invariant `z == x * count` implies `z == x * y`, satisfying the post-condition.

*   **`simple_sum.py`**
    *   **Pre-condition**: `x == 10`.
    *   **Post-condition**: `res == 15`.
    *   **Explanation**: The program starts with `x` as 10. It then computes `x = x + 2`, making `x` equal to 12. Finally, it computes `res = x + 3`, which is `12 + 3 = 15`. This directly meets the post-condition.

*   **`sample/loop_invariant.py`**
    *   **Pre-condition**: `n >= 0`.
    *   **Post-condition**: `2 * s == n * (n + 1)`. This is the formula for the sum of the first `n` integers (`s = n*(n+1)/2`).
    *   **Invariant**: `0 <= i <= n and 2 * s == i * (i + 1)`. The invariant maintains that `s` is the sum of integers up to the current value of `i`.
    *   **Explanation**: This program calculates the sum of integers from 1 to `n`.
        - The invariant holds at the start (`i=0`, `s=0`).
        - Inside the loop, `i` is incremented, and then `s` is increased by the new `i`. This maintains the sum property.
        - When the loop finishes, `i == n`. The invariant `2 * s == i * (i + 1)` becomes `2 * s == n * (n + 1)`, which is exactly the post-condition.

*   **`sample/simple_assignment.py`**
    *   **Pre-condition**: `x >= 0`.
    *   **Post-condition**: `y == x + 1`.
    *   **Explanation**: The code directly assigns `y` to the value of `x + 1`. This trivially satisfies the post-condition.

### Unverified Examples

These programs fail verification because their logic contains flaws that prevent the post-conditions from being guaranteed.

*   **`invalid_if_precondition.py`**
    *   **Pre-condition**: `True`.
    *   **Post-condition**: `res != 0`. The result must not be zero.
    *   **Explanation**: The logic fails for a specific input. If `x` is `-1`, the condition `x > 0` is false, so the `else` block is executed. This sets `res = x + 1`, which evaluates to `-1 + 1 = 0`. This outcome violates the post-condition, so the program is unverified.

*   **`invalid_invariant.py`**
    *   **Pre-condition**: `n > 0`.
    *   **Post-condition**: `i == n`.
    *   **Invariant**: `i < n`.
    *   **Explanation**: The verification fails because the invariant is incorrect for proving the post-condition.
        1.  **Invariant is not preserved**: The invariant must hold true *at the end* of each loop iteration. When `i` becomes `n-1`, the loop runs one more time, setting `i` to `n`. At this point, the invariant `i < n` is false.
        2.  **Invariant + Loop Termination does not imply Post-condition**: When the loop terminates, the condition `i < n` is false, meaning `i >= n`. The invariant `i < n` is also supposed to hold *before* the loop check. If the loop terminates, `i` must be `>= n`. The combination of the invariant and the loop termination condition does not logically lead to the post-condition `i == n`. A correct invariant would be `i <= n`.

*   **`invalid_simple_assignment.py`**
    *   **Pre-condition**: `x >= 0`.
    *   **Post-condition**: `y == x + 1`.
    *   **Explanation**: The code sets `y = x + 10`. This is a direct contradiction to the post-condition, which requires `y` to be `x + 1`. The program is unverified because `x + 10` is never equal to `x + 1`.

