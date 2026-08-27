Hindley Milner algorithm notes

Step through program expressions in order, one full pass.
We continually keep track of an `env` (environment) that maps variable names to their types.

For each expression `e`, we infer a type for `e` by first inferring subexpressions of `e`, then building a set of type constraints, then solving this set of constraints (and returning it as well).

## Building Constraints

We can write inference on `e` as
`env |- e : t -| C`
where `C` is a set of constraints on types.

The simplest rules are when `e` is a name or constant.

```
{} |- true : bool -| {} (no constraints generated)
{} |- 0 : int -| {} (no constraints generated)
{x : bool} |- x : bool -| {} (no constraints generated)
{x : int} |- x : int -| {} (no constraints generated)
{} |- x :  -| {} would fail because x is not bound in the environment.
```

If e is an if else expression

```
if e1 then e2 else e3
```

First infer its subexpressions. Suppose we get

```
env |- e1 : t1 -| C1
env |- e2 : t2 -| C2
env |- e3 : t3 -| C3
```

Then

```
env |- if e1 then e2 else e3 : 't -| C1 + C2 + C3 + C
    if fresh 't (this just means 't is a new type not used already)
    and env |- e1 : t1 -| C1
    and env |- e2 : t2 -| C2
    and env |- e3 : t3 -| C3
    and C = {
        t1 = bool
        t2 = 't
        t3 = 't
    }
```

where + denotes set union.
We would then actually solve for 't using the set of constraints, but we will get to that later.

If we have an anonymous function `fun x => e`:

```
env |- fun x => e : 't -> t1 -| C
    if fresh 't
    and env + {x : 't} |- e : t1 -| C
```

so we first append x : 't to the env, then infer e, then return its constraint set.

For example

```
{} |- fun x => if x then 1 else 0 : 'a -> 'b
    {x : 'a} |- if x then 1 else 0 : 'b
        {x : 'a} |- x : 'a -| {}
        {x : 'a} |- 1 : int -| {}
        {x : 'a} |- 0 : int -| {}
    {x : 'a} |- if x then 1 else 0 : 'b -| {'a = bool, 'b = int}
{} |- fun x => if x then 1 else 0 : 'a -> 'b -| {'a = bool, 'b = int}
...
solve constraints
...
fun x => if x then 1 else 0 : bool -> int
```

Function application `e1 e2`:

```
env |- e1 e2 : 't -| C1 + C2 + C
    if fresh 't
    and env |- e1 : t1 -| C1
    and env |- e2 : t2 -| C2
    C = {t1 = t2 -> t'}
```

Example:

let I be the initial environment that binds ( + ) : int -> int -> int

```
I |- ( + ) 1 : 't
    I |- ( + ) : int -> int -> int -| {}
    I |- 1 : int -| {}
I |- ( + ) 1 : 't -| {int -> int -> int = int -> 't}
...
solve constraints
...
I |- ( + ) 1 : int -> int
```

## Solving Constraints

Suppose we have the constraints

```
'x -> ('x -> int) = int -> 'y
'x -> 'x = 'y
```

We can solve by taking the 2nd constraint and substituting `{'x -> 'x / 'y}` everywhere. (this notation `{a / b}` means 'substitute a for b')

```
'x -> ('x -> int) = int -> ('x -> 'x)
```

Now both sides are arrow types, so the input and output types must equate.

```
'x = int
'x -> int = 'x -> 'x
```

This gives us a new substitution: `{int / 'x}`.

```
int -> int = int -> int
```

We again equate inputs and outputs:

```
int = int (unifies)
int = int (unifies)
```

so we are done. The substitutions we did were

```
{'x -> 'x / 'y,}; {int 'x}
```

We could also have started from the first constraint.

```
'x -> ('x -> int) = int -> 'y
'x -> 'x = 'y
```

equate inputs and outputs:

```
'x = int
'x -> int = 'y
'x -> 'x = 'y
```

now we can subst `{int / 'x}`

```
int -> int = 'y
int -> int = 'y
```

now subst `{int -> int / 'y}`

```
int -> int = int -> int (unifies)
```

and again we are done, with substitutions

```
{int / 'x}; {int -> int / 'y}
```

unification algorithm:

1. Pick some constraint t1 = t2 and remove from set.
2. Reduce t1 = t2. Either:
   -update solution with new substitution
   -Or add new constraints back to set
   -Or fail (if contradiction)

reductions: match t1 = t2 with
| 'x = 'x => just ignore and remove
| t1 -> t2 = t3 -> t4 => add constraints t1 = t3, t2 = t4
| 'x = t (where 'x does not appear in t) => substitute {t / 'x}
| else => fail

another example:

```
('x -> int) -> 'x  = 'y -> int
'x -> 'x = 'y
```

reduce

```
('x -> int) = 'y
'x  = int
'x -> 'x = 'y
```

subst `{ ('x -> int) / 'y }`

```
'x = int
'x -> 'x = 'x -> int
```

subst `{ int / 'x }`

```
int -> int = int -> int
```

done

## Let and polymorphism

```
{} |- let id = fun x -> x in (let a = id 0 in id true) : 'c
    {} |- fun x -> x : 'a -> 'a -| {} <--- We found that id : 'a -> 'a as intended
        {x : 'a} |- x : 'a -| {}
    --- now use that in the env
    {id : 'a -> 'a} |- let a = id 0 in id true : 'c -| {'a -> 'a = int -> 'b, 'a -> 'a = bool -> 'c}
        {id : 'a -> 'a} |- id 0 : 'b -| {'a -> 'a = int -> 'b} <--- already an issue; we assert that id 'a must be int because it was applied to an int

        {id : 'a -> 'a, a : 'b} |- id true : 'c -| {'a -> 'a = int -> 'b}

```
