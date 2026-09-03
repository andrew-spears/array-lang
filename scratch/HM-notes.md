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

## Dependent types

Now suppose we have matrix types, so (3, 2) is the type of a 3x2 matrix.

- has type (m : Nat) -> (n : Nat) -> (m, n) -> (m, n) -> (m, n)
  where m and n are probably implicit.

for example, if we know A : (2, 3), then A + B must have type (2, 3).

or we could define a function `double : {m n : Nat} -> (m, n) -> (m, n)` which doubles the elements of a matrix A. Implicit inputs like this are really the same as universally quantified type variables:

`forall m n, (m, n) -> (m, n)`

except that m, n here have to be Nats, not types. This is actually quite distinct from what we did we let \_ in polymorphism. We need type schemes which allow things like

`forall m n : Nat, (m, n) -> (m, n)`

Lets try to infer the type of double A. Let
`env = double : forall m n : Nat, (m, n) -> (m, n), A : (2, 3)`

```
env |- double A
  fresh 't1
  env |- double : ('m, 'n) -> ('m, 'n) -| {} -- gets instantiated to fresh variables
  env |- A : (2, 3) -| {}
: 't -| [('m, 'n) -> ('m, 'n) = (2, 3) -> 't]
```

now solving those constraints.

```
('m, 'n) -> ('m, 'n) = (2, 3) -> 't
('m, 'n) = (2, 3), ('m, 'n) = 't
```

We also need a rule that says to split a constraint on shapes into constraints on dimensions, e.g. ('m, 'n) = (2, 3) becomes m = 2, n = 3. Maybe a more general rule - for a constraint where both sides use the same type constructor, all fields must be equal, or something like that.

```
'm = 2, 'n = 3, ('m, 'n) = 't
subst 2 / 'm
'n = 3, (2, 'n) = 't
subst 3 / 'n
(2, 3) = 't
subst (2, 3) / 't
```

so we get {(2, 3) / 't, 3 / 'n, 2 / 'm}. makes sense.

What about a function like matrix multiplication:

`Dot : forall m n k : Nat, (m, n) -> (n, k) -> (m, k)`

Lets try to infer Dot (Dot A B) C, where A : (2, 3) and C : (4, 5), but we know nothing about B.

let `env = Dot : forall m n k : Nat, (m, n) -> (n, k) -> (m, k), A : (2, 3), C: (4, 5)`

```
env |- (Dot ((Dot A) B)) C
    fresh t1
    env |- Dot ((Dot A) B)
        fresh t2
        env |- Dot : (m1, n1) -> (n1, k1) -> (m1, k1)
        env |- (Dot A) B
            fresh t3
            env |- Dot A
                fresh t4
                env |- Dot : (m2, n2) -> (n2, k2) -> (m2, k2) -| {}
                env |- A : (2, 3) -| {}
            : t4 -| [(m2, n2) -> (n2, k2) -> (m2, k2) = (2, 3) -> t4]
            env |- B : fresh t5 -| {}
        : t3 -| [(m2, n2) -> (n2, k2) -> (m2, k2) = (2, 3) -> t4, t4 = t5 -> t3]
    : t2 -| [
        (m2, n2) -> (n2, k2) -> (m2, k2) = (2, 3) -> t4,
        t4 = t5 -> t3,
        (m1, n1) -> (n1, k1) -> (m1, k1) = t3 -> t2
    ]
    env |- C : (4, 5) -| {}
: t1 -| [
    (m2, n2) -> (n2, k2) -> (m2, k2) = (2, 3) -> t4,
    t4 = t5 -> t3,
    (m1, n1) -> (n1, k1) -> (m1, k1) = t3 -> t2,
    t2 = (4, 5) -> t1
]
```

Solving constraints:

```
(m2, n2) -> (n2, k2) -> (m2, k2) = (2, 3) -> t4,
t4 = t5 -> t3,
(m1, n1) -> (n1, k1) -> (m1, k1) = t3 -> t2,
t2 = (4, 5) -> t1

subst m2, n2 = 2, 3

(3, k2) -> (2, k2) = t4,
t4 = t5 -> t3,
(m1, n1) -> (n1, k1) -> (m1, k1) = t3 -> t2,
t2 = (4, 5) -> t1

subst (3, k2) -> (2, k2) = t4

(3, k2) -> (2, k2) = t5 -> t3,
(m1, n1) -> (n1, k1) -> (m1, k1) = t3 -> t2,
t2 = (4, 5) -> t1

subst t5 = (3, k2)

(2, k2) = t3,
(m1, n1) -> (n1, k1) -> (m1, k1) = t3 -> t2,
t2 = (4, 5) -> t1

subst t3 = (2, k2)

(m1, n1) -> (n1, k1) -> (m1, k1) = (2, k2) -> t2,
t2 = (4, 5) -> t1

subst m1, n1 = 2, k2

(k2, k1) -> (2, k1) = t2,
t2 = (4, 5) -> t1

subst (k2, k1) -> (2, k1) = t2

(k2, k1) -> (2, k1) = (4, 5) -> t1

subst (k2, k1) = (4, 5)

(2, 5) = t1

```

we get (2, 5 as expected). We implicitly figured out that B must have been (3, 4).

So the types in our language are now dependent with universally quantified variables. For now, we fix those variables to be only dimensions/shapes, i.e. Nats.

so a type may look like

`Dot : forall m n k, (m, n) -> (n, k) -> (m, k)`

where m n k are implicitly nats. or

`forall {}, (2, 5)`

Then during inference, we may still need polymorphism from let \_ in. Say we are inferring

`let id = fun x => x in id`

the type of id during inference would be

`forall 't, forall m n, (m, n) -> (m, n)`

of course the 't doesnt really matter here unless our matrices had carrier types. If a matrix could contain ints or bools and we represented types as `(rows, cols) carrier`, then we might see

`forall 't, forall m n, (m, n) 't -> (m, n) 't`

## Refined approach

Every type scheme is `forall [tvars] [dvars], t`, and the variable types and variable dimensions are treated exactly the same. We rely on construction to put them in their proper places, e.g. dimensions are always in shapes like (m, n) and types never appear in shapes.

example:
env = {dot : forall m n k, (m, n) -> (n, k) -> (m, k)
+: forall m n, (m, n) -> (m, n) -> (m, n)
I: (2, 2)}
env is implicit before all |-
e = let f = fun x => x + I in f

|- let f = fun x => x + I in f
|- fun x => x + I
fresh t1
{x : t1} |- (+ (+ x)) I
fresh t2
{x : t1} |- (+ (+ x))
fresh t3
{x : t1} |- + : (m1, n1) -> (m1, n1) -> (m1, n1) -- instantiate DVars
{x : t1} |- (+ x)
fresh t4
{x : t1} |- + : (m2, n2) -> (m2, n2) -> (m2, n2) -- instantiate DVars
{x : t1} |- x : t1
: t4 -| {(m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
: t3 -| {(m1, n1) -> (m1, n1) -> (m1, n1) = t4 -> t3, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
{x : t1} |- I : (2, 2)
: t2 -| {t3 = (2, 2) -> t2, (m1, n1) -> (m1, n1) -> (m1, n1) = t4 -> t3, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
: t1 -> t2 -| {t3 = (2, 2) -> t2, (m1, n1) -> (m1, n1) -> (m1, n1) = t4 -> t3, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
generalize
unify {t3 = (2, 2) -> t2, (m1, n1) -> (m1, n1) -> (m1, n1) = t4 -> t3, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
subst (2, 2) -> t2 / t3
{(m1, n1) -> (m1, n1) -> (m1, n1) = t4 -> (2, 2) -> t2, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
{(m1, n1) -> (m1, n1) = t4 -> (2, 2), (m1, n1) = t2, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
{(m1, n1) = t4, (m1, n1) = (2, 2), (m1, n1) = t2, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
subst (m1, n1) / t4
{(m1, n1) = (2, 2), (m1, n1) = t2, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> (m1, n1)}
{m1 = 2, n1 = 2, (m1, n1) = t2, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> (m1, n1)}
subst 2 / m1
{n1 = 2, (2, n1) = t2, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> (2, n1)}
subst 2 / n1
{(2, 2) = t2, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> (2, 2)}
subst (2, 2) / t2
{(m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> (2, 2)}
{(m2, n2) -> (m2, n2) = t1, (m2, n2) =(2, 2)}
subst (m2, n2) -> (m2, n2) / t1
{(m2, n2) =(2, 2)}
{m2 = 2, n2 = 2}
subst 2 / m2
{n2 = 2}
subst 2 / n2
-- back subst:
(2, 2) -> t2 / t3; (m1, n1) / t4; 2 / m1; 2 / n1; (2, 2) / t2; (m2, n2) -> (m2, n2) / t1; 2 / m2; 2 / n2
(2, 2) -> (2, 2) / t3; (2, 2) / t4; 2 / m1; 2 / n1; (2, 2) / t2; (2, 2) -> (2, 2) / t1; 2 / m2; 2 / n2
so t1 = (2, 2) -> (2, 2) -- so the new env is {f : (2, 2) -> (2, 2)}
{f : (2, 2) -> (2, 2)} |- f : (2, 2) -> (2, 2)
so we get (2, 2) -> (2, 2), as expected

This means our substitutions need to be qualitatively different for types vs dims.
types get substituted for OpenTypes, but dims get substituted for either nats or other dims. Otherwise they behave the same way

slightly different example:
env = {dot : forall m n k, (m, n) -> (n, k) -> (m, k)
+: forall m n, (m, n) -> (m, n) -> (m, n)
I: forall m, (m, m)}
env is implicit before all |-
e = let f = fun x => x + I in f

|- let f = fun x => x + I in f
|- fun x => x + I
fresh t1
{x : t1} |- (+ (+ x)) I
fresh t2
{x : t1} |- (+ (+ x))
fresh t3
{x : t1} |- + : (m1, n1) -> (m1, n1) -> (m1, n1) -- instantiate
{x : t1} |- (+ x)
fresh t4
{x : t1} |- + : (m2, n2) -> (m2, n2) -> (m2, n2) -- instantiate
{x : t1} |- x : t1
: t4 -| {(m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
: t3 -| {(m1, n1) -> (m1, n1) -> (m1, n1) = t4 -> t3, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
{x : t1} |- I : (m3, m3)
: t2 -| {t3 = (m3, m3) -> t2, (m1, n1) -> (m1, n1) -> (m1, n1) = t4 -> t3, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
: t1 -> t2 -| {t3 = (m3, m3) -> t2, (m1, n1) -> (m1, n1) -> (m1, n1) = t4 -> t3, (m2, n2) -> (m2, n2) -> (m2, n2) = t1 -> t4}
generalize
...
{f : (m3, m3) -> (m3, m3)}
