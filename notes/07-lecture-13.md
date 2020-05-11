# lambda calculus

An important thing about the notes below: the lambda calculus language we
describe really does only consist of
1. Variabes x where x is a String
2. Expressions e ::= x | λ x. e | e e

So below, any of the capitalized `Name`s and assignments `:=` are not a part of
the lambda calculus, but instead part of the convenient metalanguage used to
describe expressions that are in the lambda calculus. Also I've used the `Name
== e1` operator below to mean that given some previous notation `Name := e2`,
we can think of `e1` as being equivalent *or evaluating* to `e2`.

## datatypes

### booleans
Define
```
True := λ x. λ y. x
False := λ x. λ y. y
```
Then
```
IfThenElse e1 e2 e3 := e1 e2 e3
Not e := IfThenElse e False True
```
for example
```
Not True
  == IfThenElse True False True
  == True False True
  == (λ x. λ y. x) (λ x. λ y. y) (λ x. λ y. x)
  == (λ x. λ y. y)
  == False
```
And we can do conjunction / disjunction:
```
And e1 e2 := IfThenElse e1 e2 False == e1 e2 FALSE
And e1 e2 := e1 True e2
```

#### call-by-value
Notice because we are using call-by-value semantics, we evaluate both arguments
to `IfThenElse`. Even though this language is pure, we need to be careful about
termination. So let's be a little more careful:
```
IfThenElse' e1 e2 e3 := (e1 (λ x. e2) (λ x. e3)) (λ x. x)
```
where `id := λ x. x` is just a dummy variable here that will get passed to the
thunk branches.

### pairs
```
MkPair e1 e2 := λ p. p e1 e2  # here p is the "selector"

Fst p := p (λ x. λ y. x)

Snd p := p (λ x. λ y. y)
```
For example
```
Fst (MkPair True False)
  == Fst (λ p. p True False)
  == (λ p. p True False) (λ x. λ y. x)
  == (λ x. λ y. x) True False
  == True
```
Of course with just a single pair, we can construct an arbitrary sized tuple.
Notice above that `Fst p == p (λ x. λ y. x) == p True`. This might seem odd,
but it's perfectly reasonable for us to use the same "bit values" for different
operations. This encoding `(λ x. λ y. x)` can be used in multiple ways.
Below, we'll use the same encoding for `False` to denote the end of a list.

### lists
We should be careful to define our ADT such that the common operations (nil,
cons, etc.) are easy to implement.
```
Nil := MkPair False False
Cons e l := MkPair True (MkPair e l)
```
So the first element of the pair indicates if we have a nil or a cons. We can
define common operations easily:
```
Head l := Fst (Snd l)

Tail l := Snd (Snd l)

IsEmpty l := Not (Fst l)
```
Recall, we're defining an interface here, it is up to the programmer to use
these operations properly.

### nats
We'll encode a natural number `n` as the `λ x. x` to the `n`th power:
```
0 := λ f. λ z. z           # applies f zero times
1 := λ f. λ z. f z         # applies f one time
2 := λ f. λ z. f (f z)     # applies f two times
3 := λ f. λ z. f (f (f z)) # applies f three times
```
We can define common arithmetic operations:
```
Succ n := λ f. λ z. f (n f z)  # apply f n times to zero, then apply f one more time!

Add m n := m Succ n            # because m f x applies f to x m times

Multiply m n := m (Add n) 0    # similarly

Pow m n := n (Mul m) 1
```

#### TODO Challenge problem
```
Pred n :=

Sub m n :=
```

### booleans and nats
To test if zero, since `n f x` applies `f` to `x` `n` times,
we can have `x` just be `False`, and `f == const True`:
```
IsZero n := n (λ x. True) False
```

## recursion
We need some way for a function to call itself, e.g. `fix f == f (fix f)`.
Consider first what is known as **omega**:
```
(λ x. x x) (λ x. x x)
  == (λ x. x x) (λ x. x x)
  == (λ x. x x) (λ x. x x)
  == (λ x. x x) (λ x. x x)
  ...
```

### Z-combinator
We will use the Z combinator (similar to Y combinator which is used in
call-by-name semantics), since we need to delay evaluation.
```
Z := λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v))
```
We use the `λ v. x x v` to delay evaluation. Let's try crunching this down:
```
Z g
  == λ f. (λ x. f (λ v. x x v)) (λ x. f (λ v. x x v)) g     #1
  == (λ x. g (λ v. x x v)) (λ x. g (λ v. x x v))            #2
  == g (λ v. (λ x. g (λ v. x x v)) (λ x. g (λ v. x x v)) v) #3
  == g (λ v. Z g v)                                         #4
  == g (Z g)                                                #5
```
Notice that 2nd expression ends up within the 3rd, allowing the replacement of
Z.

### example
To use this, our recursion functions need to be defined to take an extra
function argument, and then we can use this definition passed to `Z` to get the
final version. As an example:
```
Factorial' f n := IfThenElse (IsZero n) 1 (Mult n (f (Pred n)))
Factorial := Z Factorial'
```

Next up, we'll prove some invariants about this lambda calculus to prove that
our programs don't get *stuck*.
