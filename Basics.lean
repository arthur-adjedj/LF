/-!
=========================================
Basics: Functional Programming in Lean
=========================================
-/

/-!
==================
Introduction
==================

  The functional style of programming is founded on simple, everyday
  mathematical intuition: If a procedure or method has no side
  effects, then (ignoring efficiency) all we need to understand
  about it is how it maps inputs to outputs -- that is, we can think
  of it as just a concrete method for computing a mathematical
  function.  This is one sense of the word "functional" in
  "functional programming."  The direct connection between programs
  and simple mathematical objects supports both formal correctness
  proofs and sound informal reasoning about program behavior.

  The other sense in which functional programming is "functional" is
  that it emphasizes the use of functions as `first-class` values --
  i.e., values that can be passed as arguments to other functions,
  returned as results, included in data structures, etc.  The
  recognition that functions can be treated as data gives rise to a
  host of useful and powerful programming idioms.

  Other common features of functional languages include `algebraic
  data types` and `pattern matching`, which make it easy to
  construct and manipulate rich data structures, and `polymorphic
  type systems` supporting abstraction and code reuse.  Lean offers
  all of these features.

  The first half of this chapter introduces the most essential
  elements of Lean's functional programming language.
  The second half introduces some basic *tactics* that
  can be used to prove properties of programs. -/

/-!================================================================= -/
/-!
==================
Data and Functions
==================

###################
Enumerated Types
###################

  While Lean provides a lot of types and features as part of its core.
  (including the usual palette of atomic data types like Booleans,
  integers, strings, etc.), Lean also offers a powerful mechanism
  for defining new data types from scratch.

  Naturally, the Lean distribution comes with an extensive standard
  library providing defs of Booleans, numbers, and many
  common data structures like lists and hash tables.  But there is
  nothing magic or primitive about these library defs.  To
  illustrate this, in this course we will explicitly recapitulate
  (almost) all the defs we need, rather than getting them
  from the standard library.

###################
Days of the Week
###################

  To see how this definition mechanism works, let's start with
  a very simple example. The following declaration tells Lean that
  we are defining a set of data values -- a *type*. -/

inductive Day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr
open Day
/-!
  The new type is called `Day`, and its members are `monday`,
  `tuesday`, etc.

  Pay no mind to the `deriving` and `open` commands for now.
  Having defined `Day`, we can write functions that operate on
  Days. -/

def next_weekday (d:Day) : Day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday

/-!
  One point to note is that the argument and return types of
  this function are explicitly declared.  Like most functional
  programming languages, Lean can often figure out these types for
  itself when they are not given explicitly -- i.e., it can do *type
  inference* -- but we'll generally include them to make reading
  easier. 

  Having defined a function, we should next check that it
  works on some examples.  There are actually three different ways
  to do the examples in Lean.  First, we can use the command
  `#eval` to evaluate a compound expression involving
  `next_weekday`. -/

#eval next_weekday friday
--monday : Day
/-!-/
#eval next_weekday (next_weekday saturday)
--tuesday : Day

/-!
  (We show Lean's responses in comments, but, if you have a
  computer handy, this would be an excellent moment to fire up the
  Lean interpreter under your favorite IDE -- either VSCode or Emacs
  -- and try it for yourself.  Load this file, `Basics.lean`,
  from the book's Lean sources, find the above example, submit it to
  Lean, and observe the result.)

  Second, we can record what we *expect* the result to be in the
  form of a Lean example: -/

theorem test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday := rfl

/-!
  This declaration does three things: it makes an
  assertion (that the second weekday after `saturday` is `tuesday`),
  and it gives the assertion a name that can be used to refer to it
  later.  Lastly, it verifies this assertion to be true thanks to `:= rfl`

  The details are not important just now, but essentially this
  can be read as "The assertion we've just made can be proved by
  observing that both sides of the equality evaluate to the same
  thing."

  Third, we can ask Lean to *compile* our `def` initions into
  executable code. This facility is very interesting, since
  it gives us a
  path from proved-correct algorithms written in Lean to
  efficient machine code.  (Of course, we are trusting the
  correctness of the Lean compiler, but this is still a big step forward
  from the way most software is developed today.) Indeed, this is
  one of the main uses for which Lean 4 was developed. We'll come back
  to this topic in later chapters. -/

/-!
###################
Booleans 
###################

  Following the pattern of the Days of the week above, we can
  define the standard type `Bool` of Booleans, with members `true`
  and `false`. Since Bool is already defined in the core language,
  this inductive definition is commented out, as it would otherwise
  give an error.

  .. code-block:: lean4

    inductive Bool : Type :=
      | true
      | false


  Functions over Booleans can be defined in the same way as
  above: -/

def negb (b: Bool) : Bool :=
  match b with
  | true => false
  | false => true

def andb (b1: Bool) (b2: Bool) : Bool :=
  match b1 with
  | true => b2
  | false => false

def orb (b1: Bool) (b2: Bool) : Bool :=
  match b1 with
  | true => true
  | false => b2

/-!
  (Although we are rolling our own Boolean functions here for the sake
  of building up everything from scratch, Lean does, of course,
  provide a multitude of useful functions and lemmas.
  
  The last two of these illustrate Lean's syntax for
  multi-argument function defs.  The corresponding
  multi-argument application syntax is illustrated by the following
  "unit tests," which constitute a complete specification -- a truth
  table -- for the `orb` function: -/

theorem test_orb1: (orb true  false) = true  := rfl
theorem test_orb2: (orb false false) = false := rfl
theorem test_orb3: (orb false true)  = true  := rfl
theorem test_orb4: (orb true  true)  = true  := rfl

/-!
  We can also introduce some familiar infix syntax for the
  Boolean operations we have just defined. The `notation` command
  defines a new symbolic notation for an existing def. -/

notation x "and" y => andb x y
notation x "||" y => orb x y

--Note : wrong associativity, it's parsed as `false || (false || (true = true))`
-- `(true = true)` is then coerced to `decide (true = true)`
theorem test_orb5: false || false || true = true := rfl

/-! A note on notation :

  In `.lean` files, we use apostrophes
  to delimit fragments of Lean code within comments; this convention,
  also used by the `coqdoc` documentation tool, keeps them visually
  separate from the surrounding text.  In the HTML version of the
  files, these pieces of text appear in a `different font`. 

  These examples are also an opportunity to introduce one more small
  feature of Lean's programming language: conditional expressions... -/

def negb' (b: Bool) : Bool :=
  if b then false
  else true

def andb' (b1: Bool) (b2: Bool) : Bool :=
  if b1 then b2
  else false

def orb' (b1: Bool) (b2: Bool) : Bool :=
  if b1 then true
  else b2

/-!
  Lean's conditionals are exactly like those found in any other
  language, with one small generalization.  Since the `Bool` type is
  not built in, Lean actually supports conditional expressions over
  *any* inductively defined type with exactly two clauses in its
  def.  The guard is considered true if it evaluates to the
  "constructor" of the first clause of the `inductive`
  def (which just happens to be called `true` in this case)
  and false if it evaluates to the second. -/

/-!
**********************************
Exercise: 1 star, standard (nandb)
**********************************

  The command `sorry` can be used as a placeholder for an
  incomplete proof or definition. We use it in exercises to
  indicate the parts that we're leaving for you
  -- i.e., your job is to replace `sorry` s with real proofs.

  Remove `sorry` and complete the def of the following
  function; then make sure that the `theorem` assertions below can
  each be verified by Lean. (I.e., fill in each proof, following the
  model of the `orb` tests above, and make sure Lean accepts it.) The
  function should return `true` if either or both of its inputs are
  `false`.

  Hint: if `rfl` will not close the goal in your proof, it's
  probably because you defined `nandb` without using a `match`
  expression. Try a different def of `nandb` and go directly to `rfl`. We'll
  explain this phenomenon later in the chapter. -/

def nandb (b1: Bool) (b2: Bool) : Bool := sorry
/-!-/
theorem test_nandb1: (nandb true false)  = true  := sorry
theorem test_nandb2: (nandb false false) = true  := sorry
theorem test_nandb3: (nandb false true)  = true  := sorry
theorem test_nandb4: (nandb true true)   = false := sorry

/-!
**********************************
Exercise: 1 star, standard (andb3)
**********************************

  Do the same for the `andb3` function below. This function should
  return `true` when all of its inputs are `true`, and `false`
  otherwise. -/

def andb3 (b1: Bool) (b2: Bool) (b3: Bool) : Bool := sorry
/-!-/
theorem test_andb31: (andb3 true true true)  = true := sorry
theorem test_andb32: (andb3 false true true) = false := sorry
theorem test_andb33: (andb3 true false true) = false := sorry
theorem test_andb34: (andb3 true true false) = false := sorry

/-!================================================================= -/
/-!
#######
Types
#######

  Every expression in Lean has a type, describing what sort of
  thing it computes. The `#check` command asks Lean to print the type
  of an expression. -/

#check true -- true : Bool

/-!
  If the expression after `#check` is followed by a colon and a type,
  Lean will verify that the type of the expression matches the given
  type and halt with an error if not. -/

#check (true: Bool)
#check (negb true: Bool)

/-!
  Functions like `negb` itself are also data values, just like
  `true` and `false`.  Their types are called *function types*, and
  they are written with arrows. -/

#check (negb: Bool -> Bool)

/-!
  The type of `negb`, written `Bool -> Bool` and pronounced
  "`Bool` arrow `Bool`," can be read, "Given an input of type
  `Bool`, this function produces an output of type `Bool`."
  Similarly, the type of `andb`, written `Bool -> Bool -> Bool`, can
  be read, "Given two inputs, each of type `Bool`, this function
  produces an output of type `Bool`." -/

/-!
##################
New Types from Old
##################-/

/-!
  The types we have defined so far are examples of "enumerated
  types": their defs explicitly enumerate a finite set of
  elements, called *constructors*.  Here is a more interesting type
  def, where one of the constructors takes an argument: -/

inductive Rgb : Type :=
  | red
  | green
  | blue
open Rgb

inductive Color : Type :=
  | black
  | white
  | primary (p : Rgb)
open Color
/-!
  Let's look at this in a little more detail.

  An `inductive` def does two things:

  - It defines a set of new *constructors*. E.g., `red`,
    `primary`, `true`, `false`, `monday`, etc. are constructors.
  - It groups them into a new named type, like `Bool`, `Rgb`, or
    `Color`.

  `Constructor expressions` are formed by applying a constructor
  to zero or more other constructors or constructor expressions,
  obeying the declared number and types of the constructor arguments.
  E.g.,

  - `red`
  - `true`
  - `primary red`
  - etc.

  But not:

  - `red primary`
  - `true red`
  - `primary (primary red)`
  - etc.
-/

/-!
  In particular, the defs of `Rgb` and `Color` say
  which constructor expressions belong to the sets `Rgb` and
  `Color`:

  - `red`, `green`, and `blue` belong to the set `Rgb`;
  - `black` and `white` belong to the set `Color`;
  - if `p` is a constructor expression belonging to the set `Rgb`,
    then `primary p` (pronounced "the constructor `primary` applied
    to the argument `p`") is a constructor expression belonging to
    the set `Color`; and
  - constructor expressions formed in these ways are the *only* ones
    belonging to the sets `Rgb` and `Color`.
    
  We can define functions on colors using pattern matching just as
  we did for `day` and `Bool`. -/

def monochrome (c : Color) : Bool :=
  match c with
  | black => true
  | white => true
  | primary p => false

/-!
  Since the `primary` constructor takes an argument, a pattern
  matching `primary` should include either a variable (as above --
  note that we can choose its name freely) or a constant of
  appropriate type (as below). -/

def isred (c : Color) : Bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false

/-!
  The pattern "`primary _`" here is shorthand for "the constructor
  `primary` applied to any `Rgb` constructor except `red`."  (The
  wildcard pattern `_` has the same effect as the dummy pattern
  variable `p` in the def of `monochrome`.) -/

/-!
#######
Modules
####### 

  Lean provides a `namespace system` to aid in organizing large
  developments.  We won't need most of its features,
  but one is useful: If we enclose a collection of declarations
  between `namespace X` and `end X` markers, then, in the remainder of
  the file after the `end`, these defs are referred to by
  names like `X.foo` instead of just `foo`.  We will use this
  feature to limit the scope of defs, so that we are free to
  reuse names. -/

namespace Playground
  def myblue : Rgb := blue
end Playground
/-!-/
def myblue : Bool := true
/-!-/
#check (Playground.myblue : Rgb)
#check (myblue : Bool)

/-!
  As you might have seen until now, every declaration of a new type using the `inductive`
  command was followed up by an `open` command making reference to the type above it.
  `open Foo` allows you to be able to write `foo` instead of `X.foo` once outside of
  the scope of the namespace. When defining constructors for an inductive type, Lean puts
  its constructors inside the type's namespace, which means that for i.e `Rgb`, you'd
  need to write `Rgb.red` instead of `red` everywhere, including when doing pattern-matches.
  opening the types' namespaces allows us to avoid this.
 -/

namespace Playground2
  def myred : Rgb := red
end Playground2
/-!-/
open Playground2
/-!-/

#check (myred : Rgb)
/-!-/

/-!
#######
Tuples
####### 

  A single constructor with multiple parameters can be used
  to create a tuple type. As an example, consider representing
  the four bits in a nybble (half a byte). We first define
  a datatype `bit` that resembles `Bool` (using the
  constructors `B0` and `B1` for the two possible bit values)
  and then define the datatype `nybble`, which is essentially
  a tuple of four bits. -/
namespace TuplePlayground
/-!-/
inductive Bit : Type :=
  | B0
  | B1
open Bit
/-!-/
inductive Nybble : Type :=
  | bits (b0 b1 b2 b3 : Bit)
open Nybble
/-!-/
#check (bits B1 B0 B1 B0: Nybble)

/-!
  The `bits` constructor acts as a wrapper for its contents.
  Unwrapping can be done by pattern-matching, as in the `all_zero`
  function which tests a nybble to see if all its bits are `B0`.  We
  use underscore (_) as a `wildcard pattern` to avoid inventing
  variable names that will not be used. -/

def all_zero (nb : Nybble) : Bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
/-!-/
#eval (all_zero (bits B1 B0 B1 B0)) --false : Bool
/-!-/
#eval (all_zero (bits B0 B0 B0 B0)) --true : Bool
/-!-/
end TuplePlayground

/-!
#######
Numbers
####### -/

/-!
  We put this section in a module so that our own def of
  Natural numbers does not interfere with the one from the
  standard library.  In the rest of the book, we'll want to use
  the standard library's. -/

namespace NatPlayground

/-!
  All the types we have defined so far -- both "enumerated
  types" such as `day`, `Bool`, and `bit` and tuple types such as
  `nybble` built from them -- are finite.  The Natural numbers, on
  the other hand, are an infinite set, so we'll need to use a
  slightly richer form of type declaration to represent them.

  There are many representations of numbers to choose from. We are
  most familiar with decimal notation (base 10), using the digits 0
  through 9, for example, to form the number 123.  You may have
  encountered hexadecimal notation (base 16), in which the same
  number is represented as 7B, or octal (base 8), where it is 173,
  or binary (base 2), where it is 1111011. Using an enumerated type
  to represent digits, we could use any of these as our
  representation Natural numbers. Indeed, there are circumstances
  where each of these choices would be useful.

  The binary representation is valuable in computer hardware because
  the digits can be represented with just two distinct voltage
  levels, resulting in simple circuitry. Analogously, we wish here
  to choose a representation that makes *proofs* simpler.

  In fact, there is a representation of numbers that is even simpler
  than binary, namely unary (base 1), in which only a single digit
  is used (as our ancient forebears might have done to count Days by
  making scratches on the walls of their caves). To represent unary
  numbers with a Lean datatype, we use two constructors. The
  `zero` constructor represents zero. When the `succ`
  constructor is applied to the representation of the Natural number
  n, the result is the representation of n+1, where `succ` stands for
  "successor" (or "scratch").  Here is the complete datatype
  def. -/

inductive Nat : Type :=
  | zero
  | succ (n : Nat)
open Nat
/-!
  With this def, 0 is represented by `zero`, 1 by `succ zero`,
  2 by `succ (succ zero)`, and so on.
  
  Informally, the clauses of the def can be read:

    - `zero` is a Natural number.
    - `succ` can be put in front of a Natural number to yield another
      one -- if `n` is a Natural number, then `succ n` is too. 
  
  Again, let's look at this in a little more detail.  The def
  of `Nat` says how expressions in the set `Nat` can be built:

    - the constructor expression `zero` belongs to the set `Nat`;
    - if `n` is a constructor expression belonging to the set `Nat`,
      then `succ n` is also a constructor expression belonging to the set
      `Nat`; and
    - constructor expressions formed in these two ways are the only
      ones belonging to the set `Nat`.
      
  These conditions are the precise force of the `inductive`
  declaration.  They imply that the constructor expression `zero`, the
  constructor expression `succ zero`, the constructor expression `succ (succ
  zero)`, the constructor expression `succ (succ (succ zero))`, and so on all
  belong to the set `Nat`, while other constructor expressions, like
  `true`, `andb true false`, `succ (succ false)`, and `zero (zero (zero succ))` do
  not.

  A critical point here is that what we've done so far is just to
  define a *representation* of numbers: a way of writing them down.
  The names `zero` and `succ` are arbitrary, and at this point they have
  no special meaning -- they are just two different marks that we
  can use to write down numbers (together with a rule that says any
  `Nat` will be written as some string of `succ` marks followed by an
  `zero`).  If we like, we can write essentially the same def
  this way: -/

inductive Nat' : Type :=
  | stop
  | tick (foo : Nat')
open Nat'
/-!
  The *interpretation* of these marks comes from how we use them to
  compute.
  
  We can do this by writing functions that pattern match on
  representations of Natural numbers just as we did above with
  Booleans and Days -- for example, here is the predecessor
  function: -/

def pred (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ n' => n'

/-!
  The second branch can be read: "if `n` has the form `succ n'`
  for some `n'`, then return `n'`." 
    
  The following `end` command closes the current module, so
  `Nat` will refer back to the type from the standard library. -/

end NatPlayground

open Nat
/-!
  Because Natural numbers are such a pervasive form of data,
  Lean provides a tiny bit of built-in magic for parsing and printing
  them: ordinary decimal numerals can be used as an alterNative to
  the "unary" notation defined by the constructors `succ` and `zero`.  Lean
  prints numbers in decimal form by default: -/

#check (succ (succ (succ (succ zero)))) --4 : Nat

def minustwo (n : Nat) : Nat :=
  match n with
  | zero => zero
  | succ zero => zero
  | succ (succ n') => n'

#eval (minustwo 4) --2 : Nat

/-!

  The constructor `succ` has the type `Nat -> Nat`, just like functions
  such as `pred` and `minustwo`: 
  -/

#check (succ : Nat -> Nat)
#check (pred : Nat -> Nat)
#check (minustwo : Nat -> Nat)

/-!

  These are all things that can be applied to a number to yield a
  number.  However, there is a fundamental difference between `succ`
  and the other two: functions like `pred` and `minustwo` are
  defined by giving `computation rules`  -- e.g., the def of
  `pred` says that `pred 2` can be simplified to `1` -- while the
  def of `succ` has no such behavior attached. Although it is *like* 
  a function in the sense that it can be applied to an
  argument, it does not *do* anything at all!  It is just a way of
  writing down numbers.

  (Think about standard decimal numerals: the numeral `1` is not a
  computation; it's a piece of data.  When we write `111` to mean
  the number one hundred and eleven, we are using `1`, three times,
  to write down a concrete representation of a number.)

  Now let's go on and define some more functions over numbers.

  For most interesting computations involving numbers, simple
  pattern matching is not enough: we also need recursion.  For
  example, to check that a number `n` is even, we may need to
  recursively check whether `n-2` is even. -/

def even (n:Nat) : Bool :=
  match n with
  | 0      => true
  | 1      => false
  | n'+2   => even n'

/-!
  We could define `odd` by a similar `def` declaration, but
  here is a simpler way: -/

def odd (n:Nat) : Bool :=
  negb (even n)

theorem test_odd1: odd 1 = true := rfl
theorem test_odd2: odd 4 = false := rfl

/-!
  Naturally, we can also define multi-argument functions by
  recursion.
-/

namespace NatPlayground2

def plus (n : Nat) (m : Nat) : Nat :=
  match m with
  | 0 => n
  | succ m' => succ (plus n m')

/-!
  Adding three to two now gives us five, as we'd expect.
-/

#eval (plus 3 2) --5 : Nat

/-!
  The steps of simplification that Lean performs can be
  visualized as follows: 
-/

/-!     `plus 3 2`
   i.e. 

    `plus (succ (succ (succ zero))) (succ (succ zero))`
    ==> `succ (plus (succ (succ zero)) (succ (succ zero)))`
          by the second clause of the `match`

    ==> `succ (succ (plus (succ zero) (succ (succ zero))))`
          by the second clause of the `match`
    ==> `succ (succ (succ (plus zero (succ (succ zero)))))`
          by the second clause of the `match`
    ==> `succ (succ (succ (succ (succ zero))))`
          by the first clause of the `match`
   i.e. `5`  -/

/-!
  As a notational convenience, if two or more arguments have
  the same type, they can be written together.  In the following
  def, `(n m : Nat)` means just the same as if we had written
  `(n : Nat) (m : Nat)`. -/

def mult (n m : Nat) : Nat :=
  match m with
  | 0 => 0
  | succ m' => plus n (mult n m')

theorem test_mult1: (mult 3 3) = 9 := rfl

/-!
  You can match two expressions at once by putting a comma
  between them: -/

def minus (n m:Nat) : Nat :=
  match n, m with
  | 0   , _    => 0
  | succ _ , 0    => n
  | succ n', succ m' => minus n' m'


def exp (base power : Nat) : Nat :=
  match power with
  | 0 => succ 0
  | succ p => mult base (exp base p)


/-!** Exercise: 1 star, standard (factorial)

    Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Lean.
 -/

def factorial (n:Nat) : Nat := sorry

theorem test_factorial1: factorial 3 = 6 := sorry
theorem test_factorial2: factorial 5 = mult 10 12 := sorry
/-![] -/

/-!Again, we can make numerical expressions easier to read and write
    by introducing notations for addition, multiplication, and
    subtraction. The following notations are commented out since
    they're already part of lean's syntax.-/

/-
infixl:50 "+" => plus
infixl:50 "-" => minus
infixl:40 "*" => mult
-/

#check ((0 + 1) + 1 : Nat)

/-!(The `infixl` command and `:50`
    control how these notations are treated by Lean's parser.  The
    details are not important for present purposes, but interested
    readers can refer to the "More on notations" section at the end of
    this chapter.)

    Note that these declarations do not change the defs we've
    already made: they are simply instructions to the Lean parser to
    accept `x + y` in place of `plus x y` and, conversely, to the Lean
    pretty-printer to display `plus x y` as `x + y`. -/

/-!While Lean does come with many built-in operations like equality, it
    is worthy to note that they can be user-defined operation!
    Here is a function `eqb`, which tests Natural numbers for
    `eq`uality, yielding a `b`oolean.  Note the use of nested
    `match`es (we could also have used a simultaneous match, as we did
    in `minus`.) -/

def eqb (n m : Nat) : Bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | succ _ => false
  | succ n' => match m with
            | 0 => false
            | succ m' => eqb n' m'

/-!Similarly, the `leb` function tests whether its first argument is
    less than or equal to its second argument, yielding a Boolean. -/

def leb (n m : Nat) : Bool :=
  match n with
  | 0 => true
  | succ n' =>
      match m with
      | 0 => false
      | succ m' => leb n' m'

theorem test_leb1: leb 2 2 = true  := rfl
theorem test_leb2: leb 2 4 = true  := rfl
theorem test_leb3: leb 4 2 = false := rfl

/-!We'll be using these (especially `eqb`) a lot, so let's give
    them infix notations. -/

notation:51 x "=?"  y:51  => eqb x y
notation:51 x "<=?" y:51 => leb x y

theorem test_leb3': 4 <=? 2 = false := rfl

/-!We now have two symbols that look like equality: `=` and
    `=?`.  We'll have much more to say about the differences and
    similarities between them later. For now, the main thing to notice
    is that `x = y` is a logical *claim* -- a "proposition" -- that we
    can try to prove, while `x =? y` is an *expression* whose
    value (either `true` or `false`) we can compute. -/

/-!** Exercise: 1 star, standard (ltb)

    The `ltb` function tests Natural numbers for `l`ess-`t`han,
    yielding a `b`oolean.  Instead of making up a new `Fixpoint` for
    this one, define it in terms of a previously defined
    function.  (It can be done with just one previously defined
    function, but you can use two if you want.) -/

def ltb (n m : Nat) : Bool := sorry

notation:51 x "<?" y:51 => ltb x y

theorem test_ltb1: ltb 2 2 = false := sorry
theorem test_ltb2: ltb 2 4 = true  := sorry
theorem test_ltb3: ltb 4 2 = false := sorry
/-![] -/

/-!################################################################# -/
/-!* Proof by Reflection -/

/-!Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each `theorem` in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.  The proofs of these claims
    were always the same: use `rfl` to check that both sides contain
    identical values.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    `0` is a "neutral element" for `+` on the right can be proved just
    by observing that `n + 0` reduces to `n` no matter what `n` is -- a
    fact that can be read directly off the def of `plus`. -/

theorem plus_O_n : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

/-! `rfl` tries "unfolding" defined terms, replacing them with their
    right-hand sides. If rfl succeeds, the whole goal is finished and
    we don't need to look at whatever expanded expressions `rfl` has created
    by all this simplification and unfolding

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler theorems we saw earlier; there is
    just one difference.

    We've added the quantifier `∀ n:Nat`, so that our
    theorem talks about *all* Natural numbers `n`.  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    `n` is some number..."  Formally, this is achieved in the proof by
    `intros n`, which moves `n` from the quantifier in the goal to a
    *context* of current assumptions. Note that we could have used
    another identifier instead of `n` in the `intros` clause, (though
    of course this might be confusing to human readers of the proof): -/

/-!The keywords `intros` and `rfl` are examples of
    *tactics*. A tactic is a command that is introduced by the `by` keyword
    to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    many more in future chapters. -/

/-!Other similar theorems can be proved with the same pattern. -/

theorem plus_1_r : ∀ n: Nat, n + 1 = succ n := by
  intro n
  rfl

theorem mult_0_r : ∀ n: Nat, n * 0 = 0 := by
  intro n
  rfl

/-!The `_r` suffix in the names of these theorems is
    pronounced "on the right." -/

/-!It is worth stepping through these proofs to observe how the
    context and the goal change. -/

/-!################################################################# -/
/-!* Proof by Rewriting -/

/-!The following theorem is a bit more interesting than the
    ones we've seen: -/

theorem plus_id_example : ∀ n m: Nat,
  n = m ->
  n + n = m + m := by
/-Instead of making a universal claim about all numbers `n` and `m`,
    it talks about a more specialized property that only holds when
    `n = m`.  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming we are given such
    numbers `n` and `m`.  We also need to assume the hypothesis
    `n = m`. The `intro` tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since `n` and `m` are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming `n = m`, then we can replace
    `n` with `m` in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Lean to
    perform this replacement is called `rewrite`. -/

  intro n m
  /-move the hypothesis into the context: -/
  intro H
  /-rewrite the goal using the hypothesis: -/
  rewrite [H]
  rfl

/-!The first line of the proof moves the universally quantified
    variables `n` and `m` into the context.  The second moves the
    hypothesis `n = m` into the context and gives it the name `H`.
    The third tells Lean to rewrite the current goal (`n + n = m + m`)
    by replacing the left side of the equality hypothesis `H` with the
    right side.

    (note that `H` is enclosed in brackets. This is because `rewrite` is meant
    to be used to do multiple rewrites in a single tactic call. As such, all the
    hypothesises you want to use to rewrite your goal can be written as
    `rewrite [H1, H2, ..., Hn]`. Furthermore, when using `H : foo = bar`,
    `rewrite` will try to replace all instances of `foo` with `bar`.
    you can also ask the tactic to replace `bar` with `foo` instead, by writing
    `<-H` instead of `H`. You can try to do so in the previous example, and see
    what it does.) -/

/-!** Exercise: 1 star, standard (plus_id_exercise)

    Remove "`sorry.`" and fill in the proof. -/

theorem plus_id_exercise : ∀ n m o : Nat,
  n = m -> m = o -> n + m = m + o := by
  /-FILL IN HERE -/
  sorry
/-![] -/

/-!The `sorry` command tells Lean that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use `sorry` to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say `sorry` you
    are leaving a door open for total nonsense to enter Lean's nice,
    rigorous, formally checked world! -/

/-!The `#check` command can also be used to examine the statements of
    previously declared lemmas and theorems.  The two examples below
    are lemmas about multiplication that are proved in the standard
    library.  (We will see how to prove them ourselves in the next
    chapter.) -/

#check Nat.mul_zero
/-!===> ∀ (n : Nat), n * 0 = 0 -/

#check Nat.mul_succ
/-!===> ∀ (n m : Nat), n * succ m = n * m + n -/

/-!We can use the `rewrite` tactic with a previously proved theorem
    instead of a hypothesis from the context. If the statement of the
    previously proved theorem involves quantified variables, as in the
    example below, Lean tries to instantiate them by matching with the
    current goal. -/

theorem mult_n_0_m_0 : ∀ p q : Nat,
  (p * 0) + (q * 0) = 0 := by
  intros p q
  rewrite [Nat.mul_zero]
  rewrite [Nat.mul_zero]
  rfl

/-!** Exercise: 1 star, standard (mult_n_1)

    Use those two lemmas about multiplication that we just checked to
    prove the following theorem.  Hint: recall that `1` is `succ zero`. -/

theorem mult_n_1 : ∀ p : Nat,
  p * 1 = p := by
  /-FILL IN HERE -/
  sorry

/-![] -/

/-!################################################################# -/
/-!* Proof by Case Analysis -/

/-!Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, Booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the `simpl` tactic as above, we get stuck.  (We then
    use the `Abort` command to give up on it for the moment.)-/

theorem plus_1_neq_0_firsttry : ∀ n : Nat,
  ((1+ n) =? 0) = false := by
  intro n
  try rfl --Doesn't work !
  sorry

/-!The reason for this is that the defs of both `eqb`
    and `+` begin by performing a `match` on their first argument.
    But here, the first argument to `+` is the unknown number `n` and
    the argument to `eqb` is the compound expression `n + 1`; neither
    can be simplified.

    To make progress, we need to consider the possible forms of `n`
    separately.  If `n` is `O`, then we can calculate the final result
    of `(n + 1) =? 0` and check that it is, indeed, `false`.  And if
    `n = S n'` for some `n'`, then, although we don't know exactly
    what number `n + 1` represents, we can calculate that, at least,
    it will begin with one `succ`, and this is enough to calculate that,
    again, `(n + 1) =? 0` will yield `false`.

    The tactic that tells Lean to consider, separately, the cases where
    `n = O` and where `n = succ n'` is called `cases`. -/

theorem plus_1_neq_0 : ∀ n : Nat,
  ((n + 1) =? 0) = false := by
  intros n
  cases n
  · rfl
  · rfl

/-!The `cases` generates *two* subgoals, which we must then
    prove, separately, in order to get Lean to accept the theorem.

    In each subgoal, Lean remembers the assumption about `n` that is
    relevant for this subgoal -- either `n = 0` or `n = succ n✝` for some
    n'.  Writing `cases H : n` tells `cases` to give the name `H`
    to this equation.

    The `·` signs on the second and third lines are called *bullets*,
    and they mark the parts of the proof that correspond to the two
    generated subgoals.  The part of the proof script that comes after
    a bullet is the entire proof for the corresponding subgoal.  In
    this example, each of the subgoals is easily proved by a single
    use of `rfl`, which itself performs some simplification --
    e.g., the second one simplifies `(succ n' + 1) =? 0` to `false` by
    first rewriting `(succ n' + 1)` to `succ (n' + 1)`, then unfolding
    `eqb`, and then simplifying the `match`.

    Marking cases with bullets is optional: if bullets are not
    present, Lean simply asks you to prove each subgoal in sequence,
    one at a time. But it is a good idea to use bullets.  For one
    thing, they make the structure of a proof apparent, improving
    readability. Also, bullets instruct Lean to ensure that a subgoal
    is complete before trying to verify the next one, preventing
    proofs for different subgoals from getting mixed up. These issues
    become especially important in large developments, where fragile
    proofs lead to long debugging sessions.

    When using tactics, Lean might need to generate new variables on the fly,
    such as the `n✝` seen in the previous proof. By default, these variable are
    said to be innacessible, in the sense that the user cannot write and
    make use of them by calling them by their name. The goal of this is to encourage
    the user to name every introduced variable he might need. How one does so will
    depend on the tactic he's currently using. In the case of `cases`, you can write
    `cases n with

      | zero => rfl
      | succ n' => rfl`

    instead of
    `cases n

      · rfl
      · rfl
    `

    The syntax is very similar to the usual way you might do pattern-matching.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Lean users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on a single line.  Good style lies
    somewhere in the middle.  One reasonable guideline is to limit
    yourself to 80-character lines.

    The `cases` tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that Boolean
    negation is involutive -- i.e., that negation is its own
    inverse. -/

theorem negb_involutive : ∀ b : Bool,
  negb (negb b) = b := by
  intros b
  cases b
  · rfl
  · rfl

/-!Note that the `cases` here has no `as` clause because
    none of the subcases of the `cases` need to bind any variables,
    so there is no need to specify any names.  In fact, we can omit
    the `as` clause from *any* `cases` and Lean will fill in
    variable names automatically.  This is generally considered bad
    style, since Lean often makes confusing choices of names when left
    to its own devices.

    It is sometimes useful to invoke `cases` inside a subgoal,
    generating yet more proof obligations. In this case, we can use bullets
    again, indented one more time to keep the "tree-like" structure of the proof
    in place.
    For example: -/

theorem andb_commutative : ∀ b c, andb b c = andb c b := by
  intro b c
  cases b
  · cases c
    · rfl
    · rfl
  · cases c
    · rfl
    · rfl


/-!Each pair of calls to `rfl` corresponds to the
    subgoals that were generated after the execution of the `cases c`
    line right above it. -/

/-!Besides `·`, we can also enclose sub-proofs in curly braces: -/

theorem andb_commutative' : ∀ b c, andb b c = andb c b := by
  intro b c
  cases b
  { cases c
    { rfl }
    { rfl } }
  { cases c
    { rfl }
    { rfl } }

/-!Since curly braces mark both the beginning and the end of a proof,
    they can be used for multiple subgoal levels, as this example
    shows. The choice of braces, bullets, or a combination of the
    two is purely a matter of taste. -/

theorem andb3_exchange :
  ∀ b c d, andb (andb b c) d = andb (andb b d) c := by
  intro b c d
  cases b
  · cases c
    { cases d
      · rfl
      · rfl }
    { cases d
      · rfl
      · rfl }
  · cases c
    { cases d
      · rfl
      · rfl }
    { cases d
      · rfl
      · rfl }

/-!** Exercise: 2 stars, standard (andb_true_elim2)

    Prove the following claim, marking cases (and subcases) with
    bullets when you use `cases`.

    Hint: You will eventually need to cases both Booleans, as in
    the theorems above. But, delay introducing the hypothesis until
    after you have an opportunity to simplify it.

    Hint 2: When you reach contradiction in the hypotheses, focus
    on how to `rewrite` with that contradiction. -/

theorem andb_true_elim2 : ∀ b c : Bool,
  andb b c = true -> c = true := by
  /-FILL IN HERE -/
  sorry
/-![] -/

/-!** Exercise: 1 star, standard (zero_nbeq_plus_1) -/
theorem zero_nbeq_plus_1 : ∀ n : Nat,
  (0 =? (n + 1)) = false := by
  /-FILL IN HERE -/
  sorry
/-![] -/

/-!================================================================= -/
/-!* More on Notation (Optional) -/

/-!(In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation defs for infix plus and times: -/

infixl:50 "+" => plus
infixl:40 "*" => mult

/-!For each notation symbol in Lean, we can specify its precedence
    level and its associativity.  The precedence level `n` is
    specified by writing `:n` after naming the command; this helps Lean parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for `+` and
    `*` say that the expression `1+2*3*4` is shorthand for
    `(1+((2*3)*4))`. Lean uses precedence levels from 0 to 1024, and
    *left* (`infixl`), *right* (`infixr`), or *no* (`notation`) associativity.
    We will see more examples of this later, e.g., in the `Lists`
    chapter. -/

/-!================================================================= -/
/-!* Fixpoints and Structural Recursion (Optional) -/

/-!Here is a copy of the def of addition: -/

def plus' (n : Nat) (m : Nat) : Nat :=
  match n with
  | 0 => m
  | succ n' => succ (plus' n' m)

/-!When Lean checks this def, it notes that `plus'` is
    "decreasing on 1st argument."  What this means is that we are
    performing a *structural recursion* over the argument `n` -- i.e.,
    that we make recursive calls only on strictly smaller values of
    `n`.  This implies that all calls to `plus'` will eventually
    termiNate.  Lean demands that some argument of *every* `def`
    def is "decreasing."

    This requirement is a fundamental feature of Lean's design: In
    particular, it guarantees that every function that can be defined
    in Lean will terminate on all inputs.  However, because Lean's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. -/

/-!** Exercise: 2 stars, standard, optional (decreasing)

    To get a concrete sense of this, find a way to write a sensible
    `def` def (of a simple function on numbers, say) that
    *does* terminate on all inputs, but that Lean will reject because
    of this restriction.  (If you choose to turn in this optional
    exercise as part of a homework assignment, make sure you comment
    out your solution so that it doesn't cause Lean to reject the whole
    file!) -/

/-!FILL IN HERE

    [] -/

/-!################################################################# -/
/-!* More Exercises -/

/-!================================================================= -/
/-!* Warmups -/

/-!** Exercise: 1 star, standard (identity_fn_applied_twice)

    Use the tactics you have learned so far to prove the following
    theorem about Boolean functions. -/

theorem identity_fn_applied_twice :
  ∀ (f : Bool -> Bool),
  (∀ (x : Bool), f x = x) ->
  ∀ (b : Bool), f (f b) = b := by
  /-FILL IN HERE -/
  sorry

/-![] -/

/-!** Exercise: 1 star, standard (negation_fn_applied_twice)

    Now state and prove a theorem `negation_fn_applied_twice` similar
    to the previous one but where the second hypothesis says that the
    function `f` has the property that `f x = negb x`. -/

/-!FILL IN HERE -/

/-!Do not modify the following line: -/
def manual_grade_for_negation_fn_applied_twice : Option (Nat × string) := none
/-!(The last def is used by the autograder.)

    [] -/

/-!** Exercise: 3 stars, standard, optional (andb_eq_orb)

    Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    `cases` and `rewrite`, but casesing everything in sight is
    not the best way.) -/

theorem andb_eq_orb :
  ∀ (b c : Bool),
  (andb b c = orb b c) ->
  b = c := by
  /-FILL IN HERE -/
  sorry

/-![] -/

/-!================================================================= -/
/-!* Course Late Policies Formalized -/

/-!Suppose that a course has a grading policy based on late Days such
    that a student's final letter grade is lowered if they submit too
    many homework assignments late.

    In this series of problems, we model that situation using the
    features of Lean that we have seen so far and prove some basic
    facts about the grading policy.  -/

namespace LateDays

/-!First, we inroduce a datatype for modeling the "letter" component
    of a grade. -/
inductive Letter : Type :=
  | A | B | C | D | F
open Letter

/-!Then we define the modifiers -- a `Natural` `A` is just a "plain"
    grade of `A`. -/
inductive Modifier : Type :=
  | Plus | Natural | Minus
open Modifier

/-!A full `Grade`, then, is just a `Letter` and a `Modifier`.

    We might write, informally, "A-" for the Lean value `grade A Minus`,
    and similarly "C" for the Lean value `grade C Natural`. -/
inductive Grade : Type :=
  | grade (l:Letter) (m:Modifier)
open Grade
/-!We will want to be able to say when one grade is "better" than
    another.  In other words, we need a way to compare two grades.  As
    with Natural numbers, we could define `Bool`-valued functions
    `grade_eqb`, `grade_ltb`, etc., and that would work fine.
    However, we can also define a slightly more informative type for
    comparing two values, as shown below.  This datatype as three
    constructors that can be used to indicate whether two values are
    "equal", "less than", or "greater than" one another. (This
    def also appears in the Lean standard libary.)  -/

inductive Comparison : Type :=
  | eq : Comparison        /-"equal" -/
  | lt : Comparison        /-"less than" -/
  | gt : Comparison        /-"greater than" -/
deriving Repr
open Comparison

/-!Using pattern matching, it is not too difficult to define the
    comparison operation for two letters `l1` and `l2` (see below).
    This def uses two features of `match` patterns: First,
    recall that we can match against *two* values simultaneously by
    separating them and the corresponding patterns with comma `,`.
    This is simply a convenient abbreviation for nested pattern
    matching.  For example, the first two cases are just shorthand for
    the nested version shown on the right: -/

/-  match l1, l2 with          match l1 with
  | A, A => eq               | A => match l2 with
  | A, _ => gt                      | A => eq
                                    | _ => gt
-/

/-!As another shorthand, we can also match one of several
    possibilites by using `|` as short hand.  For example the pattern
    `| C, A | C, B)` stands for two cases: `C, A` and `C, B` and will
    match either possibility.  -/
def letter_comparison (l1 l2 : Letter) : Comparison :=
  match l1, l2 with
  | A, A => eq
  | A, _ => gt
  | B, A => lt
  | B, B => eq
  | B, _ => gt
  | C, A | C, B => lt
  | C, C => eq
  | C, _ => gt
  | D, A | D, B | D, C => lt
  | D, D => eq
  | D, _ => gt
  | F, A | F, B | F,C | F, D => lt
  | F, F => eq

/-!We can test the `letter_comparison` operation by trying it out on a few
    examples. -/
#eval letter_comparison B A
/-!==> lt -/
#eval letter_comparison D D
/-!==> eq -/
#eval letter_comparison B F
/-!==> gt -/

/-!As a further sanity check, we can prove that the
    `letter_comparison` function does indeed give the result `eq` when
    comparing a letter `l` against itself.  -/
/-!** Exercise: 1 star, standard (letter_comparison)

    Prove the following theorem. -/

theorem letter_comparison_eq :
  ∀ l, letter_comparison l l = eq := by
  /-FILL IN HERE -/
  sorry

/-![] -/

/-!We can follow the same strategy to define the comparison operation
    for two grade modifiers.  We consider them to be ordered as
    `Plus > Natural > Minus`. -/
def modifier_comparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | Plus, Plus => eq
  | Plus, _ => gt
  | Natural, Plus => lt
  | Natural, Natural => eq
  | Natural, _ => gt
  | Minus, Plus | Minus, Natural => lt
  | Minus, Minus => eq

/-!** Exercise: 2 stars, standard (grade_comparison)

    Use pattern matching to complete the following def.  Note
    that the ordering on grades is sometimes called "lexicographic"
    ordering: we first compare the letters and, only in the case that
    the letters are equal do we need to consider the modifiers.
    (I.e. all grade variants of `A` are greater than all
    grade variants of `B`.)

    Hint: match against `g1` and `g2` simultaneously, but don't try to
    enumerate all the cases.  Instead do case analysis on the result
    of a suitable call to `letter_comparison` to end up with just `3`
    possibilities. -/

def grade_comparison (g1 g2 : Grade) : comparison
  /-REPLACE THIS LINE WITH ":= _your_def_ ." -/
  := sorry

/-!The following "unit tests" of your `grade_comparison` function
    should pass after you have defined it correctly. -/

theorem test_grade_comparison1 :
  (grade_comparison (grade A Minus) (grade B Plus)) = gt := by
  /-FILL IN HERE -/
  sorry

theorem test_grade_comparison2 :
  (grade_comparison (grade A Minus) (grade A Plus)) = lt := by
  /-FILL IN HERE -/
  sorry

theorem test_grade_comparison3 :
  (grade_comparison (grade F Plus) (grade F Plus)) = eq := by
  /-FILL IN HERE -/
  sorry

theorem test_grade_comparison4 :
  (grade_comparison (grade B Minus) (grade C Plus)) = gt := by
  /-FILL IN HERE -/
  sorry

/-![] -/

/-!Now that we have a def of grades and how they compare to
    one another, let us implement the late penalty fuction. -/

/-!First, we define what it means to lower the `Letter` component of
    a grade. Note that, since `F` is already the lowest grade
    possible, we just leave it untouched.  -/
def lower_letter (l : Letter) : Letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F  /-!Note that you can't go lower than `F` -/

/-!Already our formalization can help us understand some corner cases
    of the grading policy.  For example, we might expect that if we
    use the `lower_letter` function its result will actually be lower,
    as claimed in the following theorem.  But this theorem is not
    provable!  Why? -/
theorem lower_letter_lowers: ∀ (l : Letter),
  letter_comparison (lower_letter l) l = lt := by
  intros l
  cases l
  · rfl
  · rfl
  · rfl
  · rfl
  · sorry /-!We get stuck here. -/


/-!The problem, of course, has to do with the "edge case" of lowering
    `F`, as we can see like this: -/
theorem lower_letter_F_is_F:
  lower_letter F = F := by rfl

/-!Now we can state a better version of the lower letter theorem that
    actually is provable.  In this version, the hypothesis about `F`
    says that `F` is strictly smaller than `l`, which rules out the
    problematic case above. In other words, as long as `l` is bigger
    than `F`, it will be lowered. -/
/-!** Exercise: 2 stars, standard (lower_letter_lowers_fixed)

    Prove the following theorem. -/

theorem lower_letter_lowers_fixed:
  ∀ (l : Letter),
    letter_comparison F l = lt ->
    letter_comparison (lower_letter l) l = lt := by
  /-FILL IN HERE -/
  sorry

/-![] -/

/-!** Exercise: 2 stars, standard (lower_grade)

    We can now use the `lower_letter` def as a helper to define
    what it means to lower a grade by one step.  Implement the
    def below so that it sends a grade `g` to one step lower
    unless it is already `grade F Minus`, which should remain
    unchanged.  Once you have implemented this def correctly,
    the subsequent example "unit tests" should hold trivially.

    Hint: To make this a succinct def that is easy to prove
    properties about, you will probably want to use nested pattern
    matching. The outer match should not match on the specific letter
    component of the grade -- it should consider only the modifier.
    You should definitely *not* try to enumerate all of the
    cases. (Our solution is under 10 lines of code, total.) -/
def lower_grade (g : Grade) : Grade
  /-REPLACE THIS LINE WITH ":= _your_def_ ." -/
  := sorry

theorem lower_grade_A_Plus :
  lower_grade (grade A Plus) = (grade A Natural) := by
  /-FILL IN HERE -/
  sorry

theorem lower_grade_A_Natural :
  lower_grade (grade A Natural) = (grade A Minus) := by
  /-FILL IN HERE -/
  sorry

theorem lower_grade_A_Minus :
  lower_grade (grade A Minus) = (grade B Plus) := by
  /-FILL IN HERE -/
  sorry

theorem lower_grade_B_Plus :
  lower_grade (grade B Plus) = (grade B Natural) := by
  /-FILL IN HERE -/
  sorry

theorem lower_grade_F_Natural :
  lower_grade (grade F Natural) = (grade F Minus) := by
  /-FILL IN HERE -/
  sorry

theorem lower_grade_twice :
  lower_grade (lower_grade (grade B Minus)) = (grade C Natural) := by
  /-FILL IN HERE -/
  sorry

theorem lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (grade B Minus))) = (grade C Minus) := by
  /-FILL IN HERE -/
  sorry

theorem lower_grade_F_Minus : lower_grade (grade F Minus) = (grade F Minus) := by
  /-FILL IN HERE -/
  sorry

/-!GRADE_THEOREM 0.25: lower_grade_A_Plus -/
/-!GRADE_THEOREM 0.25: lower_grade_A_Natural -/
/-!GRADE_THEOREM 0.25: lower_grade_A_Minus -/
/-!GRADE_THEOREM 0.25: lower_grade_B_Plus -/
/-!GRADE_THEOREM 0.25: lower_grade_F_Natural -/
/-!GRADE_THEOREM 0.25: lower_grade_twice -/
/-!GRADE_THEOREM 0.25: lower_grade_thrice -/
/-!GRADE_THEOREM 0.25: lower_grade_F_Minus

    [] -/

/-!** Exercise: 3 stars, standard (lower_grade_lowers)

    Now prove the following theorem, which says that, as long as the
    grade starts out above F-, the `lower_grade` option does indeed
    lower the grade.  As usual, casesing everything in sight is
    *not* a good idea.  Judicious use of `cases`, along with
    rewriting is a better strategy.

    Hint: If you define your `grade_comparison` function as suggested,
    you will need to rewrite using `letter_comparison_eq` in two
    cases.  The remaining case is the only one in which you need to
    cases a `Letter`.  The case for `F` will probably benefit from
    `lower_grade_F_Minus`.  -/
theorem lower_grade_lowers :
  ∀ (g : Grade),
    grade_comparison (grade F Minus) g = lt ->
    grade_comparison (lower_grade g) g = lt := by
  /-FILL IN HERE -/
  sorry

/-![] -/

/-!Now that we have implemented and tested a function that lowers a
    grade by one step, we can implement a specific late Days policy.
    Given a number of `late_days`, the `apply_late_policy` function
    computes the final grade from `g`, the initial grade.

    This function encodes the following policy:

      # late Days     penalty
         0 - 8        no penalty
         9 - 16       lower grade by one step (A+ => A, A => A-, A- => B+, etc.)
        17 - 20       lower grade by two steps
          >= 21       lower grade by three steps (a whole letter)
-/
def apply_late_policy (late_days : Nat) (g : Grade) : Grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g))

/-!Sometimes it is useful to be able to "unfold" a def to be
    able to make progress on a proof.  Soon, we will see how to do this
    in a much simpler way automatically, but for now, it is easy to prove
    that a use of any def like `apply_late_policy` is equal to its
    right hand side. (It follows just from rfl.)

    This result is useful because it allows us to use `rewrite` to
    expose the internals of the def. -/
theorem apply_late_policy_unfold :
  ∀ (late_days : Nat) (g : Grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g  else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))) := by
  intro n g
  rfl

/-!Let's prove some properties about this policy... -/

/-!This theorem states that if a student accrues no more than 8 late
   Days throughout the semester, your grade is unaffected. It is
   easy to prove, once you use the `apply_late_policy_unfold`
   you can rewrite using the hypothesis. -/

/-!** Exercise: 2 stars, standard (no_penalty_for_mostly_on_time)

    Prove the following theorem. -/

theorem no_penalty_for_mostly_on_time :
  ∀ (late_days : Nat) (g : Grade),
    (late_days <? 9) = true ->
    apply_late_policy late_days g = g := by
  /-FILL IN HERE -/
  sorry

/-![] -/

/-!The following theorem proves that, as long as a student has
    between 9 and 16 late Days, their final grade is lowered by one
    step. -/

/-!** Exercise: 2 stars, standard (graded_lowered_once)

    Prove the following theorem. -/

theorem grade_lowered_once :
  ∀ (late_days : Nat) (g : Grade),
    (late_days <? 9) = false ->
    (late_days <? 17) = true ->
    (grade_comparison (grade F Minus) g = lt) ->
    (apply_late_policy late_days g) = (lower_grade g) := by
  /-FILL IN HERE -/
  sorry

/-![] -/
end LateDays

/-!================================================================= -/
/-!* Binary Numerals -/

/-!** Exercise: 3 stars, standard (binary)

    We can generalize our unary representation of Natural numbers to
    the more efficient binary representation by treating a binary
    number as a sequence of constructors `B0` and `B1` (representing 0s
    and 1s), termiNated by a `Z`. For comparison, in the unary
    representation, a number is a sequence of `S` constructors termiNated
    by an `O`.

    For example:

        decimal               binary                          unary
           0                       Z                              O
           1                    B1 Z                            S O
           2                B0 (B1 Z)                        S (S O)
           3                B1 (B1 Z)                     S (S (S O))
           4            B0 (B0 (B1 Z))                 S (S (S (S O)))
           5            B1 (B0 (B1 Z))              S (S (S (S (S O))))
           6            B0 (B1 (B1 Z))           S (S (S (S (S (S O)))))
           7            B1 (B1 (B1 Z))        S (S (S (S (S (S (S O))))))
           8        B0 (B0 (B0 (B1 Z)))    S (S (S (S (S (S (S (S O)))))))

    Note that the low-order bit is on the left and the high-order bit
    is on the right -- the opposite of the way binary numbers are
    usually written.  This choice makes them easier to manipulate. -/

inductive Bin : Type :=
  | Z
  | B0 (n : Bin)
  | B1 (n : Bin)
open Bin

/-!Complete the defs below of an increment function `incr`
    for binary numbers, and a function `bin_to_Nat` to convert
    binary numbers to unary numbers. -/

def incr (m:Bin) : Bin
  /-REPLACE THIS LINE WITH ":= _your_def_ ." -/
  := sorry

def bin_to_Nat (m:Bin) : Nat
  /-REPLACE THIS LINE WITH ":= _your_def_ ." -/
  := sorry

/-!The following "unit tests" of your increment and binary-to-unary
    functions should pass after you have defined those functions correctly.
    Of course, unit tests don't fully demonstrate the correctness of
    your functions!  We'll return to that thought at the end of the
    next chapter. -/

theorem test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z) := by
  /-FILL IN HERE -/
  sorry

theorem test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z) := by
  /-FILL IN HERE -/
  sorry

theorem test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)) := by
  /-FILL IN HERE -/
  sorry

theorem test_bin_incr4 : bin_to_Nat (B0 (B1 Z)) = 2 := by
  /-FILL IN HERE -/
  sorry

theorem test_bin_incr5 :
        bin_to_Nat (incr (B1 Z)) = 1 + bin_to_Nat (B1 Z) := by
  /-FILL IN HERE -/
  sorry

theorem test_bin_incr6 :
        bin_to_Nat (incr (incr (B1 Z))) = 2 + bin_to_Nat (B1 Z) := by
  /-FILL IN HERE -/
  sorry

/-![] -/