/- * Basics: Functional Programming in Lean -/

/- REMINDER:

          #####################################################
          ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
          #####################################################

   (See the [Preface] for why.)
-/

/- ################################################################# -/
/- * Introduction -/

/- The functional style of programming is founded on simple, everyday
    mathematical intuition: If a procedure or method has no side
    effects, then (ignoring efficiency) all we need to understand
    about it is how it maps inputs to outputs -- that is, we can think
    of it as just a concrete method for computing a mathematical
    function.  This is one sense of the word "functional" in
    "functional programming."  The direct connection between programs
    and simple mathematical objects supports both formal correctness
    proofs and sound informal reasoning about program behavior.

    The other sense in which functional programming is "functional" is
    that it emphasizes the use of functions as _first-class_ values --
    i.e., values that can be passed as arguments to other functions,
    returned as results, included in data structures, etc.  The
    recognition that functions can be treated as data gives rise to a
    host of useful and powerful programming idioms.

    Other common features of functional languages include _algebraic
    data types_ and _pattern matching_, which make it easy to
    construct and manipulate rich data structures, and _polymorphic
    type systems_ supporting abstraction and code reuse.  Lean offers
    all of these features.

    The first half of this chapter introduces the most essential
    elements of Lean's functional programming language.  
    The second half introduces some basic _tactics_ that
    can be used to prove properties of programs. -/

/- ################################################################# -/
/- * Data and Functions -/

/- ================================================================= -/
/- ** Enumerated Types -/

/-  While Lean provides a lot of types and features as part of its core.  
    (including the usual palette of atomic data types like Booleans, 
    integers, strings, etc.), Lean also offers a powerful mechanism 
    for defining new data types from scratch.

    Naturally, the Lean distribution comes with an extensive standard
    library providing defs of Booleans, numbers, and many
    common data structures like lists and hash tables.  But there is
    nothing magic or primitive about these library defs.  To
    illustrate this, in this course we will explicitly recapitulate
    (almost) all the defs we need, rather than getting them
    from the standard library. -/

/- ================================================================= -/
/- ** Days of the Week -/

/- To see how this definition mechanism works, let's start with
    a very simple example. The following declaration tells Lean that
    we are defining a set of data values -- a _type_. -/

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
/- The new type is called [Day], and its members are [monday],
    [tuesday], etc.
   
    Pay no mind to the [deriving] and [open] commands for now.
    Having defined [Day], we can write functions that operate on
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

/- One point to note is that the argument and return types of
    this function are explicitly declared.  Like most functional
    programming languages, Lean can often figure out these types for
    itself when they are not given explicitly -- i.e., it can do _type
    inference_ -- but we'll generally include them to make reading
    easier. -/

/- Having defined a function, we should next check that it
    works on some examples.  There are actually three different ways
    to do the examples in Lean.  First, we can use the command
    [#eval] to evaluate a compound expression involving
    [next_weekday]. -/

#eval next_weekday friday
/- ==> monday : Day -/

#eval next_weekday (next_weekday saturday)
/- ==> tuesday : Day -/

/- (We show Lean's responses in comments, but, if you have a
    computer handy, this would be an excellent moment to fire up the
    Lean interpreter under your favorite IDE -- either VSCode or Emacs
    -- and try it for yourself.  Load this file, [Basics.lean],
    from the book's Lean sources, find the above example, submit it to
    Lean, and observe the result.) -/

/- Second, we can record what we _expect_ the result to be in the
    form of a Lean example: -/

theorem test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday := rfl

/- This declaration does two things: it makes an
    assertion (that the second weekday after [saturday] is [tuesday]),
    and it gives the assertion a name that can be used to refer to it
    later.  Having made the assertion, we can also ask Lean to verify
    it like this: -/

/- The details are not important just now, but essentially this
    can be read as "The assertion we've just made can be proved by
    observing that both sides of the equality evaluate to the same
    thing."

    Third, we can ask Lean to _compile_ our [def]initions into 
    executable code. This facility is very interesting, since 
    it gives us a
    path from proved-correct algorithms written in Lean to
    efficient machine code.  (Of course, we are trusting the
    correctness of the Lean compiler, but this is still a big step forward
    from the way most software is developed today.) Indeed, this is
    one of the main uses for which Lean 4 was developed. We'll come back
    to this topic in later chapters. -/

/- ================================================================= -/
/- ** TODO AUTO GRADE ??? -/
/- ** Homework Submission Guidelines -/

/- ================================================================= -/
/- ** Booleans -/

/- Following the pattern of the Days of the week above, we can
    define the standard type [Bool] of Booleans, with members [true]
    and [false]. Since Bool is already defined in the core language, 
    this inductive definition is commented out, as it would otherwise 
    give an error.-/

/-inductive Bool : Type :=
  | true
  | false-/

/- Functions over Booleans can be defined in the same way as
    above: -/

def negb (b:Bool) : Bool :=
  match b with
  | true => false
  | false => true

def andb (b1:Bool) (b2:Bool) : Bool :=
  match b1 with
  | true => b2
  | false => false

def orb (b1:Bool) (b2:Bool) : Bool :=
  match b1 with
  | true => true
  | false => b2

/- (Although we are rolling our own Boolean functions here for the sake
    of building up everything from scratch, Lean does, of course,
    provide a multitude of useful functions and lemmas. -/

/- The last two of these illustrate Lean's syntax for
    multi-argument function defs.  The corresponding
    multi-argument application syntax is illustrated by the following
    "unit tests," which constitute a complete specification -- a truth
    table -- for the [orb] function: -/

theorem test_orb1: (orb true  false) = true  := rfl
theorem test_orb2: (orb false false) = false := rfl
theorem test_orb3: (orb false true)  = true  := rfl
theorem test_orb4: (orb true  true)  = true  := rfl

/- We can also introduce some familiar infix syntax for the
    Boolean operations we have just defined. The [notation] command
    defines a new symbolic notation for an existing def. -/

notation x "and" y => andb x y
notation x "||" y => orb x y

--Note : wrong associativity, it's parsed as `false || (false || (true = true))`
-- `(true = true)` is then coerced to `decide (true = true)`
theorem test_orb5: false || false || true = true := rfl

/- _A note on notation_: In [.lean] files, we use square brackets
    to delimit fragments of Lean code within comments; this convention,
    also used by the [coqdoc] documentation tool, keeps them visually
    separate from the surrounding text.  In the HTML version of the
    files, these pieces of text appear in a [different font]. -/

/- These examples are also an opportunity to introduce one more small
    feature of Lean's programming language: conditional expressions... -/

def negb' (b:Bool) : Bool :=
  if b then false
  else true

def andb' (b1:Bool) (b2:Bool) : Bool :=
  if b1 then b2
  else false

def orb' (b1:Bool) (b2:Bool) : Bool :=
  if b1 then true
  else b2

/- Lean's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the [Bool] type is
    not built in, Lean actually supports conditional expressions over
    _any_ inductively defined type with exactly two clauses in its
    def.  The guard is considered true if it evaluates to the
    "constructor" of the first clause of the [inductive]
    def (which just happens to be called [true] in this case)
    and false if it evaluates to the second. -/

/- **** Exercise: 1 star, standard (nandb)

    The command [sorry] can be used as a placeholder for an
    incomplete proof.  We use it in exercises to indicate the parts
    that we're leaving for you -- i.e., your job is to replace
    [sorry]s with real proofs.

    Remove "[sorry.]" and complete the def of the following
    function; then make sure that the [theorem] assertions below can
    each be verified by Lean.  (I.e., fill in each proof, following the
    model of the [orb] tests above, and make sure Lean accepts it.) The
    function should return [true] if either or both of its inputs are
    [false].

    Hint: if [simpl] will not simplify the goal in your proof, it's
    probably because you defined [nandb] without using a [match]
    expression. Try a different def of [nandb], or just
    skip over [simpl] and go directly to [rfl]. We'll
    explain this phenomenon later in the chapter. -/

def nandb (b1:Bool) (b2:Bool) : Bool := sorry

theorem test_nandb1: (nandb true false)  = true  := sorry
theorem test_nandb2: (nandb false false) = true  := sorry
theorem test_nandb3: (nandb false true)  = true  := sorry
theorem test_nandb4: (nandb true true)   = false := sorry
/- [] -/

/- **** Exercise: 1 star, standard (andb3)

    Do the same for the [andb3] function below. This function should
    return [true] when all of its inputs are [true], and [false]
    otherwise. -/

def andb3 (b1:Bool) (b2:Bool) (b3:Bool) : Bool := sorry

theorem test_andb31: (andb3 true true true)  = true := sorry
theorem test_andb32: (andb3 false true true) = false := sorry
theorem test_andb33: (andb3 true false true) = false := sorry
theorem test_andb34: (andb3 true true false) = false := sorry
/- [] -/

/- ================================================================= -/
/- ** Types -/

/- Every expression in Lean has a type, describing what sort of
    thing it computes. The [#check] command asks Lean to print the type
    of an expression. -/

#check true
/- ===> true : Bool -/

/- If the expression after [#check] is followed by a colon and a type,
    Lean will verify that the type of the expression matches the given
    type and halt with an error if not. -/

#check (true: Bool)
#check (negb true: Bool)
  

/- Functions like [negb] itself are also data values, just like
    [true] and [false].  Their types are called _function types_, and
    they are written with arrows. -/

#check (negb: Bool -> Bool)

/- The type of [negb], written [Bool -> Bool] and pronounced
    "[Bool] arrow [Bool]," can be read, "Given an input of type
    [Bool], this function produces an output of type [Bool]."
    Similarly, the type of [andb], written [Bool -> Bool -> Bool], can
    be read, "Given two inputs, each of type [Bool], this function
    produces an output of type [Bool]." -/

/- ================================================================= -/
/- ** New Types from Old -/

/- The types we have defined so far are examples of "enumerated
    types": their defs explicitly enumerate a finite set of
    elements, called _constructors_.  Here is a more interesting type
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
/- Let's look at this in a little more detail.

    An [inductive] def does two things:

    - It defines a set of new _constructors_. E.g., [red],
      [primary], [true], [false], [monday], etc. are constructors.

    - It groups them into a new named type, like [Bool], [rgb], or
      [color].

    _Constructor expressions_ are formed by applying a constructor
    to zero or more other constructors or constructor expressions,
    obeying the declared number and types of the constructor arguments.
    E.g.,
        - [red]
        - [true]
        - [primary red]
        - etc.
    But not
        - [red primary]
        - [true red]
        - [primary (primary red)]
        - etc.
-/

/- In particular, the defs of [rgb] and [color] say
    which constructor expressions belong to the sets [rgb] and
    [color]:

    - [red], [green], and [blue] belong to the set [rgb];
    - [black] and [white] belong to the set [color];
    - if [p] is a constructor expression belonging to the set [rgb],
      then [primary p] (pronounced "the constructor [primary] applied
      to the argument [p]") is a constructor expression belonging to
      the set [color]; and
    - constructor expressions formed in these ways are the _only_ ones
      belonging to the sets [rgb] and [color]. -/

/- We can define functions on colors using pattern matching just as
    we did for [day] and [Bool]. -/

def monochrome (c : Color) : Bool :=
  match c with
  | black => true
  | white => true
  | primary _ => false

/- Since the [primary] constructor takes an argument, a pattern
    matching [primary] should include either a variable (as above --
    note that we can choose its name freely) or a constant of
    appropriate type (as below). -/

def isred (c : Color) : Bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false

/- The pattern "[primary _]" here is shorthand for "the constructor
    [primary] applied to any [rgb] constructor except [red]."  (The
    wildcard pattern [_] has the same effect as the dummy pattern
    variable [p] in the def of [monochrome].) -/

/- ================================================================= -/
/- ** Modules -/

/- Lean provides a _module system_ to aid in organizing large
    developments.  We won't need most of its features,
    but one is useful: If we enclose a collection of declarations
    between [Module X] and [End X] markers, then, in the remainder of
    the file after the [End], these defs are referred to by
    names like [X.foo] instead of just [foo].  We will use this
    feature to limit the scope of defs, so that we are free to
    reuse names. -/

namespace Playground
  def myblue : Rgb := blue
end Playground

def myblue : Bool := true

#check (Playground.myblue : Rgb)
#check (myblue : Bool)

/- ================================================================= -/
/- ** Tuples -/

namespace TuplePlayground

/- A single constructor with multiple parameters can be used
    to create a tuple type. As an example, consider representing
    the four bits in a nybble (half a byte). We first define
    a datatype [bit] that resembles [Bool] (using the
    constructors [B0] and [B1] for the two possible bit values)
    and then define the datatype [nybble], which is essentially
    a tuple of four bits. -/

inductive Bit : Type :=
  | B0
  | B1
open Bit

inductive Nybble : Type :=
  | bits (b0 b1 b2 b3 : Bit)
open Nybble

#check (bits B1 B0 B1 B0: Nybble)
  
/- The [bits] constructor acts as a wrapper for its contents.
    Unwrapping can be done by pattern-matching, as in the [all_zero]
    function which tests a nybble to see if all its bits are [B0].  We
    use underscore (_) as a _wildcard pattern_ to avoid inventing
    variable names that will not be used. -/

def all_zero (nb : Nybble) : Bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false

#eval (all_zero (bits B1 B0 B1 B0))
/- ===> false : Bool -/
#eval (all_zero (bits B0 B0 B0 B0))
/- ===> true : Bool -/

end TuplePlayground

/- ================================================================= -/
/- ** Numbers -/

/- We put this section in a module so that our own def of
    Natural numbers does not interfere with the one from the
    standard library.  In the rest of the book, we'll want to use
    the standard library's. -/

namespace NatPlayground

/- All the types we have defined so far -- both "enumerated
    types" such as [day], [Bool], and [bit] and tuple types such as
    [nybble] built from them -- are finite.  The Natural numbers, on
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
    to choose a representation that makes _proofs_ simpler.

    In fact, there is a representation of numbers that is even simpler
    than binary, namely unary (base 1), in which only a single digit
    is used (as our ancient forebears might have done to count Days by
    making scratches on the walls of their caves). To represent unary
    numbers with a Lean datatype, we use two constructors. The
    capital-letter [O] constructor represents zero.  When the [S]
    constructor is applied to the representation of the Natural number
    n, the result is the representation of n+1, where [S] stands for
    "successor" (or "scratch").  Here is the complete datatype
    def. -/

inductive Nat : Type :=
  | O
  | S (n : Nat)
open Nat
/- With this def, 0 is represented by [O], 1 by [S O],
    2 by [S (S O)], and so on. -/

/- Informally, the clauses of the def can be read:
      - [O] is a Natural number (remember this is the letter "[O],"
        not the numeral "[0]").
      - [S] can be put in front of a Natural number to yield another
        one -- if [n] is a Natural number, then [S n] is too. -/

/- Again, let's look at this in a little more detail.  The def
    of [Nat] says how expressions in the set [Nat] can be built:

    - the constructor expression [O] belongs to the set [Nat];
    - if [n] is a constructor expression belonging to the set [Nat],
      then [S n] is also a constructor expression belonging to the set
      [Nat]; and
    - constructor expressions formed in these two ways are the only
      ones belonging to the set [Nat]. -/

/- These conditions are the precise force of the [inductive]
    declaration.  They imply that the constructor expression [O], the
    constructor expression [S O], the constructor expression [S (S
    O)], the constructor expression [S (S (S O))], and so on all
    belong to the set [Nat], while other constructor expressions, like
    [true], [andb true false], [S (S false)], and [O (O (O S))] do
    not.

    A critical point here is that what we've done so far is just to
    define a _representation_ of numbers: a way of writing them down.
    The names [O] and [S] are arbitrary, and at this point they have
    no special meaning -- they are just two different marks that we
    can use to write down numbers (together with a rule that says any
    [Nat] will be written as some string of [S] marks followed by an
    [O]).  If we like, we can write essentially the same def
    this way: -/

inductive Nat' : Type :=
  | stop
  | tick (foo : Nat')
open Nat'
/- The _interpretation_ of these marks comes from how we use them to
    compute. -/

/- We can do this by writing functions that pattern match on
    representations of Natural numbers just as we did above with
    Booleans and Days -- for example, here is the predecessor
    function: -/

def pred (n : Nat) : Nat :=
  match n with
  | O => O
  | S n' => n'

/- The second branch can be read: "if [n] has the form [S n']
    for some [n'], then return [n']."  -/

/- The following [End] command closes the current module, so
    [Nat] will refer back to the type from the standard library. -/

end NatPlayground

/- Because Natural numbers are such a pervasive form of data,
    Lean provides a tiny bit of built-in magic for parsing and printing
    them: ordinary decimal numerals can be used as an alterNative to
    the "unary" notation defined by the constructors [S] and [O].  Lean
    prints numbers in decimal form by default: -/

#check (Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))))
/- ===> 4 : Nat -/

def minustwo (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | Nat.succ (Nat.succ n') => n'

#eval (minustwo 4)
/- ===> 2 : Nat -/

/- The constructor [S] has the type [Nat -> Nat], just like functions
    such as [pred] and [minustwo]: -/

#check (Nat.succ : Nat -> Nat)
#check (Nat.pred : Nat -> Nat)
#check (minustwo : Nat -> Nat)

/- These are all things that can be applied to a number to yield a
    number.  However, there is a fundamental difference between [S]
    and the other two: functions like [pred] and [minustwo] are
    defined by giving _computation rules_ -- e.g., the def of
    [pred] says that [pred 2] can be simplified to [1] -- while the
    def of [S] has no such behavior attached.  Although it is
    _like_ a function in the sense that it can be applied to an
    argument, it does not _do_ anything at all!  It is just a way of
    writing down numbers.

    (Think about standard decimal numerals: the numeral [1] is not a
    computation; it's a piece of data.  When we write [111] to mean
    the number one hundred and eleven, we are using [1], three times,
    to write down a concrete representation of a number.)

    Now let's go on and define some more functions over numbers.

    For most interesting computations involving numbers, simple
    pattern matching is not enough: we also need recursion.  For
    example, to check that a number [n] is even, we may need to
    recursively check whether [n-2] is even.  Such functions are
    introduced with the keyword [Fixpoint] instead of [def]. -/

def even (n:Nat) : Bool :=
  match n with
  | 0        => true
  | 1      => false
  | n'+2 => even n'

/- We could define [odd] by a similar [Fixpoint] declaration, but
    here is a simpler way: -/

def odd (n:Nat) : Bool :=
  negb (even n)

theorem test_odd1: odd 1 = true := rfl
theorem test_odd2:    odd 4 = false := rfl

/- (You may notice if you step through these proofs that
    [simpl] actually has no effect on the goal -- all of the work is
    done by [rfl].  We'll discuss why that is shortly.)

    Naturally, we can also define multi-argument functions by
    recursion.  -/

namespace NatPlayground2

def plus (n : Nat) (m : Nat) : Nat :=
  match n with
  | 0 => m
  | Nat.succ n' => Nat.succ (plus n' m)

/- Adding three to two now gives us five, as we'd expect. -/

#eval (plus 3 2)
/- ===> 5 : Nat -/

/- The steps of simplification that Lean performs can be
    visualized as follows: -/

/-      [plus 3 2]
   i.e. [plus (S (S (S O))) (S (S O))]
    ==> [S (plus (S (S O)) (S (S O)))]
          by the second clause of the [match]
    ==> [S (S (plus (S O) (S (S O))))]
          by the second clause of the [match]
    ==> [S (S (S (plus O (S (S O)))))]
          by the second clause of the [match]
    ==> [S (S (S (S (S O))))]
          by the first clause of the [match]
   i.e. [5]  -/

/- As a notational convenience, if two or more arguments have
    the same type, they can be written together.  In the following
    def, [(n m : Nat)] means just the same as if we had written
    [(n : Nat) (m : Nat)]. -/

def mult (n m : Nat) : Nat :=
  match n with
  | 0 => 0
  | Nat.succ n' => plus m (mult n' m)

theorem test_mult1: (mult 3 3) = 9 := rfl

/- You can match two expressions at once by putting a comma
    between them: -/

def minus (n m:Nat) : Nat :=
  match n, m with
  | 0   , _    => 0
  | Nat.succ _ , 0    => n
  | Nat.succ n', Nat.succ m' => minus n' m'


def exp (base power : Nat) : Nat :=
  match power with
  | 0 => Nat.succ 0
  | Nat.succ p => mult base (exp base p)


/- **** Exercise: 1 star, standard (factorial)

    Recall the standard mathematical factorial function:

       factorial(0)  =  1
       factorial(n)  =  n * factorial(n-1)     (if n>0)

    Translate this into Lean.

    Make sure you put a [:=] between the header we've given you and
    your def.  If you see an error like "The reference
    factorial was not found in the current environment," it means
    you've forgotten the [:=]. -/

def factorial (n:Nat) : Nat := sorry

theorem test_factorial1: factorial 3 = 6 := sorry
theorem test_factorial2: factorial 5 = mult 10 12 := sorry
/- [] -/

/- Again, we can make numerical expressions easier to read and write
    by introducing notations for addition, multiplication, and
    subtraction. -/

/-
infixl:50 "+" => plus
infixl:50 "-" => minus
infixl:40 "*" => mult
-/

#check ((0 + 1) + 1 : Nat)

/- (The [level], [associativity], and [Nat_scope] annotations
    control how these notations are treated by Lean's parser.  The
    details are not important for present purposes, but interested
    readers can refer to the "More on Notation" section at the end of
    this chapter.)

    Note that these declarations do not change the defs we've
    already made: they are simply instructions to the Lean parser to
    accept [x + y] in place of [plus x y] and, conversely, to the Lean
    pretty-printer to display [plus x y] as [x + y]. -/

/- When we say that Lean comes with almost nothing built-in, we really
    mean it: even equality testing is a user-defined operation!
    Here is a function [eqb], which tests Natural numbers for
    [eq]uality, yielding a [b]oolean.  Note the use of nested
    [match]es (we could also have used a simultaneous match, as we did
    in [minus].) -/

def eqb (n m : Nat) : Bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | Nat.succ _ => false
  | Nat.succ n' => match m with
            | 0 => false
            | Nat.succ m' => eqb n' m'

/- Similarly, the [leb] function tests whether its first argument is
    less than or equal to its second argument, yielding a Boolean. -/

def leb (n m : Nat) : Bool :=
  match n with
  | 0 => true
  | Nat.succ n' =>
      match m with
      | 0 => false
      | Nat.succ m' => leb n' m'

theorem test_leb1: leb 2 2 = true  := rfl
theorem test_leb2: leb 2 4 = true  := rfl
theorem test_leb3: leb 4 2 = false := rfl

/- We'll be using these (especially [eqb]) a lot, so let's give
    them infix notations. -/

notation:70 x "=?" y  => eqb x y
notation:70 x "<=?" y => leb x y

theorem test_leb3': (4 <=? 2) = false := rfl

/- We now have two symbols that look like equality: [=] and
    [=?].  We'll have much more to say about the differences and
    similarities between them later. For now, the main thing to notice
    is that [x = y] is a logical _claim_ -- a "proposition" -- that we
    can try to prove, while [x =? y] is an _expression_ whose
    value (either [true] or [false]) we can compute. -/

/- **** Exercise: 1 star, standard (ltb)

    The [ltb] function tests Natural numbers for [l]ess-[t]han,
    yielding a [b]oolean.  Instead of making up a new [Fixpoint] for
    this one, define it in terms of a previously defined
    function.  (It can be done with just one previously defined
    function, but you can use two if you want.) -/

def ltb (n m : Nat) : Bool := sorry

notation x "<?" y => ltb x y

theorem test_ltb1: ltb 2 2 = false := sorry
theorem test_ltb2: ltb 2 4 = true  := sorry
theorem test_ltb3: ltb 4 2 = false := sorry
/- [] -/

/- ################################################################# -/
/- * Proof by Simplification -/

/- Now that we've defined a few datatypes and functions, let's
    turn to stating and proving properties of their behavior.
    Actually, we've already started doing this: each [theorem] in the
    previous sections makes a precise claim about the behavior of some
    function on some particular inputs.  The proofs of these claims
    were always the same: use [simpl] to simplify both sides of the
    equation, then use [rfl] to check that both sides contain
    identical values.

    The same sort of "proof by simplification" can be used to prove
    more interesting properties as well.  For example, the fact that
    [0] is a "neutral element" for [+] on the left can be proved just
    by observing that [0 + n] reduces to [n] no matter what [n] is -- a
    fact that can be read directly off the def of [plus]. -/

theorem plus_O_n : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

/- Moreover, it will be useful to know that [rfl] does
    somewhat _more_ simplification than [simpl] does -- for example,
    it tries "unfolding" defined terms, replacing them with their
    right-hand sides.  The reason for this difference is that, if
    rfl succeeds, the whole goal is finished and we don't need
    to look at whatever expanded expressions [rfl] has created
    by all this simplification and unfolding; by contrast, [simpl] is
    used in situations where we may have to read and understand the
    new goal that it creates, so we would not want it blindly
    expanding defs and leaving the goal in a messy state.

    The form of the theorem we just stated and its proof are almost
    exactly the same as the simpler examples we saw earlier; there are
    just a few differences.

    First, we've used the keyword [theorem] instead of [theorem].
    This difference is mostly a matter of style; the keywords
    [theorem] and [theorem] (and a few others, including [Lemma],
    [Fact], and [Remark]) mean pretty much the same thing to Lean.

    Second, we've added the quantifier [∀ n:Nat], so that our
    theorem talks about _all_ Natural numbers [n].  Informally, to
    prove theorems of this form, we generally start by saying "Suppose
    [n] is some number..."  Formally, this is achieved in the proof by
    [intros n], which moves [n] from the quantifier in the goal to a
    _context_ of current assumptions. Note that we could have used
    another identifier instead of [n] in the [intros] clause, (though
    of course this might be confusing to human readers of the proof): -/

/- The keywords [intros], [simpl], and [rfl] are examples of
    _tactics_.  A tactic is a command that is used between [Proof] and
    [Qed] to guide the process of checking some claim we are making.
    We will see several more tactics in the rest of this chapter and
    many more in future chapters. -/

/- Other similar theorems can be proved with the same pattern. -/

theorem plus_1_r : ∀ n:Nat, n +1 = Nat.succ n := by
  intro n
  rfl

theorem mult_0_r : ∀ n:Nat, n * 0 = 0 := by
  intro n
  rfl

/- The [_r] suffix in the names of these theorems is
    pronounced "on the right." -/

/- It is worth stepping through these proofs to observe how the
    context and the goal change.  You may want to add calls to [simpl]
    before [rfl] to see the simplifications that Lean performs
    on the terms before checking that they are equal. -/

/- ################################################################# -/
/- * Proof by Rewriting -/

/- The following theorem is a bit more interesting than the
    ones we've seen: -/

theorem plus_id_example : ∀ n m:Nat,
  n = m ->
  n + n = m + m := by
/- Instead of making a universal claim about all numbers [n] and [m],
    it talks about a more specialized property that only holds when
    [n = m].  The arrow symbol is pronounced "implies."

    As before, we need to be able to reason by assuming we are given such
    numbers [n] and [m].  We also need to assume the hypothesis
    [n = m]. The [intros] tactic will serve to move all three of these
    from the goal into assumptions in the current context.

    Since [n] and [m] are arbitrary numbers, we can't just use
    simplification to prove this theorem.  Instead, we prove it by
    observing that, if we are assuming [n = m], then we can replace
    [n] with [m] in the goal statement and obtain an equality with the
    same expression on both sides.  The tactic that tells Lean to
    perform this replacement is called [rewrite]. -/

  intro n m
  /- move the hypothesis into the context: -/
  intro H
  /- rewrite the goal using the hypothesis: -/
  rewrite [H]
  rfl

/- The first line of the proof moves the universally quantified
    variables [n] and [m] into the context.  The second moves the
    hypothesis [n = m] into the context and gives it the name [H].
    The third tells Lean to rewrite the current goal ([n + n = m + m])
    by replacing the left side of the equality hypothesis [H] with the
    right side.

    (The arrow symbol in the [rewrite] has nothing to do with
    implication: it tells Lean to apply the rewrite from left to right.
    In fact, you can omit the arrow, and Lean will default to rewriting
    in this direction.  To rewrite from right to left, you can use
    [rewrite <-].  Try making this change in the above proof and see
    what difference it makes.) -/

/- **** Exercise: 1 star, standard (plus_id_exercise)

    Remove "[sorry.]" and fill in the proof. -/

theorem plus_id_exercise : ∀ n m o : Nat,
  n = m -> m = o -> n + m = m + o := by
  /- FILL IN HERE -/ 
  sorry
/- [] -/

/- The [sorry] command tells Lean that we want to skip trying
    to prove this theorem and just accept it as a given.  This can be
    useful for developing longer proofs, since we can state subsidiary
    lemmas that we believe will be useful for making some larger
    argument, use [sorry] to accept them on faith for the moment,
    and continue working on the main argument until we are sure it
    makes sense; then we can go back and fill in the proofs we
    skipped.  Be careful, though: every time you say [sorry] you
    are leaving a door open for total nonsense to enter Lean's nice,
    rigorous, formally checked world! -/

/- The [#check] command can also be used to examine the statements of
    previously declared lemmas and theorems.  The two examples below
    are lemmas about multiplication that are proved in the standard
    library.  (We will see how to prove them ourselves in the next
    chapter.) -/

#check Nat.mul_zero
/- ===> ∀ (n : Nat), n * 0 = 0 -/

#check Nat.mul_succ
/- ===> ∀ (n m : Nat), n * Nat.succ m = n * m + n -/

/- We can use the [rewrite] tactic with a previously proved theorem
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

/- **** Exercise: 1 star, standard (mult_n_1)

    Use those two lemmas about multiplication that we just checked to
    prove the following theorem.  Hint: recall that [1] is [S O]. -/

theorem mult_n_1 : ∀ p : Nat,
  p * 1 = p := by
  /- FILL IN HERE -/ 
  sorry

/- [] -/

/- ################################################################# -/
/- * Proof by Case Analysis -/

/- Of course, not everything can be proved by simple
    calculation and rewriting: In general, unknown, hypothetical
    values (arbitrary numbers, Booleans, lists, etc.) can block
    simplification.  For example, if we try to prove the following
    fact using the [simpl] tactic as above, we get stuck.  (We then
    use the [Abort] command to give up on it for the moment.)-/

theorem plus_1_neq_0_firsttry : ∀ n : Nat,
  ((1+ n) =? 0) = false := by
  intro n
  try rfl 
  sorry

/- The reason for this is that the defs of both [eqb]
    and [+] begin by performing a [match] on their first argument.
    But here, the first argument to [+] is the unknown number [n] and
    the argument to [eqb] is the compound expression [n + 1]; neither
    can be simplified.

    To make progress, we need to consider the possible forms of [n]
    separately.  If [n] is [O], then we can calculate the final result
    of [(n + 1) =? 0] and check that it is, indeed, [false].  And if
    [n = S n'] for some [n'], then, although we don't know exactly
    what number [n + 1] represents, we can calculate that, at least,
    it will begin with one [S], and this is enough to calculate that,
    again, [(n + 1) =? 0] will yield [false].

    The tactic that tells Lean to consider, separately, the cases where
    [n = O] and where [n = S n'] is called [cases]. -/

theorem plus_1_neq_0 : ∀ n : Nat,
  ((n + 1) =? 0) = false := by
  intros n 
  cases n
  · rfl
  · rfl

/- The [cases] generates _two_ subgoals, which we must then
    prove, separately, in order to get Lean to accept the theorem.

    The annotation "[as [| n']]" is called an _intro pattern_.  It
    tells Lean what variable names to introduce in each subgoal.  In
    general, what goes between the square brackets is a _list of
    lists_ of names, separated by [|].  In this case, the first
    component is empty, since the [O] constructor is nullary (it
    doesn't have any arguments).  The second component gives a single
    name, [n'], since [S] is a unary constructor.

    In each subgoal, Lean remembers the assumption about [n] that is
    relevant for this subgoal -- either [n = 0] or [n = S n'] for some
    n'.  The [eqn:E] annotation tells [cases] to give the name [E]
    to this equation.  Leaving off the [eqn:E] annotation causes Lean
    to elide these assumptions in the subgoals.  This slightly
    streamlines proofs where the assumptions are not explicitly used,
    but it is better practice to keep them for the sake of
    documentation, as they can help keep you oriented when working
    with the subgoals.

    The [-] signs on the second and third lines are called _bullets_,
    and they mark the parts of the proof that correspond to the two
    generated subgoals.  The part of the proof script that comes after
    a bullet is the entire proof for the corresponding subgoal.  In
    this example, each of the subgoals is easily proved by a single
    use of [rfl], which itself performs some simplification --
    e.g., the second one simplifies [(S n' + 1) =? 0] to [false] by
    first rewriting [(S n' + 1)] to [S (n' + 1)], then unfolding
    [eqb], and then simplifying the [match].

    Marking cases with bullets is optional: if bullets are not
    present, Lean simply asks you to prove each subgoal in sequence,
    one at a time. But it is a good idea to use bullets.  For one
    thing, they make the structure of a proof apparent, improving
    readability. Also, bullets instruct Lean to ensure that a subgoal
    is complete before trying to verify the next one, preventing
    proofs for different subgoals from getting mixed up. These issues
    become especially important in large developments, where fragile
    proofs lead to long debugging sessions.

    There are no hard and fast rules for how proofs should be
    formatted in Lean -- e.g., where lines should be broken and how
    sections of the proof should be indented to indicate their nested
    structure.  However, if the places where multiple subgoals are
    generated are marked with explicit bullets at the beginning of
    lines, then the proof will be readable almost no matter what
    choices are made about other aspects of layout.

    This is also a good place to mention one other piece of somewhat
    obvious advice about line lengths.  Beginning Lean users sometimes
    tend to the extremes, either writing each tactic on its own line
    or writing entire proofs on a single line.  Good style lies
    somewhere in the middle.  One reasonable guideline is to limit
    yourself to 80-character lines.

    The [cases] tactic can be used with any inductively defined
    datatype.  For example, we use it next to prove that Boolean
    negation is involutive -- i.e., that negation is its own
    inverse. -/

theorem negb_involutive : ∀ b : Bool,
  negb (negb b) = b := by
  intros b
  cases b
  · rfl
  · rfl

/- Note that the [cases] here has no [as] clause because
    none of the subcases of the [cases] need to bind any variables,
    so there is no need to specify any names.  In fact, we can omit
    the [as] clause from _any_ [cases] and Lean will fill in
    variable names automatically.  This is generally considered bad
    style, since Lean often makes confusing choices of names when left
    to its own devices.

    It is sometimes useful to invoke [cases] inside a subgoal,
    generating yet more proof obligations. In this case, we use
    different kinds of bullets to mark goals on different "levels."
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


/- Each pair of calls to [rfl] corresponds to the
    subgoals that were generated after the execution of the [cases c]
    line right above it. -/

/- Besides [-] and [+], we can use [*] (asterisk) or any repetition
    of a bullet symbol (e.g. [--] or [***]) as a bullet.  We can also
    enclose sub-proofs in curly braces: -/

theorem andb_commutative' : ∀ b c, andb b c = andb c b := by
  intro b c
  cases b
  { cases c
    { rfl }
    { rfl } }
  { cases c
    { rfl }
    { rfl } }

/- Since curly braces mark both the beginning and the end of a proof,
    they can be used for multiple subgoal levels, as this example
    shows. Furthermore, curly braces allow us to reuse the same bullet
    shapes at multiple levels in a proof. The choice of braces,
    bullets, or a combiNation of the two is purely a matter of
    taste. -/

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

/- **** Exercise: 2 stars, standard (andb_true_elim2)

    Prove the following claim, marking cases (and subcases) with
    bullets when you use [cases].

    Hint: You will eventually need to cases both Booleans, as in
    the theorems above. But, delay introducing the hypothesis until
    after you have an opportunity to simplify it.

    Hint 2: When you reach contradiction in the hypotheses, focus
    on how to [rewrite] with that contradiction. -/

theorem andb_true_elim2 : ∀ b c : Bool,
  andb b c = true -> c = true := by
  /- FILL IN HERE -/ 
  sorry
/- [] -/

/- **** Exercise: 1 star, standard (zero_nbeq_plus_1) -/
theorem zero_nbeq_plus_1 : ∀ n : Nat,
  (0 =? (n + 1)) = false := by
  /- FILL IN HERE -/ 
  sorry
/- [] -/

/- ================================================================= -/
/- ** More on Notation (Optional) -/

/- (In general, sections marked Optional are not needed to follow the
    rest of the book, except possibly other Optional sections.  On a
    first reading, you might want to skim these sections so that you
    know what's there for future reference.)

    Recall the notation defs for infix plus and times: -/

infixl:50 "+" => plus
infixl:40 "*" => mult

/- For each notation symbol in Lean, we can specify its _precedence
    level_ and its _associativity_.  The precedence level [n] is
    specified by writing `:n` after naming the command; this helps Lean parse compound
    expressions.  The associativity setting helps to disambiguate
    expressions containing multiple occurrences of the same
    symbol. For example, the parameters specified above for [+] and
    [*] say that the expression [1+2*3*4] is shorthand for
    [(1+((2*3)*4))]. Lean uses precedence levels from 0 to 1024, and
    _left_, _right_, or _no_ associativity.  We will see more examples
    of this later, e.g., in the [Lists]
    chapter. -/

/- ================================================================= -/
/- ** Fixpoints and Structural Recursion (Optional) -/

/- Here is a copy of the def of addition: -/

def plus' (n : Nat) (m : Nat) : Nat :=
  match n with
  | 0 => m
  | Nat.succ n' => Nat.succ (plus' n' m)

/- When Lean checks this def, it notes that [plus'] is
    "decreasing on 1st argument."  What this means is that we are
    performing a _structural recursion_ over the argument [n] -- i.e.,
    that we make recursive calls only on strictly smaller values of
    [n].  This implies that all calls to [plus'] will eventually
    termiNate.  Lean demands that some argument of _every_ [def]
    def is "decreasing."

    This requirement is a fundamental feature of Lean's design: In
    particular, it guarantees that every function that can be defined
    in Lean will terminate on all inputs.  However, because Lean's
    "decreasing analysis" is not very sophisticated, it is sometimes
    necessary to write functions in slightly unnatural ways. -/

/- **** Exercise: 2 stars, standard, optional (decreasing)

    To get a concrete sense of this, find a way to write a sensible
    [def] def (of a simple function on numbers, say) that
    _does_ terminate on all inputs, but that Lean will reject because
    of this restriction.  (If you choose to turn in this optional
    exercise as part of a homework assignment, make sure you comment
    out your solution so that it doesn't cause Lean to reject the whole
    file!) -/

/- FILL IN HERE

    [] -/

/- ################################################################# -/
/- * More Exercises -/

/- ================================================================= -/
/- ** Warmups -/

/- **** Exercise: 1 star, standard (identity_fn_applied_twice)

    Use the tactics you have learned so far to prove the following
    theorem about Boolean functions. -/

theorem identity_fn_applied_twice :
  ∀ (f : Bool -> Bool),
  (∀ (x : Bool), f x = x) ->
  ∀ (b : Bool), f (f b) = b := by
  /- FILL IN HERE -/ 
  sorry

/- [] -/

/- **** Exercise: 1 star, standard (negation_fn_applied_twice)

    Now state and prove a theorem [negation_fn_applied_twice] similar
    to the previous one but where the second hypothesis says that the
    function [f] has the property that [f x = negb x]. -/

/- FILL IN HERE -/

/- Do not modify the following line: -/
def manual_grade_for_negation_fn_applied_twice : Option (Nat × string) := none
/- (The last def is used by the autograder.)

    [] -/

/- **** Exercise: 3 stars, standard, optional (andb_eq_orb)

    Prove the following theorem.  (Hint: This one can be a bit tricky,
    depending on how you approach it.  You will probably need both
    [cases] and [rewrite], but casesing everything in sight is
    not the best way.) -/

theorem andb_eq_orb :
  ∀ (b c : Bool),
  (andb b c = orb b c) ->
  b = c := by
  /- FILL IN HERE -/ 
  sorry

/- [] -/

/- ================================================================= -/
/- ** Course Late Policies Formalized -/

/- Suppose that a course has a grading policy based on late Days such
    that a student's final letter grade is lowered if they submit too
    many homework assignments late.

    In this series of problems, we model that situation using the
    features of Lean that we have seen so far and prove some basic
    facts about the grading policy.  -/

namespace LateDays

/- First, we inroduce a datatype for modeling the "letter" component
    of a grade. -/
inductive Letter : Type :=
  | A | B | C | D | F
open Letter

/- Then we define the modifiers -- a [Natural] [A] is just a "plain"
    grade of [A]. -/
inductive Modifier : Type :=
  | Plus | Natural | Minus
open Modifier

/- A full [grade], then, is just a [letter] and a [modifier].

    We might write, informally, "A-" for the Lean value [Grade A Minus],
    and similarly "C" for the Lean value [Grade C Natural]. -/
inductive Grade : Type :=
  | grade (l:Letter) (m:Modifier)
open Grade
/- We will want to be able to say when one grade is "better" than
    another.  In other words, we need a way to compare two grades.  As
    with Natural numbers, we could define [Bool]-valued functions
    [grade_eqb], [grade_ltb], etc., and that would work fine.
    However, we can also define a slightly more informative type for
    comparing two values, as shown below.  This datatype as three
    constructors that can be used to indicate whether two values are
    "equal", "less than", or "greater than" one another. (This
    def also appears in the Lean standard libary.)  -/

inductive Comparison : Type :=
  | eq : Comparison        /- "equal" -/
  | lt : Comparison        /- "less than" -/
  | gt : Comparison        /- "greater than" -/
deriving Repr
open Comparison

/- Using pattern matching, it is not too difficult to define the
    comparison operation for two letters [l1] and [l2] (see below).
    This def uses two features of [match] patterns: First,
    recall that we can match against _two_ values simultaneously by
    separating them and the corresponding patterns with comma [,].
    This is simply a convenient abbreviation for nested pattern
    matching.  For example, the first two cases are just shorthand for
    the nested version shown on the right:

  match l1, l2 with          match l1 with
  | A, A => eq               | A => match l2 with
  | A, _ => gt                      | A => eq
  end                               | _ => gt
                                    end
                             end
-/

/- As another shorthand, we can also match one of several
    possibilites by using [|] as short hand.  For example the pattern
    [C , (A | B)] stands for two cases: [C, A] and [C, B] and will
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

/- We can test the [letter_comparison] operation by trying it out on a few
    examples. -/
#eval letter_comparison B A
/- ==> lt -/
#eval letter_comparison D D
/- ==> eq -/
#eval letter_comparison B F
/- ==> gt -/

/- As a further sanity check, we can prove that the
    [letter_comparison] function does indeed give the result [eq] when
    comparing a letter [l] against itself.  -/
/- **** Exercise: 1 star, standard (letter_comparison)

    Prove the following theorem. -/

theorem letter_comparison_eq :
  ∀ l, letter_comparison l l = eq := by
  /- FILL IN HERE -/ 
  sorry
  
/- [] -/

/- We can follow the same strategy to define the comparison operation
    for two grade modifiers.  We consider them to be ordered as
    [Plus > Natural > Minus]. -/
def modifier_comparison (m1 m2 : Modifier) : Comparison :=
  match m1, m2 with
  | Plus, Plus => eq
  | Plus, _ => gt
  | Natural, Plus => lt
  | Natural, Natural => eq
  | Natural, _ => gt
  | Minus, Plus | Minus, Natural => lt
  | Minus, Minus => eq

/- **** Exercise: 2 stars, standard (grade_comparison)

    Use pattern matching to complete the following def.  Note
    that the ordering on grades is sometimes called "lexicographic"
    ordering: we first compare the letters and, only in the case that
    the letters are equal do we need to consider the modifiers.
    (I.e. all grade variants of [A] are greater than all
    grade variants of [B].)

    Hint: match against [g1] and [g2] simultaneously, but don't try to
    enumerate all the cases.  Instead do case analysis on the result
    of a suitable call to [letter_comparison] to end up with just [3]
    possibilities. -/

def grade_comparison (g1 g2 : Grade) : comparison
  /- REPLACE THIS LINE WITH ":= _your_def_ ." -/
  := sorry

/- The following "unit tests" of your [grade_comparison] function
    should pass after you have defined it correctly. -/

theorem test_grade_comparison1 :
  (grade_comparison (grade A Minus) (grade B Plus)) = gt := by
  /- FILL IN HERE -/ 
  sorry

theorem test_grade_comparison2 :
  (grade_comparison (grade A Minus) (grade A Plus)) = lt := by
  /- FILL IN HERE -/ 
  sorry

theorem test_grade_comparison3 :
  (grade_comparison (grade F Plus) (grade F Plus)) = eq := by
  /- FILL IN HERE -/ 
  sorry

theorem test_grade_comparison4 :
  (grade_comparison (grade B Minus) (grade C Plus)) = gt := by
  /- FILL IN HERE -/ 
  sorry

/- [] -/

/- Now that we have a def of grades and how they compare to
    one another, let us implement the late penalty fuction. -/

/- First, we define what it means to lower the [letter] component of
    a grade. Note that, since [F] is already the lowest grade
    possible, we just leave it untouched.  -/
def lower_letter (l : Letter) : Letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F  /- Note that you can't go lower than [F] -/

/- Already our formalization can help us understand some corner cases
    of the grading policy.  For example, we might expect that if we
    use the [lower_letter] function its result will actually be lower,
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
  · sorry /- We get stuck here. -/


/- The problem, of course, has to do with the "edge case" of lowering
    [F], as we can see like this: -/
theorem lower_letter_F_is_F:
  lower_letter F = F := by rfl

/- Now we can state a better version of the lower letter theorem that
    actually is provable.  In this version, the hypothesis about [F]
    says that [F] is strictly smaller than [l], which rules out the
    problematic case above. In other words, as long as [l] is bigger
    than [F], it will be lowered. -/
/- **** Exercise: 2 stars, standard (lower_letter_lowers_fixed)

    Prove the following theorem. -/

theorem lower_letter_lowers_fixed:
  ∀ (l : Letter),
    letter_comparison F l = lt ->
    letter_comparison (lower_letter l) l = lt := by
  /- FILL IN HERE -/
  sorry
 
/- [] -/

/- **** Exercise: 2 stars, standard (lower_grade)

    We can now use the [lower_letter] def as a helper to define
    what it means to lower a grade by one step.  Implement the
    def below so that it sends a grade [g] to one step lower
    unless it is already [Grade F Minus], which should remain
    unchanged.  Once you have implemented this def correctly,
    the subsequent example "unit tests" should hold trivially.

    Hint: To make this a succinct def that is easy to prove
    properties about, you will probably want to use nested pattern
    matching. The outer match should not match on the specific letter
    component of the grade -- it should consider only the modifier.
    You should definitely _not_ try to enumerate all of the
    cases. (Our solution is under 10 lines of code, total.) -/
def lower_grade (g : Grade) : Grade
  /- REPLACE THIS LINE WITH ":= _your_def_ ." -/
  := sorry

theorem lower_grade_A_Plus :
  lower_grade (grade A Plus) = (grade A Natural) := by
  /- FILL IN HERE -/ 
  sorry

theorem lower_grade_A_Natural :
  lower_grade (grade A Natural) = (grade A Minus) := by
  /- FILL IN HERE -/ 
  sorry

theorem lower_grade_A_Minus :
  lower_grade (grade A Minus) = (grade B Plus) := by
  /- FILL IN HERE -/ 
  sorry

theorem lower_grade_B_Plus :
  lower_grade (grade B Plus) = (grade B Natural) := by
  /- FILL IN HERE -/ 
  sorry

theorem lower_grade_F_Natural :
  lower_grade (grade F Natural) = (grade F Minus) := by
  /- FILL IN HERE -/ 
  sorry

theorem lower_grade_twice :
  lower_grade (lower_grade (grade B Minus)) = (grade C Natural) := by
  /- FILL IN HERE -/ 
  sorry

theorem lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (grade B Minus))) = (grade C Minus) := by
  /- FILL IN HERE -/ 
  sorry

/- Note: Lean makes no distinction between an [theorem] and a
    [theorem]. We state this one as a [theorem] only as a hint that we
    will use it in proofs below. -/
theorem lower_grade_F_Minus : lower_grade (grade F Minus) = (grade F Minus) := by
  /- FILL IN HERE -/ 
  sorry

/- GRADE_THEOREM 0.25: lower_grade_A_Plus -/
/- GRADE_THEOREM 0.25: lower_grade_A_Natural -/
/- GRADE_THEOREM 0.25: lower_grade_A_Minus -/
/- GRADE_THEOREM 0.25: lower_grade_B_Plus -/
/- GRADE_THEOREM 0.25: lower_grade_F_Natural -/
/- GRADE_THEOREM 0.25: lower_grade_twice -/
/- GRADE_THEOREM 0.25: lower_grade_thrice -/
/- GRADE_THEOREM 0.25: lower_grade_F_Minus

    [] -/

/- **** Exercise: 3 stars, standard (lower_grade_lowers)

    Now prove the following theorem, which says that, as long as the
    grade starts out above F-, the [lower_grade] option does indeed
    lower the grade.  As usual, casesing everything in sight is
    _not_ a good idea.  Judicious use of [cases], along with
    rewriting is a better strategy.

    Hint: If you define your [grade_comparison] function as suggested,
    you will need to rewrite using [letter_comparison_eq] in two
    cases.  The remaining case is the only one in which you need to
    cases a [letter].  The case for [F] will probably benefit from
    [lower_grade_F_Minus].  -/
theorem lower_grade_lowers :
  ∀ (g : Grade),
    grade_comparison (grade F Minus) g = lt ->
    grade_comparison (lower_grade g) g = lt := by
  /- FILL IN HERE -/ 
  sorry

/- [] -/

/- Now that we have implemented and tested a function that lowers a
    grade by one step, we can implement a specific late Days policy.
    Given a number of [late_days], the [apply_late_policy] function
    computes the final grade from [g], the initial grade.

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

/- Sometimes it is useful to be able to "unfold" a def to be
    able to make progress on a proof.  Soon, we will see how to do this
    in a much simpler way automatically, but for now, it is easy to prove
    that a use of any def like [apply_late_policy] is equal to its
    right hand side. (It follows just from rfl.)

    This result is useful because it allows us to use [rewrite] to
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

/- Let's prove some properties about this policy... -/

/- This theorem states that if a student accrues no more than 8 late
   Days throughout the semester, your grade is unaffected. It is
   easy to prove, once you use the [apply_late_policy_unfold]
   you can rewrite using the hypothesis. -/

/- **** Exercise: 2 stars, standard (no_penalty_for_mostly_on_time)

    Prove the following theorem. -/

theorem no_penalty_for_mostly_on_time :
  ∀ (late_days : Nat) (g : Grade),
    (late_days <? 9) = true ->
    apply_late_policy late_days g = g := by
  /- FILL IN HERE -/ 
  sorry

/- [] -/

/- The following theorem proves that, as long as a student has
    between 9 and 16 late Days, their final grade is lowered by one
    step. -/

/- **** Exercise: 2 stars, standard (graded_lowered_once)

    Prove the following theorem. -/

theorem grade_lowered_once :
  ∀ (late_days : Nat) (g : Grade),
    (late_days <? 9) = false ->
    (late_days <? 17) = true ->
    (grade_comparison (grade F Minus) g = lt) ->
    (apply_late_policy late_days g) = (lower_grade g) := by
  /- FILL IN HERE -/ 
  sorry

/- [] -/
end LateDays

/- ================================================================= -/
/- ** Binary Numerals -/

/- **** Exercise: 3 stars, standard (binary)

    We can generalize our unary representation of Natural numbers to
    the more efficient binary representation by treating a binary
    number as a sequence of constructors [B0] and [B1] (representing 0s
    and 1s), termiNated by a [Z]. For comparison, in the unary
    representation, a number is a sequence of [S] constructors termiNated
    by an [O].

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

/- Complete the defs below of an increment function [incr]
    for binary numbers, and a function [bin_to_Nat] to convert
    binary numbers to unary numbers. -/

def incr (m:Bin) : Bin
  /- REPLACE THIS LINE WITH ":= _your_def_ ." -/
  := sorry

def bin_to_Nat (m:Bin) : Nat
  /- REPLACE THIS LINE WITH ":= _your_def_ ." -/
  := sorry

/- The following "unit tests" of your increment and binary-to-unary
    functions should pass after you have defined those functions correctly.
    Of course, unit tests don't fully demonstrate the correctness of
    your functions!  We'll return to that thought at the end of the
    next chapter. -/

theorem test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z) := by
  /- FILL IN HERE -/ 
  sorry

theorem test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z) := by
  /- FILL IN HERE -/ 
  sorry

theorem test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)) := by
  /- FILL IN HERE -/ 
  sorry

theorem test_bin_incr4 : bin_to_Nat (B0 (B1 Z)) = 2 := by
  /- FILL IN HERE -/ 
  sorry

theorem test_bin_incr5 :
        bin_to_Nat (incr (B1 Z)) = 1 + bin_to_Nat (B1 Z) := by
  /- FILL IN HERE -/ 
  sorry

theorem test_bin_incr6 :
        bin_to_Nat (incr (incr (B1 Z))) = 2 + bin_to_Nat (B1 Z) := by
  /- FILL IN HERE -/ 
  sorry

/- [] -/

/- ################################################################# -/
/- * Testing Your Solutions -/

/- Each SF chapter comes with a test file containing scripts that
    check whether you have solved the required exercises. If you're
    using SF as part of a course, your instructors will likely be
    running these test files to autograde your solutions. You can also
    use these test files, if you like, to make sure you haven't missed
    anything.

    Important: This step is _optional_: if you've completed all the
    non-optional exercises and Lean accepts your answers, this already
    shows that you are in good shape.

    The test file for this chapter is [BasicsTest.v]. To run it, make
    sure you have saved [Basics.v] to disk.  Then do this:

       coqc -Q . LF Basics.v
       coqc -Q . LF BasicsTest.v

    (Make sure you do this in a directory that also contains a file named
    [_LeanProject] containing the single line [-Q . LF].)

    If you accidentally deleted an exercise or changed its name, then
    [make BasicsTest.vo] will fail with an error that tells you the
    name of the missing exercise.  Otherwise, you will get a lot of
    useful output:

    - First will be all the output produced by [Basics.v] itself.  At
      the end of that you will see [COQC BasicsTest.v].

    - Second, for each required exercise, there is a report that tells
      you its point value (the number of stars or some fraction
      thereof if there are multiple parts to the exercise), whether
      its type is ok, and what assumptions it relies upon.

      If the _type_ is not [ok], it means you proved the wrong thing:
      most likely, you accidentally modified the theorem statement
      while you were proving it.  The autograder won't give you any
      points for that, so make sure to correct the theorem.

      The _assumptions_ are any unproved theorems which your solution
      relies upon.  "Closed under the global context" is a fancy way
      of saying "none": you have solved the exercise. (Hooray!)  On
      the other hand, a list of axioms means you haven't fully solved
      the exercise. (But see below regarding "Allowed Axioms.") If the
      exercise name itself is in the list, that means you haven't
      solved it; probably you have [sorry] it.

    - Third, you will see the maximum number of points in standard and
      advanced versions of the assignment.  That number is based on
      the number of stars in the non-optional exercises.

    - Fourth, you will see a list of "Allowed Axioms".  These are
      unproved theorems that your solution is permitted to depend
      upon.  You'll probably see something about
      [functional_extensionality] for this chapter; we'll cover what
      that means in a later chapter.

    - Finally, you will see a summary of whether you have solved each
      exercise.  Note that summary does not include the critical
      information of whether the type is ok (that is, whether you
      accidentally changed the theorem statement): you have to look
      above for that information.

    Exercises that are manually graded will also show up in the
    output.  But since they have to be graded by a human, the test
    script won't be able to tell you much about them.  -/

/- 2023-03-25 11:11 -/
