# Tiny typed lambda calculus

In my effort of teaching myself type theory and PL design I decided to write a basic term type checker. The following is a small subset of lambda calculus that supports the following expressions: ``Int``, ``Applications``, ``Abstractions``, ``Add``, ``Variables``, ``If expressions``, ``True and false expressions``.

For now the following primitives are supported: ``Booleans``, ``Integers``, ``Functions``.
# Grammar
todo.

# Brief Introduction
todo.
# Examples
The identity function for booleans is defined by the following lambda expression: λ*x*:*Bool*.*x*. Which accepts an *x* of type *Bool* as parameter and returns the same type. That is, a function *Bool -> Bool*.

# Todo
[ ] Polymorphic types.
[ ] Implement Hindley-Milner algorithm.
[ ] Implement a REPL.
[x] Add tests.
