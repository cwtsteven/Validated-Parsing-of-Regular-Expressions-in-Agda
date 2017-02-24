# Parsing-Regular-Expressions

This is my Computer Science project submitted to the University of Birmingham as part of its undergraduate degree requirements.

In this project, we aim to study the feasibility of constructing a certified algorithm for translating
regular expressions to finite automata in Type Theory. The translation consists of several
steps: regular expressions to NFA (with epsilon step) using Thompson's construction; NFA (with epsilon step) to NFA by removing
epsilon-transitions; DFA to DFA by powerset construction; and DFA to MDFA by removing unreachable
states and quotient construction. The correctness of the translation is obtained by showing that
their accepting languages are equal and the translated MDFA is minimal. The above translation
and its correctness proofs are formalised in Agda { a dependently-typed functional programming
language based on Type Theory.
