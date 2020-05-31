# Formal Verification of a Realistic Compiler

## Summary
In [this paper](./paper.pdf), Xavier Leroy provides an overview of the
development and verification of CompCert. This begins with exploring some
equivalent definitions of what it means for a compiler to be verified; this is
relevant because CompCert uses various verification methods for different
compiler passes, and composes them together.
Next, there is an overview of the compiler passes and a breakdown of how much
Coq code is dedicated to the passes' formal specifications and proofs.
In addition to the formal methods, however, Coq is also used as the programming
language to write the compiler, so the compiler functions are first-class
citizens to the proof assistant, which avoids the need for a separate program
logic. Leroy then details the verification of the register allocation pass, where
much of the described machinery, while very domain specific, looks quite
familiar after reading 10 chapters of Frap. The paper concludes by describing
future goals and elaborating on the unverified parts of the compiler, with
possible consequences and mitigations.

## Strengths
I enjoyed this paper; it was a refreshing conclusion to the quarter after
reading more pessimistic views on formal verification. What I enjoyed most was
seeing that the techniques we learned in class were the main overarching tools
used in the CompCert verification

- small-step operational semantics [4.1]
- dataflow analysis [4.2]
- simulation relation [4.3]

I also found the verification of the *validation* of the graph coloring
heuristic [4.2] to be an interesting approach to avoid the difficulty in proving
the correctness of the algorithm itself.

Lastly, I appreciated the concluding elaboration on what is *not* verified, and
what that means for users of CompCert.

## Critiques
At the end of [4.3] there is what looks like an informal proof of what is the
correct specification for the relationship between register state R and location
state R'. I didn't quite follow the logic here; perhaps it is possible, and
beneficial, to formally verify this specification.

While I listed the conclusion as a strength, I do find it interesting that
Leroy feels issue (1) is the most delicate, namely that developers writing
Clight may have differing views on the meaning of their programs. I personally
am more concerned with issues like (2) and (3): the unverified parts of the
compiling process, particularly Coq's extraction facility, and the Caml compiler
and run-time system. Shouldn't the Caml compiler that produces the Clight
compiler be just as important to verify as the Clight compiler itself?
