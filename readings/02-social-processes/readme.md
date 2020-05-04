# Social Processes and Proofs of Theorems and Programs

## Summary
In [Social Processes and Proofs of Theorems and Programs](./paper.pdf), De
Millo, Lipton, and Perlis issue an attack on the (a) motivation, (b)
practicality, and (c) potential consequences of formal verification of
programs. For avenue (a), the attack is primarily on the _classicist_ view of
mathematics, the view in which one considers a proof as evidence that there
does exist some completely formal, mechanical deduction from the basest axioms.
Instead, the authors argue that proofs are simply messages passed among the
mathematical community and describe the social process by which confidence in a
theorem grows, stating that only at the end of this process is the theorem
thought to be true in the classical sense.  They argue that there is no such
social analog for formal verifications as messages, and conclude formal
verification is doomed to fail.

For avenue (b), the authors first make a strong claim that a program of 20,000
lines will never read "VERIFIED" because any human artifact of sufficient size
and complexity is imperfect.  Next, they claim that the discontinuous nature of
programs make verification of complex software all but infeasible.

For (c), it is argued that while the desire for correct programs is valuable,
efforts would be better spent on making reliable programs. Furthermore the
authors warn against restricting the design of programming
languages to ease verification.

## Strengths
In general, I find the arguments increase in validity from (a) to (c). I
have very little strengths to report from (a) and (b), and perhaps the only
positive thing I can say is that I do like the analogy of a proof as a message,
to be passed around and iterated upon.  In (c), the arguments for where research
effort could be better spent are worthwhile and, in fact, some of them hold up
quite well 40 years later.

In suggesting ways that computer scientists can make
programming more like engineering and mathematics, the authors have some ideas
that have largely panned out: the abstraction of general structures are often
separated and published as their own libraries ("whose specific instances become
more reliable as the reliability of the general structure increases"), and the
open source movement has dramatically increased exposure of software to social
processes.

Lastly, the argument that ease of formal verification should
not dominate program language design is a worthy avenue for debate. It is
arguable that writing correct and reliable software may be easier to elicit in
languages designed from a motivation of human intuition, and if such a design
goal leads a language in a different direction than the goal of easier
verification, this trade-off is certainly worth exploring.

## Critiques
First, I take issue with the attack on the classicist view of mathematics, which
minimizes the important role that formalism played in the history of
mathematics; prior to Cantorian set theory, mathematics was largely
untethered and in dire need of paradoxical resolutions (see "Everything and
More", by DFW, for excellent historical context). Without such formalization,
modern mathematics would not be where it is today.

The statement

> mathematicians' errors are corrected, not by formal symbolic logic, but by
> other mathematicians

is not necessarily inherent to mathematics; it is quite plausible that this
observation had only held up until the time of writing precisely because
mathematicians did not have a convenient mechanism for the construction of
symbolic logic, i.e., verification tools.

I believe the authors overvalue the simplicity of a proof. Many of the most
famous results in mathematics have objectively complex proofs: take for
example Fermat's Last Theorem, which took Andrew Wiles 7 years and 129 pages
to prove, and yet was still "the proof of the 20th century" according to
legend John Conway, may he rest in peace.

The "fundamental logical objection" based on the transition from formal
(program) to informal (requirements) is absurd. Their argument is easily seen
as insubstantial when applied directly to formal logic in mathematics; a
deduction can be formal, and so can its statement. The mathematician's
interpretation of said statement, analogous to program requirements, is
informal, but this transition is not one that upends the foundation or utility
of either domain.

Finally let's consider issues in (b). First, the statement

> No programmer would agree that large production systems are composed of
> nothing more than algorithms and small programs

has not aged well. The current trend is precisely the opposite: microservices
which each serve a single, simple purpose.  This point alone disarms many of
the arguments throughout the paper. In particular, the claim that there is no
continuity to scale from small verified pieces to large complex production
software is baseless; one could easily imagine verifying component services in
isolation, perhaps with another verification of the conjunction of the
services. Even if the "glue" verification of this conjunction were infeasible,
their argument disregards the value of having verified components at all; you
get to rule out large classes of errors if certain components of your software
are verified.

Furthermore the authors repeatedly cite examples of how long formal deductions
would be from first principles; why should we assume that this is necessary?
Proofs don't work this way; if a lemma is already proven it is freely available
for use in a theorem. The same can and should be true in formal verification.
For example, one could imagine importing a module that exports a type signature
guaranteeing a certain theorem; importers could assume this theorem, but the
verification could be in separate pieces.

One particular line I referenced above is a good representative example of the
arguments in this paper: in regards to a programmer returning to the
verification of his (sic) 20,000 line program:

> The message will never read VERIFIED.

Of course, if true, this claim alone would be reason enough to halt
verification research, but it is obviously unfounded speculation.

The quote above brings up one final issue with this paper, perhaps the only
issue I've outlined which can be blamed on the times and perspectives of the
authors in 1979: gender stereotyping and normativity abound!
