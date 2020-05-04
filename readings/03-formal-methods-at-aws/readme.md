# Use of Formal Methods at AWS

## Summary
In [this paper](./paper.pdf), engineers at AWS describe their experience of
applying formal methods to real world problems, specifically formal
specification and model checking. It is argued that traditional industry
verification methods often fail at the complexity level of services built at
AWS, largely due to an underestimation bias of the true probability of
supposedly "extremely rare" events in systems operating at massive scale. These
traditional methods work well for finding bugs in implementation, but fail to
find bugs in design. The authors found that writing designs in the formal
specification language TLA+ and using the associated TLC model checker proved
very effective in identifying such design bugs. Some other practical benefits
included
1. a better approach to writing designs
2. ease of refactoring
3. automatic documentation.

## Strengths
The exposition of the problem of designs at large scale to be caused in part by
underestimation of probabilities is incisive. The same is true for the
comparison of designing systems with and without TLA+, i.e. designing for the
happy case and _what might go wrong_ versus _what needs to go right_.  In
describing the ROI, I appreciated the table of real examples that list the
investment of Line Count and return of Benefits.  In general, I thought the
paper successfully demonstrated that formal specification can be practical and
worthwhile in more than just safety-critical domains.

## Critiques
It is condescending at best and stereotyping at worst to obscure words like
"verification" when presenting to engineers - are you really helping change
the widespread view that formal methods are impractical if you aren't letting
them shine? Similar assumptions are made about we the readers in the decision
not to include snippets of specifications, which in my opinion would have
improved the paper. There is a slight scent of elitism here.

It would be helpful to know more than just the LOC of certain specifications
when evaluating the cost of the overall investment, such as an explanation of
how formal specification has altered the existing workflow at Amazon. There may
be less cycles of development and testing, but how much time is now allocated
upfront to the design phase? What about maintenance cost of these specifications
once they are created? How does this maintenance impact the workflow?

Lastly, in describing the shortcomings of formal specification, the authors
describe a class of "sustained emergent performance degradation" problems
that they have been unable to model, and allude to the use of other
techniques to mitigate such risk. What are these techniques? Trade secrets?
