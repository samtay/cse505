# Formal Proofs, the Fine Print and Side Effects

## Summary
In [this paper](./paper.pdf), Murray and van Oorschot make general observations
and raise important questions regarding the current role (real and perceived) of
formal methods that they feel must be answered in order to provide an accurate
cost-benefit analysis of formal methods. Some of the highlights are:

1. Observations
  - proofs (and namely their drawbacks) remain largely misunderstood, especially
  by non-experts
  - along with benefits of proofs come *side effects* like code changes and
  deployment constraints
  - there are various perspectives on what the *value* of a proof is

2. Questions
  - What is the relationship between proof side effects and changes that stop
  attacks?
  - How much value is retained by a proof when some of its assumptions are not
  met?
  - How can we better explain the "fine print" that comes with a proof?

## Strengths
Although the goal of this paper is simply to raise awareness and questions for
further exploration, I still found it very informative and appreciated the
various demonstrative examples. In particular the various misunderstandings of
proofs hit close to home for me; I would certainly be categorized by the authors
as a "non-expert" but I am also an enthusiast, and at times reading about the
various misconceptions felt like someone was pointing out how loudly I chew. I
sometimes broadly consider something that has been formally verified "bug-free",
even if I don't use those words exactly. To this end, the analogy of "fine
print" for various modeling assumptions is apt, just in the same way others may
naively think "Facebook is free!".

On the other hand, the authors also observe that *even for experts*
understanding the precise claims of a formal theorem can take huge effort, and
offer the example of Benjamin Pierce spending a person-week of effort to
understand the main seL4 correctness theorem statement.

Another valuable observation by the authors is that any proof about a system's
security *necessarily* makes assumptions about the attacks they claim to
prevent, and the Spectre attack in Example 1 is a great demonstration of just
how limiting this is.

As we saw in the AWS paper, one of the proof benefits observed is that
the process forces the human to carefully examine the system model, and this
examination often reveals flaws before the proof is even complete.  Greg Nelson
clearly falls in this camp as well, considering the value of a proof *not* to be
any sort of guarantee, but rather a "bug-catcher".

Finally, defining the sets
  - P := side effects of proofs
  - A := side effects needed to stop attacks

and examining their various possible relationships precisely illustrates
our current lack of understanding and context surrounding formal methods.

## Critiques
It's hard to find critiques of a paper whose sole purpose is to raise questions
and not answer them. However, given that the authors have spent such effort in
analyzing the current literature and identifying these important questions, an
obvious potential for improvement would be to at least propose potential avenues
for their answers.

The paper broadly considers only two groups of proof side effects: code changes
and deployment constraints. I think we should also consider something akin to
"operational effects"; one of the rather obvious "costs" in a cost benefit
analysis is in terms of time and money. Clearly verification
efforts incur this cost both upfront and in ongoing maintenance.

While I find the analysis regarding sets P and A illustrative for discussion,
it's not clear if measuring their intersection is actually a worthwhile question
to answer. Given the very general definitions of these sets, it very well may be
an impossible thing to measure.
