# Reflections on Trusting Trust

## Summary

In [this paper](./paper.pdf), Ken Thompson demonstrates that the code one
reads, or even writes, can have unexpected and potentially malicious behavior,
unbeknownst to the user and even the programmer. He tells a story in three
stages:

1. Stage 1 considers a C program which, when compiled and executed, will
   produce as output an exact copy of its source.
2. Stage 2 demonstrates how one can extend the official C compiler with C code,
   creating a new compiler that will accept a new unprintable character
   `\v`. This is done in two sub-stages, where initially we make
   a new compiler that directly knows to treat `\v` as the
   vertical tab by using the ASCII 11 decimal. Then we use this "smarter"
   compiler to compile a C interpreter that simply treats the string
   `\v` as the unprintable character `\v`, which
   the new compiler has now learned is the vertical tab.
3. Stage 3 first shows how one would naively add a Trojan horse to the C
   compiler, which when used to compile the UNIX `login` command, would allow
   a particular known password to be used on any resulting compiled `login`
   executables. However, a quick look at the C compiler source code would
   reveal this malicious code. Instead, Thompson shows a sneakier way to
   accomplish this by using the previous two stages: add the Trojan horse that
   targets the aforementioned login program, and add a second Trojan horse that
   targets the C compiler program and replaces it with the Stage 1
   self-reproducing program, which of course will insert the two Trojan horses.
   Just as in Stage 2, we have two sub-stages: first use the official compiler
   to compile this obviously bugged C compiler to create the "smarter"
   compiler. Now remove the bugs from the C compiler source code and use this
   "smarter" compiler to compile what looks like the official and
   non-malicious C source code. Then the new compiler will insert the two
   Trojan horses, as it was trained to do, even though the source makes no
   mention of them.

Thompson has deftly demonstrated that you cannot trust code that you did not
*totally* create yourself. He then concludes the paper on a fairly
unrelated topic, namely unauthorized access to computer systems. He criticizes
the press for its treatment of hackers as heroes when they are, in fact,
criminals, and describes the urgent need for the social stigma surrounding
hacking to match analogous wrongdoings of trespass and theft, especially since
the legal system will soon treat these activities properly.

## Strengths
I thought the presentation of how to produce the final bugged compiler in three
stages was very clear and concise. I really enjoyed Stage 1 in particular; I had
never seen this programming exercise before and found the solution clever and
satisfying. My favorite part and what I found most valuable was the culmination
of the three stages to produce the bugged compiler. This is kind of a confusing
concept to write in words, but breaking down the process into stages, not
unlike the process of breaking down a procedure into functions, makes things
much easier to understand altogether.

## Critiques
First, while the idea behind the bugged compiler is devilishly clever, it's not
obvious that this should be a practical concern. If an attacker had access to
swap compiler binaries on a server, presumably they could wreak even more havoc
in other ways. And, if it is a legitimate concern, the author offers no
possible avenue for defending such an attack.

Second, I found the closing argument out of place. I imagine that Thompson
wanted to write about trusting code, i.e., the main part of the paper, but also
felt he had a platform in this Turing Award response, and so wanted to include
some social commentary on hacking. That being said, I don't disagree with any
of his concluding remarks; it sounds like a valuable perspective and comment on
the hacking scene, at the time of writing.

Throughout the paper there is talk of the C compiler binary but also the C
program that produces the compiler, but Thompson uses the single word
"compiler" for both of these entities, which caused me some confusion.

Last, and certainly least, the labels are swapped on Figures 2.1 and 2.2.
