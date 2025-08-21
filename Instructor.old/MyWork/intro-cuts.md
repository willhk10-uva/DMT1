The alternative is type theory. If one takes first-order set theory as the foundation,
types are then represented in those terms, and machines have to deal with structures
from the unwieldy realm of its axioms and reasoning principles. And, if one takes type
theory as the foundation, then one embeds set theory abstractions into it. The huge
gain now for choosing type theory is that it is the winner in many dimensions, which
include impressive and capable tooling at this stage, and the embrace of a significant
specialised subcommunity from across many branches of mathematical research who are
now working to establish state of the art machine-checked mathematical foundations
for their many diverse fields of mathematics. More recently, demand I'm told now far
outstrips the supply of trained Lean programmers, perhaps MS-and-above level or above.

So, this course is meant to suggest a possible model to replace traditional CS2 courses in
DMT.  Beyond that, it's being used as the first segment of a current introductory graduate
course. For the broader community is perhaps it'll provide another slightly different path
from step zero into programming and reasoning in Lean 4. A 2-3X speed version of this course,
as the first big unit in a grad course, seems to fit the need.  This online book will be
posted in pieces over the coures the current semester (as of Spring 2025). The result will
be a formal explication what what at the end solved the constraint: teach everything that
has to be covered, now on type theoretical foundations and using the new gnerations of
tools, without too much distraction from the tooling, and with obvious gains in clarity,
generality of abstractions, correctness, completeness, layeredness (e.g., set theory, as
embedded in (higher-order) predicate logic as that is embedded in the foundational logic.
The win in the availability of software tooling, appropriateness of levels of abstraction,
deep active community makes it plausible to consider throwing the switching. 

The hypothesis for this book draft is thus roughly that switching CS students from courses
based on first-order theory and quasi-formal presentations, to one something more akin to
this, would better engage students in their main area of interest, computation, while giving
them fluency is concepts and tools for which it's clear there's now growing demand up the
stack at some of the most dominant, e.g., cloud computing, companies in the world. Now is a
great time to consider it.


--

Any first course in DMT must cover propositional and predicate logic, set theory, and induction.
This course delivers roughly the logical and mathematical concepts covered in a traditional course,
using standard notations, but now with these amazing capabilities at one's fingertips. Some faculty
and students complain about being distracted by the syntax of Lean. But at the end of the day, Lean
is the logic they should really be learning if they want "in." That said, across multiple evolving
offerings of this course, it has been a challenge to find that complete little sub-fractal of the
vast expanse of Lean in which logical reasoning in type theory is, at bottom, deeply computational.
So, type theory, not first-order set theory.

The solution here rests on a few practices. Some are: to minimize intellectually irrelevant
distrations following from the use of the Lean language and tooling; focus sharly on students'
eventual understanding of logical types and inference rules as precise, polymorphic subroutines
that you compose into programs that compute and foundationally check proofs.

The last big part of the course then uses everything learned about so far to embed the concepts
and notations of set theory in Lean, based on the choice not only to specify but also then to 
representing sets and relations as predicates. Students must develop the intellectual ability
to translate across such abstraction boundaries, while uttering the magic incantation, "by the
definition of ... it will suffice to show ...."


