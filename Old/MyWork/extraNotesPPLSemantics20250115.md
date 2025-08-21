
In class, we also covered
-  history behind imperative (Turing, von Neumann) and declarative (Church) languages
-  countability, with proofs  of it for the rationals, and uncountability for the reals
-  an informal proof by contradiction here here.

We also heard that there's but a countable number of programs
so there's no way every real can have a program that computes it.
Not only are the real numbers uncountable; many are ucomputable:
beyond the reach of finite (terminating) program executions.

The nominal/main subject of the class was semantics of propositional
logic. We did cover, including much of the narrative, terms, and
perspective shifts described in the intro to the next chapter on
*model theory*.

When we say we're "evaluating an expression over an interpretation,"
we remember to view interpretation as representations of particular
"worlds" within which the expression can be evaluated. Evaluating an
expression, e, over an interpretation, i, or in world i, can now be
seen as applying *(eval e)* to i to produce a Boolean indicating
whether i satisfies e or not. 

Next we came to see *e* as a specification of a *property* that any
given world might or might not have. One example would be the property
of having at least one happy pet. If this property is specified in
propositional logic by the expression,  e := HappyCat \/ HappyDog,
then we have four worlds to consider: no happy pet, only dog happy,
only cat happy, and both pets happy. Only three of these four worlds
has the property specified by e.

We know that *(eval e i)*, or [[e]]i, reduces to the semantic value
of *e* over *i*; and we can also express this idea by saying that *i*
satisfies the predicate, *e*, that i is a model for e, or that *i* has
has the property (specified by) *e*.

Finally, let's consider the expression *(eval e)*, or [[e]]. We
know that *eval* takes an expression and an interpretation. What
you will also is that *(eval e)* reduces to a function: it's one
that is like *eval* but with *e* already "baked in," and that is 
ready to be applied to an *i* to produce a final Boolean answer. 
We can thus now see [[e]] as a function that that can use to check
whether a given world or situation has the property specified by
*e* or not. We now have the concept of *property checking.*

Think of expressions as specifying properties of possible words
is not always what you want to do. Soon enough we'll see that we
will want to view some propositions as formally specifying valid
patterns of logical thinking. Check out the propositions listed in
the examples file in Chapter 1. Most of them seem reasonable but
you'll have to think through some of them, and just a few are not
valid: they don't work in all circumstances.

## To Do
