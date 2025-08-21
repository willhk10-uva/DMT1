/- @@@
Note: In commonplace mathematical lingo, a theorem is often
thought of as a "true proposition:" for which a proof has
been given. There's also a purely social convention around
using the word, theorem. A theorem is an "important" truth,
often the "main result" of a mathematical research project.
To produce such a proof it's often important to prove one or
more "smaller" propositions along the way. The word used for
these is usually "lemma." Finally, facts that follow from the
truth of a theorem are usually called "corollaries."

Lean4 does support use of the word, theorem, instead of def,
when defining a proof of a proposition. It is just a nicety
with no real additional importance. No need to be perplexed
by it. Just read it as "def."
@@@ -/


--------
/- @@@
Recall that the introduction rule takes a specific value,
*w*, and proof, *pf : P w,* that that value has property
*P*. Elimination destructures such a proof. What is gives
you back, however, is not the *specific* witness used to
create the proof, but rather than arbitrary value, *w : T*,
along with a proof of *P w*. For this reason, you will see
that proofs of existence are called *information hiding*
objects. A specific witness is no longer availabe from a
proof of existence.
@@@ -/


/- @@@
To this end. delete everything from fun to the end and put
(_) in its place. Next, use Lean to display, and understand,
what type of value is needded. Provide a complete term of that
type if you can, but in any case apply the right inference
rule to as many of its arguments as you have, arranging the
actual arguments vertically indented and with (_) for each
of the arguments to be filled in subsequently. And now just
elaborate what goes in each of those "holes", until you get
to the bottom of the proof object (here, at *tea.right*). You
can't just read the text, you have to watch and experience
the emergence of the proof, largely at this point fron the
mere syntactic forms of the propositions being proved all
along the way.
@@@ -/

/- @@@
The preceding expression of the proof explicitly applies
inference axioms without Lean-provided concrete notations.
The following expression of the proof uses concrete notations.

Here's what that looks like. Lean packs all of the above into
the often more compact and humanly interpretable "by case analysis
syntax using pattern matching" notation. Here's that very same
proof presented in this more conventional notation. in
Lean. This notation, by the way, is largely adopted from Haskell,
a historically and practically important programming language. It
ushered in numerous fundamental constructs now deeply embedded not
only into Lean but a broad swatch of functional languages. Others
include, for example, OCaml, SML, etc. The Coq proof assistant, a
most interesting, still important, antecedent of Lean, is written
in OCaml, so with Coq, it's all the same ideas we've been learning
but in OCaml-like syntax rather than Haskell-like syntax. Cool, eh!
A great mind exercise is to read through the completely desugared,
pure functional proof construction, and see where each element in
that definition is reflected in the one using Haskelly notation,
here.
@@@ -/


/- @@@
way to apply elimination is by pattern matching,
as in the following example. It shows that if there exists a
number that's true and even, then there's a natural number
that's even. Note that what matching gives you is not the
specific value used to form the proof, but an *arbitrary*
value, *w* and a proof *pf : P w.* That is what you have
to work with after applying the elimination rule.
@@@ -/

/- @@@
To show this we destructure *pf* as *⟨ w, pf_w ⟩*. This
gives us a witness, *w : Nat* (whose value we do not know),
along with a proof, *pf_w*, that *w* (whatever value it is)
satifies both *True* and *is_even.* Surely then *w* satisfies
*is_even* by itself. That's the insight.

We can thus form the desired proof by applying Exists.intro
to *w* and a proof that *w* satisfies *is_even.* Here *w*
is the witness (value unknown) obtained by destructuring the
assumed proof of the premise. We know it's and so will be able
to use it as a witness in a proof that there is an even number.
Now *pf_w* is then an assumed proof that *w* satisfies both
*True* and *is_even*. From this proof we can derive a proof
that *w* satisfies *is_even* (by and elimination right). To
prove there exists an even number, then, we just apply
Exists.intro to *w* and to *pf_w.right*. (You can use *.2*
instead of *.right* in this expression).

In English we might say this. Prove that if there's a number
that is True and even then there's a number that's even.

Proof: Assume there's a number that is True and even. We
can then deduce that there is number, *w*, for which there
is a proof, *pf* that *w* is *True* and *w* is *even*.
From that proof, *pf,* by *and elimination right,* we can
deduce there's a proof, *pf_w_even*, that *w* is even.
So we now have a witness, *w*, and a proof that *w* is
even, so we can form a proof that there exists a number
that's even: ⟨ w, pf_w_even ⟩.
@@@ -/




--------
