namespace DMT1.reasoning

/- @@@
We'll assume that P, Q, and R are some given
propositions, and that p is a proof of P, q is
a proof of Q, and r is a proof of R.
@@@ -/
variable
  (P Q R : Prop)
  (p : P)
  (q : Q)
  (r : R)

def pq :    P ∧ Q        :=  And.intro p q
def p_qr :  P ∧ (Q ∧ R)  :=  And.intro p (And.intro q r)
def pq_r :  (P ∧ Q) ∧ R  :=  And.intro (And.intro p q) r

def pq' :    P ∧ Q        :=  ⟨ p, q ⟩
def p_qr' :  P ∧ (Q ∧ R)  :=  ⟨ p, ⟨ q, r ⟩ ⟩
def pq_r' :  (P ∧ Q) ∧ R  :=  ⟨ ⟨ p, q ⟩, r ⟩


theorem andCommutes' : P ∧ Q → Q ∧ P := by
intro h
exact And.intro (And.right h) (And.left h)

theorem andCommutes : P ∧ Q → Q ∧ P := by
  intro h
  let p := And.left h
  let q := And.right h
  exact  ⟨ q, p ⟩

theorem andAssoc : P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R := by
  apply Iff.intro _ _
  intro h
  let p := h.left
  let q := h.right.left
  let r := h.right.right
  let pq := And.intro p q
  exact (And.intro pq r)
  intro h
  let p := h.left.left
  let q := h.left.right
  let r := h.right
  let qr := And.intro q r
  exact (And.intro p qr)



end reasoning
