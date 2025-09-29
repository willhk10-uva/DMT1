def andAssoc : Prop := ∀ (P Q R : Prop), P ∧ (Q ∧ R) → (P ∧ Q) ∧ R  /- 'And' is associative! -/

def pfAndAssoc : andAssoc :=
  fun (P Q R : Prop) =>
    (
      fun (pqr : P ∧ (Q ∧ R)) =>
      (
        let p:P := pqr.left
        let q:Q := pqr.right.left
        let r:R := pqr.right.right
        let pq : P ∧ Q := And.intro p q
        And.intro pq r
      )
    )

#check pfAndAssoc
