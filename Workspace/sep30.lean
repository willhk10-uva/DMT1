theorem hungry (H M S : Prop) : (H ∧ M) → (H → M → S) → S :=
(
  fun hm : H ∧ M => /- hm is of type H ∧ M-/
    fun hms: H → M → S => /- hms is of type H → M → S-/
    (
      hms (hm.left) (hm.right) /-by pulling H and M out of hm, you now can prove hms-/
    )
)


theorem xyz (C M B : Prop) : (C ∨ M) → (C → B) → (M→B) → B:=
(
  fun corm cb mb =>
    match corm with
    | Or.inl c => cb c /- and.left but for or statements-/
    | Or.inr m => mb m/- and.right but for or statements-/
)

#check xyz

theorem orCom (A B : Prop) : (A ∨ B) ↔ (B ∨ A) :=
(
  Iff.intro
  -- backward
  (
    fun porq =>
    (
    Or.inl p => porq p
    )
  )
  -- forward
  (
    _
  )
)
