/-!
Streams (possibly infinite) are lazy sequences of values where each element is computed
only when needed. They enable:

1. **Infinite data**: Represent sequences like natural numbers or Fibonacci without bounds.
2. **Productivity**: Compute prefixes on demand, ensuring termination of finite observations.
3. **Composability**: Define `map`, `zipWith`, `filter`, etc., in a modular way.
4. **Stream fusion**: Combine successive operations like `map` and `zipWith` into single traversals.
-/

-- Rename to avoid conflict with preexisting Stream declaration
structure LazyStream (α : Type) where
  head : α
  tail : Unit → LazyStream α

-- Provide a simple Repr instance that displays the head and hides the tail
instance [Repr α] : Repr (LazyStream α) where
  reprPrec s _ := "LazyStream.mk " ++ repr s.head ++ " <tail>"

namespace LazyStream

/-- Construct a lazy stream from a head and a (lazy) tail thunk. -/
def cons {α : Type} (hd : α) (tl : Unit → LazyStream α) : LazyStream α :=
  ⟨hd, tl⟩

/-- Repeat the same value forever. -/
unsafe def repeatStream {α : Type} (x : α) : LazyStream α :=
  cons x (fun _ => repeatStream x)

/-- Natural numbers from `n` upward: n, n+1, n+2, … -/
unsafe def fromNat (n : Nat) : LazyStream Nat :=
  cons n (fun _ => fromNat (n + 1))

/-- Map a function over a stream lazily. -/
unsafe def map {α β : Type} (f : α → β) : LazyStream α → LazyStream β
  | ⟨hd, tl⟩ => cons (f hd) (fun _ => map f (tl ()))

/-- Zip two streams with a binary function. -/
unsafe def zipWith {α β γ : Type} (f : α → β → γ)
    : LazyStream α → LazyStream β → LazyStream γ
  | ⟨h1, t1⟩, ⟨h2, t2⟩ =>
    cons (f h1 h2) (fun _ => zipWith f (t1 ()) (t2 ()))

/-- Take the first `n` elements of a stream as a list. -/
partial def take {α : Type} : Nat → LazyStream α → List α
  | 0, _        => []
  | n+1, ⟨h, t⟩ => h :: take n (t ())

/-- Fuse two maps into one traversal: map f ∘ map g = map (f ∘ g) -/
unsafe def fuseMap {α β γ : Type} (f : β → γ) (g : α → β)
    : LazyStream α → LazyStream γ
  | ⟨hd, tl⟩ => cons (f (g hd)) (fun _ => fuseMap f g (tl ()))

end LazyStream

open LazyStream

-- Some canonical streams
unsafe def ones : LazyStream Nat := repeatStream 1
unsafe def nats : LazyStream Nat := fromNat 0

/-- Fibonacci numbers as a lazy stream: 0, 1, 1, 2, 3, 5, … -/
unsafe def fibAux (a b : Nat) : LazyStream Nat :=
  cons a (fun _ => fibAux b (a + b))
unsafe def fibs : LazyStream Nat := fibAux 0 1

/-! ### Examples -/

/-- Example 1: First five natural numbers -/
unsafe def example1 : List Nat := take 5 nats

/-- Example 2: First ten Fibonacci numbers -/
unsafe def example2 : List Nat := take 10 fibs

/-- Example 3: Squares of the first seven naturals -/
unsafe def example3 : List Nat := take 7 (map (fun x => x * x) nats)

/-- Example 4: Pairwise sums of naturals and ones -/
unsafe def example4 : List Nat := take 5 (zipWith (· + ·) nats ones)

/-! ### Stream Fusion Examples -/

/-- Example 5: Fuse two maps (square then succ) using `fuseMap`. -/
unsafe def exampleFusion1 : List Nat :=
  take 5 (fuseMap Nat.succ (fun x => x * x) nats)

/-- Example 6: Sequential maps: map succ ∘ map square -/
unsafe def exampleFusion2 : List Nat :=
  take 5 (map Nat.succ (map (fun x => x * x) nats))

/-- Demonstrate that fusion yields the same result as sequential maps -/
unsafe def demonstrateFusion : IO Unit := do
  let f1 := exampleFusion1
  let f2 := exampleFusion2
  IO.println s!"Fused result:     {f1}"
  IO.println s!"Sequential result: {f2}"

#eval example1
#eval example2
#eval example3
#eval example4
#eval demonstrateFusion
