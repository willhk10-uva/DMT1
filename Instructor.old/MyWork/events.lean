

/- @@@
EVENT TYPE AND ARG TYPE

Global dictionary of event types, each with the type
of its argument. Define one such event type common to
all event entries of a specific kind appearing in any
interface of any module in the system.
@@@ -/

inductive EventType
| starting
| finished

/- @@@
From EventType value to corresponding payload type.
Note: the dot notation refers to the constructor names.
The argument types here are just for illutration.
@@@ -/
def EventArgType : EventType → Type
| .starting => Nat
| .finished => String


/- @@@
TOSTRING INSTANCES

ToString instances for payload types. THE Odd constructions
are to convince Lean that everything typechecks
@@@ -/
instance : ToString EventType where
  toString
    | .starting => "Starting"
    | .finished => "Finished"

instance : ToString (EventArgType .starting) :=
  { toString := ((inferInstance : ToString Nat).toString) }     -- Uses Nat's ToString

instance : ToString (EventArgType .finished) :=
  { toString := ((inferInstance : ToString String).toString) }  -- Uses String's ToString

/- @@@
EVENTINSTANCE: Actual-parameter-carrying event instance
for an event of type EventType.
@@@ -/
structure EventInstance (t : EventType) where
  payload : EventArgType t


/- @@@
HANDLER

Family of event handlers, one per EventType value, t.
Takes an event type and instance argumentsand returns:
an interactive computation. QUESTION: CAN ONE OF THOSE
ANNOUNCE AN EVENT?
@@@ -/
def Handler (t : EventType) := EventInstance t → IO Unit


/- @@@
The type of a HANDLER REGISTRY for events of type EventType t.
Nothing here precludes having multiple registries for an eventType.
@@@-/
def Registry (t : EventType) := List (Handler t)

/- @@@
REGISTER a handler for an event of type EventType t with a given registry
@@@ -/
def addHandler (t : EventType) (reg : Registry t) (h : Handler t) : Registry t :=
  h :: reg

/- @@@
ANNOUNCE
Function to announce an event to all handlers.
Here t and reg are independent; maybe that's not right.
Interesting design.
@@@ -/
def announce (t : EventType) (reg : Registry t) (e : EventInstance t) : IO Unit :=
  reg.foldl (λ acc h => acc *> h e) (pure ())


/- @@@
EXAMPLE
@@@ -/

-- Log event handler with string
def logHandler {t : EventType} [ToString (EventArgType t)] : Handler t :=
  λ e => IO.println s!"Received event of type: {t} with payload {e.payload}"

-- Double event handler. Nat arg. Convinces Lean it typechecks.
def doubleHandler : Handler .starting
| { payload := (n : Nat) } => IO.println s!"Double the payload: {n * 2}"

/- @@@
Demo
@@@ -/
def main : IO Unit := do
  let regA := addHandler .starting [] logHandler
  let regA := addHandler .starting regA doubleHandler
  let regB := addHandler .finished [] logHandler

  -- Explicit event creation with payload type annotation
  let eventA : EventInstance .starting := { payload := (42 : Nat) }
  let eventB : EventInstance .finished := { payload := ("Hello" : String) }

  announce .starting regA eventA
  announce .finished regB eventB

#eval main
