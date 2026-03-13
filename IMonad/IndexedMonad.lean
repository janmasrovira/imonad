abbrev IndexedType (I : Type) := I → I → Type → Type

class IxFunctor {I : Type} (f : IndexedType I) : Type 1 where
  imap {i j α β} (h : α → β) : f i j α → f i j β

class IxApplicative {I : Type} (f : IndexedType I) extends IxFunctor f where
  ipure {i α} : α → f i i α
  iseq {i j k α β} : f i j (α → β) → (Unit → f j k α) → f i k β

class IxMonad {I : Type} (m : IndexedType I) extends IxApplicative m where
  ibind {i j k α β} : m i j α → (α → m j k β) → m i k β
