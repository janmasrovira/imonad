import IMonad.Base
import IMonad.IndexedMonad

variable
  {I : Type}

abbrev IndexPreservingFunction (a b : I → Type) : Type :=
  ∀ {i : I}, a i → b i

infixr:35 " ⇒ " => IndexPreservingFunction

def iid {a : I → Type} : a ⇒ a :=
  fun x => x

def icomp {a b c : I → Type} (f : b ⇒ c) (g : a ⇒ b) : a ⇒ c :=
  fun x => f (g x)

infixr:35 " ∘ⁱ " => icomp

class IFunctor {I : Type} (f : (I → Type) → I → Type) : Type 1 where
  imap {a b : I → Type} : (a ⇒ b) → (f a ⇒ f b)

open IFunctor

infixr:100 " <$>ⁱ " => IFunctor.imap

class LawfulIFunctor (f : (I → Type) → I → Type) [IFunctor f] : Prop where
  id_imap {a i} {x : f a i} : imap iid x = x
  comp_imap {a b c i} (g : b ⇒ c) (h : a ⇒ b) (x : f a i)
    : let goh : a ⇒ c := fun {i} => icomp (I := I) (i := i) g h
      goh <$>ⁱ x = g <$>ⁱ (h <$>ⁱ x)

inductive Path {I : Type} (g : (I × I) → Type) : (I × I) → Type where
  | stop {i : I} : Path g (i, i)
  | cons {i j k : I} : g (i, j) → Path g (j, k) → Path g (i, k)

def Path.imap {a b : I × I → Type} (f : a ⇒ b) : Path a ⇒ Path b := fun x =>
    match x with
    | .stop => .stop
    | .cons ij jk => .cons (f ij) (imap f jk)

instance : IFunctor (Path (I := I)) where
  imap := Path.imap

inductive atKey {K : Type} : Type → K → K → Type where
  | m {a : Type} {k : K} : a → atKey a k k

infix:5  " @ₖ "  => atKey

abbrev myList (A : Type) := Path (A @ₖ ((), ())) ((),())

namespace myList

def fromList {A : Type} (l : List A) : myList A := match l with
  | [] => .stop
  | x :: xs => .cons (.m x) (fromList xs)

def toList {A : Type} (l : myList A) : List A := match l with
  | .stop => []
  | .cons (.m x) xs => .cons x (toList xs)

def equiv_list {A : Type} : List A ≃ myList A where
  toFun := fromList
  invFun := toList
  left_inv := by
    simp [Function.LeftInverse]; intro l; induction l
    case nil => simp [toList, fromList]
    case cons x xs h => simp [toList, fromList, h]
  right_inv :=
    let rec go (l : myList A) : fromList (toList l) = l := by
        cases l
        case stop => simp [toList, fromList]
        case cons x xs => cases x; simp [toList, fromList, go xs]
    go

end myList

class IMonad (m : (I → Type) → I → Type) [IFunctor m] : Type 1 where
  iskip {p} : p ⇒ m p
  iextend {p q} : (p ⇒ m q) → (m p ⇒ m q)

export IMonad (iskip iextend)

namespace IMonad

section

variable
  {m : (I → Type) → I → Type}
  [IFunctor m] [IMonad m]
  {p q r : I → Type}
  {i j k : I}
  {A : Type}

abbrev iseq (f : p ⇒ m q) (g : q ⇒ m r) : p ⇒ m r := iextend g ∘ f
abbrev ibind (x : m p i) (g : p ⇒ m q) : m q i := iextend g x

scoped infixl:10 " ?>= " => ibind

abbrev sbind (c : m (A @ₖ j) i) (f : A → m q j) : m q i :=
  c ?>= fun (.m a) => f a

scoped infixl:10 " =>= " => sbind

abbrev At (m : (I → Type) → I → Type) (i j : I) (A : Type) : Type := m (A @ₖ j) i

instance : IxFunctor (At m) where
  imap f := imap (fun ⟨a⟩ => .m (f a))

-- This shows that any Kleisli Triple can be turned into an Indexed Monad
instance : IxMonad (At m) where
  ipure a := iskip (.m a)
  iseq f g := f =>= fun k => IxFunctor.imap k (g ())
  ibind x g := x =>= fun a => g a

end
