module _ where

data ⊥ : Set where
⊥-elim : {A : Set} → ⊥ → A
⊥-elim ()

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat hiding (_+_) renaming (Nat to ℕ)
open import Agda.Builtin.String

cong : {A B : Set} (f : A → B) {x y : A} (eq : x ≡ y) → f x ≡ f y
cong f refl = refl

sym : {A : Set} {x y : A} (eq : x ≡ y) → y ≡ x
sym refl = refl

data List (A : Set) : Set where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A
infixr 5 _∷_

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B fst

data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

over-inr : {A B1 B2 : Set} (f : B1 → B2) (e : A + B1) → A + B2
over-inr f (inl x) = inl x
over-inr f (inr x) = inr (f x)

data Dec {A : Set} (x y : A) : Set where
  eq : x ≡ y → Dec x y
  neq : (x ≡ y → ⊥) → Dec x y

_>>=_ : {A B C : Set} → A + B → (B → A + C) → A + C
inl x >>= f = inl x
inr x >>= f = f x

dec-string : (x y : String) → Dec x y
dec-string x y with primStringEquality x y
dec-string x y | false = neq (⊥-elim trustme) where postulate trustme : ⊥
dec-string x y | true = eq primTrustMe where open import Agda.Builtin.TrustMe

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : {x : A} {xs : List A} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

data Any {A : Set} (P : A → Set) : List A → Set where
  zero : {x : A} {xs : List A} → Any P (x ∷ xs)
  suc : {x : A} {xs : List A} (p : Any P xs) → Any P (x ∷ xs)

_∈_ : {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

data Type : Set where
  Nat : Type
  _⇒_ : (A B : Type) → Type

injl⇒ : {A B C D : Type} → (A ⇒ B) ≡ (C ⇒ D) -> A ≡ C
injl⇒ refl = refl

injr⇒ : {A B C D : Type} → (A ⇒ B) ≡ (C ⇒ D) -> B ≡ D
injr⇒ refl = refl

dec-type : (S T : Type) → Dec S T
dec-type Nat Nat = eq refl
dec-type Nat (T ⇒ T₁) = neq (λ ())
dec-type (S ⇒ S₁) Nat = neq (λ ())
dec-type (S ⇒ T) (P ⇒ Q) with dec-type S P
dec-type (S ⇒ T) (P ⇒ Q) | eq p rewrite p with dec-type T Q
dec-type (S ⇒ T) (P ⇒ Q) | eq p | eq q rewrite q = eq refl
dec-type (S ⇒ T) (P ⇒ Q) | eq p | neq q = neq λ r → q (injr⇒ r)
dec-type (S ⇒ T) (P ⇒ Q) | neq p = neq λ r → p (injl⇒ r)

data TermU : Set where
  var : (name : String) → TermU
  lit : ℕ → TermU
  suc : (num : TermU) → TermU
  lam : (name : String) (T : Type) (body : TermU) → TermU
  app : (fun arg : TermU) → TermU

data TermT (Γ : List (String × Type)) : Type → Set where
  var : (name : String) (T : Type) (valid : (name , T) ∈ Γ) → TermT Γ T
  lit : ℕ → TermT Γ Nat
  suc : (num : TermT Γ Nat) → TermT Γ Nat
  lam : (name : String) (S : Type) {T : Type} (body : TermT (name , S ∷ Γ) T) → TermT Γ T
  app : {S T : Type} (fun : TermT Γ (S ⇒ T)) (arg : TermT Γ S) → TermT Γ T

forgetTypes : {Γ : List (String × Type)} {T : Type} → TermT Γ T → TermU
forgetTypes (var name T valid) = var name
forgetTypes (lit x) = lit x
forgetTypes (suc t) = suc (forgetTypes t)
forgetTypes (lam name S b) = lam name S (forgetTypes b)
forgetTypes (app f x) = app (forgetTypes f) (forgetTypes x)

data Checked (Γ : List (String × Type)) : TermU → Set where
  ok : {u : TermU} (T : Type) (t : TermT Γ T) (same : forgetTypes t ≡ u) → Checked Γ u

checkSuc : ∀ {Γ u} → Checked Γ u → String + Checked Γ (suc u)
checkSuc (ok Nat t same) = inr (ok Nat (suc t) (cong suc same))
checkSuc (ok (T ⇒ T₁) t same) = inl "Can't do suc of function"

checkLam : ∀ name T {Γ u} → Checked ((name , T) ∷ Γ) u → String + Checked Γ (lam name T u)
checkLam name S (ok T t same) = inr (ok T (lam name S t) (cong (lam name S) same))

checkApp : ∀ {Γ f x} → Checked Γ f → Checked Γ x → String + Checked Γ (app f x)
checkApp (ok Nat tf same-f) (ok TX tx same-x) = inl "Can't apply a Nat to an argument"
checkApp (ok (S ⇒ T) tf same-f) (ok TX tx same-x) with dec-type S TX
checkApp (ok (S ⇒ T) tf refl) (ok .S tx refl) | eq refl = inr (ok T (app tf tx) refl)
checkApp (ok (S ⇒ T) tf same-f) (ok TX tx same-x) | neq x = inl "Arg type does not match function type"

weakenVar : ∀ {n v T Γ} → Checked Γ (var n) → Checked ((v , T) ∷ Γ) (var n)
weakenVar (ok T (var name .T valid) same) = ok T (var name T (suc valid)) same
weakenVar (ok .Nat (lit x) ())
weakenVar (ok .Nat (suc t) ())
weakenVar (ok T (lam name S t) ())
weakenVar (ok T (app t t₁) ())

lookupVar : ∀ name Γ → String + Checked Γ (var name)
lookupVar n [] = inl (primStringAppend "Var not found: " n)
lookupVar n ((v , T) ∷ Γ) with dec-string n v
lookupVar n ((v , T) ∷ Γ) | eq p = inr (ok T (var n T zero) refl)
lookupVar n ((v , T) ∷ Γ) | neq p = lookupVar n Γ >>= λ c → inr (weakenVar c)

typeCheck : (Γ : List (String × Type)) (u : TermU) → String + Checked Γ u
typeCheck Γ (var name) = lookupVar name Γ
typeCheck Γ (lit x) = inr (ok Nat (lit x) refl)
typeCheck Γ (suc u) = typeCheck Γ u >>= checkSuc
typeCheck Γ (lam name T u) = typeCheck (name , T ∷ Γ) u >>= checkLam name T
typeCheck Γ (app f x) = 
  typeCheck Γ f >>= λ tf →
  typeCheck Γ x >>= λ tx →
  checkApp tf tx
