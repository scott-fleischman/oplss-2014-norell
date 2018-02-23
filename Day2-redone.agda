module _ where

data 𝔹 : Set where
  true false : 𝔹

if_then_else_ : {A : Set} (b : 𝔹) (t f : A) → A
if true then t else f = t
if false then t else f = f

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

_+_ : (m n : ℕ) → ℕ
zero + n = n
suc m + n = suc (m + n)

data List (A : Set) : Set where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A
infixr 5 _∷_

infixl 3 _∈_
data _∈_ {A : Set} (x : A) : List A → Set where
  zero : {xs : List A} → x ∈ x ∷ xs
  suc : {y : A} {xs : List A} (p : x ∈ xs) → x ∈ y ∷ xs

lookup : {A : Set} {x : A} {xs : List A} (i : x ∈ xs) → A
lookup {x = x} zero = x
lookup (suc i) = lookup i

data All {A : Set} (P : A → Set) : List A → Set where
  [] : All P []
  _∷_ : {xs : List A} {x : A} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

lookup-all : {A : Set} {x : A} {xs : List A} {P : A → Set} (i : x ∈ xs) (a : All P xs) → P x
lookup-all zero (px ∷ pxs) = px
lookup-all (suc i) (px ∷ pxs) = lookup-all i pxs

data Type : Set where
  nat bool : Type

data Expr (Γ : List Type) : Type → Set where
  var : {x : Type} (i : x ∈ Γ) → Expr Γ x
  value : (n : ℕ) → Expr Γ nat
  true false : Expr Γ bool
  add : (m n : Expr Γ nat) → Expr Γ nat
  if : {r : Type} (b : Expr Γ bool) (t f : Expr Γ r) → Expr Γ r

Value : Type → Set
Value nat = ℕ
Value bool = 𝔹

eval : {t : Type} {Γ : List Type} (env : All Value Γ) (expr : Expr Γ t) → Value t
eval env (var i) = lookup-all i env
eval env (value n) = n
eval env true = true
eval env false = false
eval env (add m n) = eval env m + eval env n
eval env (if b t f) = if (eval env b) then (eval env t) else (eval env f)

module Test where
  open import Agda.Builtin.Equality

  Γ : List Type
  Γ = bool ∷ bool ∷ nat ∷ []

  env : All Value Γ
  env = true ∷ false ∷ 21 ∷ []

  p1 : eval env (add (value 10) (if (var zero) (var (suc (suc zero))) (value 6))) ≡ 31
  p1 = refl
