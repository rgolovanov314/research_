module Inductions where 

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

-- {-# BUILTIN NATURAL ℕ #-}

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m) ⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm m zero =
  begin
    m + zero
  ≡⟨ +-identityʳ m ⟩
    m
  ≡⟨⟩
    zero + m
  ∎
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc′ zero n p = refl 
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m n p =
  begin 
    m + (n + p)
  ≡⟨ sym (+-assoc m n p)⟩
    (m + n) + p
  ≡⟨ cong (_+ p) (+-comm m n)⟩
    (n + m) + p 
  ≡⟨ (+-assoc n m p)⟩
    n + (m + p)
  ∎

-- written using rewrite
+-swap′ : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap′ m n p rewrite (sym (+-assoc m n p)) | (+-comm m n) | (+-assoc n m p) = refl

*-zeroʳ : ∀ (m : ℕ) → m * zero ≡ zero 
*-zeroʳ zero = 
  begin 
    zero * zero 
  ≡⟨⟩
    zero 
  ∎ 
*-zeroʳ (suc m) = 
  begin 
    (suc m) * zero 
  ≡⟨ (*-zeroʳ m)⟩
    zero 
  ∎

*-identity : ∀ (m : ℕ) → (suc zero) * m ≡ m 
*-identity zero rewrite (*-zeroʳ (suc zero)) = refl
*-identity (suc m) = 
  begin 
    (suc zero) * (suc m) 
  ≡⟨⟩
    (suc m) + (zero * suc m) 
  ≡⟨⟩
    suc m + zero 
  ≡⟨ +-identityʳ (suc m)⟩
    suc m
  ∎

*-distrib-+ : ∀ (p m n : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ p zero n = refl
*-distrib-+ p (suc m) n = 
  begin 
    (suc m + n) * p 
  ≡⟨⟩
    p + (m + n) * p 
  ≡⟨ cong (_+_ p) (*-distrib-+ p m n)⟩
    p + (m * p + n * p)
  ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
    suc m * p + n * p 
  ∎

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = 
  begin 
    (zero * n) * p 
  ≡⟨⟩
    zero * p 
  ≡⟨⟩
    zero 
  ≡⟨⟩
    zero * (n * p)
  ∎
*-assoc (suc zero) n p =
  begin 
    ((suc zero) * n) * p 
  ≡⟨ cong (_* p) (*-identity n) ⟩
    n * p 
  ≡⟨ sym (*-identity (n * p))⟩
    (suc zero) * (n * p)
  ∎
*-assoc (suc m) n p =
  begin
    ((suc m) * n) * p 
  ≡⟨ cong (_* p) (*-distrib-+ n 1 m)⟩
    ((1 * n) + (m * n)) * p 
  ≡⟨ *-distrib-+ p (1 * n) (m * n)⟩
    (1 * n) * p + (m * n) * p
  ≡⟨ cong (_+ (m * n) * p) (*-assoc (suc zero) n p)⟩
    1 * (n * p) + (m * n) * p 
  ≡⟨ cong (1 * (n * p)+_) (*-assoc m n p)⟩ 
    1 * (n * p) + m * (n * p)
  ≡⟨ cong (_+ m * (n * p)) ( *-identity (n * p))⟩
    (n * p) + m * (n * p)
  ≡⟨⟩
    (suc m) * (n * p)
  ∎

{-*-comm : ∀ (m n : ℕ) → m * n ≡ n * m 
*-comm zero n {!   !}
*-comm (suc m) n = {!   !}-}

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m 
*-comm zero n = 
  begin 
    zero * n 
  ≡⟨⟩
    zero 
  ≡⟨ sym ( *-zeroʳ n ) ⟩
    n * zero
  ∎
*-comm m zero = 
  begin 
    m * zero 
  ≡⟨ *-zeroʳ m ⟩
    zero 
  ≡⟨⟩
    zero * m
  ∎
*-comm (suc m) (suc n) =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + (m * (suc n))
  ≡⟨ cong ((suc n) +_) (*-comm m (suc n)) ⟩
    (suc n) + ((suc n) * m)
  ≡⟨⟩
    (suc n) + (m + (n * m))
  ≡⟨ +-swap (suc n) m (n * m) ⟩
    m + ((suc n) + (n * m))
  ≡⟨ sym (+-assoc m (suc n) (n * m)) ⟩
    (m + (suc n)) + (n * m)
  ≡⟨ cong (_+ (n * m)) (+-suc m n) ⟩
    suc (m + n) + (n * m)
  ≡⟨ cong suc (+-assoc m n (n * m)) ⟩
    (suc m) + (n + (n * m))
  ≡⟨ cong (λ m*n → (suc m) + (n + m*n)) (*-comm n m) ⟩
    (suc m) + (n + (m * n))
  ≡⟨⟩
    (suc m) + ((suc m) * n)
  ≡⟨ cong ((suc m) +_) (*-comm ((suc m)) n) ⟩
    (suc m) + (n * (suc m))
  ≡⟨⟩
    (suc n) * (suc m)
  ∎
  
 

+*^ : ∀ (m n p : ℕ) → m ^ (n + p) ≡ (m ^ n) * (m ^ p)
+*^ m zero p = 
  begin 
    m ^ (zero + p)
  ≡⟨⟩
    m ^ p 
  ≡⟨ sym (*-identity (m ^ p))⟩
    (suc zero) * (m ^ p)
  ≡⟨⟩
    (m ^ zero) * (m ^ p)
  ∎
+*^ m (suc n) p =
  begin
    m ^ (suc n + p)
  ≡⟨⟩
    m * m ^ (n + p)
  ≡⟨ cong (_*_ m) (+*^ m n p)⟩ 
    m * ((m ^ n) * (m ^ p))
  ≡⟨ sym (*-assoc m (m ^ n) (m ^ p))⟩
    (m ^ (suc n)) * (m ^ p)
  ∎


{-from (inc b) ≡ suc (from b)
from (inc O) ≡ from (I) ≡ suc zero ≡ suc (from O)

from (inc (m O)) = from (m I) = suc (from (m O))
from (inc (m I)) = from (m I O) = suc (from (m I))

to (from b) ≡ b 
to (from O) = to zero = O 
-- ask 
to (from (m O)) = to (2 * (from m))
-}
