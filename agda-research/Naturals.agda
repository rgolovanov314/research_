module Naturals where 

data ℕ : Set where 
    zero : ℕ
    suc : ℕ → ℕ

seven : ℕ
seven = suc (suc (suc (suc (suc (suc (suc zero))))))

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq 
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n 
(suc m) + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩    -- is shorthand for
    (suc (suc zero)) + (suc (suc (suc zero)))
  ≡⟨⟩    -- inductive case
    suc ((suc zero) + (suc (suc (suc zero))))
  ≡⟨⟩    -- inductive case
    suc (suc (zero + (suc (suc (suc zero)))))
  ≡⟨⟩    -- base case
    suc (suc (suc (suc (suc zero))))
  ≡⟨⟩    -- is longhand for
    5
  ∎

_ : 2 + 3 ≡ 5
_ =
  begin
    2 + 3
  ≡⟨⟩
    suc (1 + 3)
  ≡⟨⟩
    suc (suc (0 + 3))
  ≡⟨⟩
    suc (suc 3)
  ≡⟨⟩
    5
  ∎

_ : 3 + 4 ≡ 7 
_ = 
    begin 
        3 + 4 
    ≡⟨⟩ 
        suc (2 + 4)
    ≡⟨⟩ 
        suc (suc (1 + 4))
    ≡⟨⟩ 
        suc (suc (suc (0 + 4)))
    ≡⟨⟩ 
        suc (suc (suc 4))
    ≡⟨⟩
        7
    ∎

_*_ : ℕ → ℕ → ℕ
zero * n = zero 
(suc m) * n = n + (m * n)

_ : 3 * 4 ≡ 12 
_ = 
    begin 
        3 * 4 
    ≡⟨⟩
        3 + (3 * 3)
    ≡⟨⟩
        3 + (3 + (2 * 3))
    ≡⟨⟩
        3 + (3 + (3 + (1 * 3)))
    ≡⟨⟩
        3 + (3 + (3 + (3 + (0 * 3))))
    ≡⟨⟩
        3 + (3 + (3 + (3 + 0)))
    ≡⟨⟩
        12
    ∎

_^_ : ℕ → ℕ → ℕ
zero ^ n = zero 
n ^ zero = 1
m ^ (suc n) = m * (m ^ n)

_ : 3 ^ 4 ≡ 81 
_ = refl

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

infixl 6  _+_  _∸_
infixl 7  _*_

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _∸_ #-}

data Bin : Set where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

inc : Bin → Bin 
inc (⟨⟩) = ⟨⟩
inc (⟨⟩ O) = ⟨⟩ I
inc (⟨⟩ I) = ⟨⟩ I O
inc (m O) = m I 
inc (m I) = (inc m) O

_ : inc (⟨⟩ I O I I) ≡ ⟨⟩ I I O O
_ = refl

to : ℕ → Bin 
to zero = ⟨⟩ O 
to (suc n) = inc (to n)

from : Bin → ℕ 
from (⟨⟩) = 0
from (⟨⟩ O) = 0
from (⟨⟩ I) = 1
from (m O) = 2 * (from m)
from (m I) = 2 * (from m) + 1

_ : (⟨⟩ I I) ≡ (to 3)
_ = refl

_ : 5 ≡ (from (⟨⟩ I O I))
_ = refl