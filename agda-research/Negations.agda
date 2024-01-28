module Negations where 

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import plfa.part1.Isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

-- evidence ¬ A holds is of the form λ{ x → N } where N is a term of type ⊥ 
-- containing as a free variable x of type A
-- evidence that A holds → evidence that ⊥ holds

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

-- ¬ A and A holding is a contradition, so we conclude that ⊥ holds

infix 3 ¬_

-- only have intuitionistic logic, not classical. i.e. dont know a priori 
-- A = not (not A). only know A → not (not A)
¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ{¬x → ¬x x}

-- alternative to above (no lambda notation)

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

-- can show not (not (not A)) implies not A even tho cant show
-- ¬¬ A = A

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)  

-- let x be evidence of A. we know from intro that A → ¬¬A .
-- then from ¬¬¬ A and ¬¬A we have contradiction, so ¬A

contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ()
-- can use absurd pattern, since it matches all possible evidence of type zero = suc m
-- (there is none)

-- can view negation as raising to 0th power

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x x))

infix 4 _<_
data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
      ------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      -------------
    → suc m < suc n

<-irreflexive : ∀ (n : ℕ) → ¬ (n < n)
<-irreflexive zero ()
<-irreflexive (suc n) (s<s n<n) = <-irreflexive n n<n

infix 4 _≮_
_≮_ : ∀ (m n : ℕ) → Set
m ≮ n = ¬ (m < n)

sm≡sn : ∀ { m n : ℕ} → suc m ≡ suc n → m ≡ n 
sm≡sn refl = refl 

sm≢sn : ∀ {m n : ℕ} → m ≢ n → suc m ≢ suc n 
sm≢sn m≢n = λ{ smn → m≢n (sm≡sn smn)}

sm≮sn : ∀ {m n : ℕ} → m ≮ n → suc m ≮ suc n 
sm≮sn m≮n = λ{ (s<s m<n) → m≮n m<n}

trichotomy : ∀ (m n : ℕ)
    → ( m < n × m ≢ n × n ≮ m )
    ⊎ ( m ≮ n × m ≡ n × n ≮ m )
    ⊎ ( m ≮ n × m ≢ n × n < m )
trichotomy zero zero    = inj₂ (inj₁  ((λ()), ( refl , (λ()))))
trichotomy zero (suc n) = inj₁ ( z<s , ( (λ()), (λ()) ) )
trichotomy (suc m) zero = inj₂ (inj₂ ( (λ()), ( (λ()) , z<s)))
trichotomy (suc m) (suc n) with trichotomy m n 
...                             | inj₁ ( m<n , ( m≢n , n≮m ) ) = 
                                  inj₁ ( s<s m<n , ( sm≢sn m≢n , sm≮sn n≮m))
...                             | inj₂ ( inj₁ ( m≮n , ( refl , n≮m ) )) = 
                                  inj₂ ( inj₁ ( sm≮sn m≮n , ( refl , sm≮sn n≮m ) ))
...                             | inj₂ (inj₂ ( m≮n , ( m≢n , n<m ) ))  = 
                                  inj₂ (inj₂ ( sm≮sn m≮n , ( sm≢sn m≢n , s<s n<m ) ))                          


postulate
  em : ∀ {A : Set} → A ⊎ ¬ A

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable = λ k → k (inj₂ (λ x → k (inj₁ x)))
