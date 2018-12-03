

data ℕ : Set where
  zero : ℕ
  suc  : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero + n = n
suc m + n = suc (m + n)


_*_ : ℕ -> ℕ -> ℕ
zero * n    = zero
(suc m) * n = n + (m * n)


  {- Define exponentiation, given by the following:
    n ^ 0       = 1
    n ^ (1 + m) = n * (n ^ m)) -}

_^_ : ℕ → ℕ → ℕ
n ^ zero  = suc zero
n ^ suc m = n * (n ^ m)

{-# BUILTIN NATURAL ℕ #-}

{- _ = 
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * 3 * (3 ^ 2)
  ≡⟨⟩
    3 * 3 * 3 * (3 ^ 1)
  ≡⟨⟩
    3 * 3 * 3 * 3 * (3 ^ 0)
  ≡⟨⟩
    3 * 3 * 3 * 3 * 1
  ≡⟨⟩
    81
  ∎ -}


_∸_ : ℕ → ℕ → ℕ
m         ∸ zero     = m
zero      ∸ (suc n)  = zero
(suc m)   ∸ (suc n)  = m ∸ n
