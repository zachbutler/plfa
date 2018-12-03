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
n ^ zero  = suc zerox
n ^ suc m = n * (n ^ m)


_∸_ : ℕ → ℕ → ℕ
m         ∸ zero     = m
zero      ∸ (suc n)  = zero
(suc m)   ∸ (suc n)  = m ∸ n
