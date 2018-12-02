module plfa.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡<>_; _≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)

(m + n) + p ≡ m + (n + p)

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
  begin
    (3 + 4) + 5
  ≡<>
    7 + 5
  ≡<>
    12
  ≡<>
    3 + 9
  ≡<>
    3 + (4 + 5)
  ∎
