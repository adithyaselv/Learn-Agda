{-
  My first Proof in Agda
-}

-- define Natural numbers

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

-- Simply defining 1
one : ℕ
one = suc(zero)

two : ℕ
two = suc(suc(zero))

-- define addition of natural numbers

_+_ : ℕ → ℕ → ℕ
zero + n = n
(suc m) + n = suc (m + n)


-- Define equality

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

-- small test for equality

-- oneplusoneistwo : one + one ≡ two
-- oneplusoneistwo = refl

-- Prove n+0 = n
