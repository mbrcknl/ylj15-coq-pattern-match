
data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data Vec (α : Set) : ℕ → Set where
  ◇   :                           Vec α (zero  )
  _,_ : ∀ {m : ℕ} → α → Vec α m → Vec α (succ m)

zip : ∀ {n : ℕ} {α β γ : Set} → (α → β → γ) → Vec α n → Vec β n → Vec γ n
zip f ◇ ◇ = ◇
zip f (x , xt) (y , yt) = f x y , zip f xt yt

