rewrite[ctx:_∣via:_∣proof:_] : 
rewrite[ctx: ctx ∣via: eq ∣proof: p ] = subst ctx (sym eq) p 

syntax subst (λ ◆ → ctx) eq proof = ◆ ⟦ ctx ≣ eq ∶- proof ⟧

