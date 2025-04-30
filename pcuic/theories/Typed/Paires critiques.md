

# Les paires critiques

D'abord, liste des relations en jeu :
- ≡>β
- ≡>η
- ≡>ι
- ≡>proj
- ≡>ηproj
- ≡>decast
- ≡α

Toutes des simulations, avec la diagonale pour les relations diagonales, sauf
- ≡>η / ≡>η (pentagone générant ≡α)
- ≡α / ≡α (transitivité)

Liste des rédexes :
- β
  ```
  (λ (x : A₀), t : B₀){Π (x : A₀'), B₀'} u ≡>R (λ (x : A₁), t' : B₁){Π (x : A₁'), B₁'} u' (terme-à-terme)
            Γ ⊢ Π (x : A₀), B₀ ≤T Π (x : A₀'), B₀'
            Γ ⊢ Π (x : A₁), B₁ ≤T Π (x : A₁'), B₁' (hypothèses inclues dans la réduction ci-dessus)
  -------------------------------------------------------------------------------------
  (λ (x : A₀), t : B₀){Π (x : A₀'), B₀'} u ≡>β (t' : B₁')[x := (u' : A₁')]
                      ▹ B₀'[x := (u : A₀')] | B₁'[x := (u' : A₁')]
  ```
  (injectivité des produits requise pour le typage)
- η
  ```
    t₀ ≡>R t₁ : Π (x : A₀), B₀ | Π (x : A₁), B₁
                Π (x : A₀), B₀ ≡>R Π (x : A₁), B₁ : □ | □ (terme-à-terme)
            Γ ⊢ Π (x : A₀), B₀ ≤T T₀
            Γ ⊢ Π (x : A₁), B₁ ≤T T₁
  -------------------------------------------------------------------------------------
    t₀ ≡>η λ (x : A₁), ((↑t₁){Π (x : A₁), B₁} x) : B₁ : T₀ | T₁
  ```
  (transitivité de la conversion de type requise pour le typage)
- ι
  ```
  case (C(args₀) : Ind p₀) return P₀ with brs₀ ≡>R case (C(args₁) : Ind p₁) return P₁ with brs₁ (terme-à-terme)
            Γ ⊢ typeof C(args₀) ≤T Ind p₀
            Γ ⊢ typeof C(args₁) ≤T Ind p₁ (hypothèses inclues dans la réduction ci-dessus)
  -------------------------------------------------------------------------------------
  case (C(args₀) : Ind p₀) return P₀ with brs₀ ≡>ι (br₁.[C] [Γbr'.[C] := (args₁ : _)] : P[ind := p₁, C(args₁)])
                      ▹ P[ind := p₀, C(args₀)] | P[ind := p₁, C(args₁)]
  ```
  (injectivité des inductifs requise pour le typage)
- proj
  ```
  proji{Ind p₀} C(p₀', args₀) ≡>R proji{Ind p₁} C(p₁', args₁) (terme-à-terme)
            Γ ⊢ Ind p₀' ≤T Ind p₀
            Γ ⊢ Ind p₁' ≤T Ind p₁ (hypothèses inclues dans la réduction ci-dessus)
  -------------------------------------------------------------------------------------
  proji{Ind p₀} C(p₀', args₀) ≡>proj (arg₁i : Γind.[i]{p₁})
                 ▹ Γind.[i]{p₀} | Γind.[i]{p₁}
  ```
  (injectivité des inductifs requise pour le typage)
- ηproj
  ```
    t₀ ≡>R t₁ : Ind p₀ | Ind p₁
                Ind p₀ ≡>R Ind p₁ : □ | □ (terme-à-terme)
            Γ ⊢ Ind p₀ ≤T T₀
            Γ ⊢ Ind p₁ ≤T T₁
  -------------------------------------------------------------------------------------
    t₀ ≡>ηproj C(p₁, proji{Ind p₁} t₁) : T₀ | T₁
  ```
  (transitivité de la conversion de type requise pour le typage)
- decast
  ```
    (c₀ : ty₀) ≡> (c₁ : ty₁) (terme-à-terme)
            Γ ⊢ ty₀ ≤T T₀
            Γ ⊢ ty₁ ≤T T₁
  -------------------------------------------------------------------------------------
    (c₀ : ty₀) ≡>decast c₁ : T₀ | T₁
  ```
  (transitivité de la conversion de type requise pour le typage)


Listons toutes les paires critiques :
- β / η :
  ```
  (λ (x : A₀), t₀ : B₀){Π (x : A₀'), B₀'} u₀ ≡>β (t₁ : B₁')[x := (u₁ : A₁')] ▹ B₀'[x := (u₀ : A₀')] | B₁'[x := (u₁ : A₁')]
  ⇓η
  (λ (x : A₂''), (λ (x : A₂), ((↑t₂){Π (x : A₂), B₂} x) : B₂){Π (x : A₂'', B₂'')} x : B₂''){Π (x : A₂'), B₂'} u₂
  Γ ⊢ Π (x : A₀), B₀ ≤T Π (x : A₀'), B₀'
  Γ ⊢ Π (x : A₁), B₁ ≤T Π (x : A₁'), B₁'
  Γ ⊢ Π (x : A₀), B₀ ≤T Π (x : A₀''), B₀''
  Γ ⊢ Π (x : A₀''), B₀'' ≤T Π (x : A₀'), B₀'
  Γ ⊢ Π (x : A₂), B₂ ≤T Π (x : A₂'), B₂'
  Γ ⊢ Π (x : A₂''), B₂'' ≤T Π (x : A₂'), B₂'
  (théoriquement il peut y avoir plus d'une η-expansion ici)
  ```
  (se clot sans souci présenté comme ça)

- β / ηproj
  ```
  (λ (x : A₀), t₀ : B₀){Π (x : A₀'), B₀'} u₀ ≡>β (t₁' : B₁')[x := (u₁' : A₁')] ▹ B₀'[x := (u₀ : A₀')] | B₁'[x := (u₁ : A₁')]
  ⇓ηproj
  (C (p₂, proji{Ind p₂} (λ (x : A₂), t₂ : B₂))){Π (x : A₂'), B₂'} u₂
  Γ ⊢ Π (x : A₀), B₀ ≤T Π (x : A₀'), B₀'
  Γ ⊢ Π (x : A₁), B₁ ≤T Π (x : A₁'), B₁'
  Γ ⊢ Ind p₀ ≤T Π (x : A₀'), B₀'
  Γ ⊢ Π (x : A₀), B₀ ≤T Ind p₀
  Γ ⊢ Ind p₂ ≤T Π (x : A₂'), B₂'
  Γ ⊢ Π (x : A₂), B₂ ≤T Ind p₂
  (théoriquement il peut y avoir plus d'une η-expansion ici)
  ```
  (se clot par non-confusion des constructeurs de type)

- ι / η :
  ```
  (case (C(args₀) : Ind p₀) return P₀ with brs₀ ≡>ι (brs₁.[C] [Γbrs₁.[i] := (args₁ : Γbrs₁.[i])] : P[ind := p₁, C(args₁)]))
  ⇓η
  case ((λ (x : A₂), C(↑ args₂)){Π (x : A₂), B₂} x : Ind p₂) return P₂ with brs₂
  Γ ⊢ typeof C(args₀) ≤T Ind p₀
  Γ ⊢ typeof C(args₁) ≤T Ind p₁
  Γ ⊢ Π (x : A₀), B₀ ≤T Ind p₀
  Γ ⊢ typeof C(args₀) ≤T Π (x : A₀), B₀
  Γ ⊢ Π (x : A₂), B₂ ≤T Ind p₂
  Γ ⊢ typeof C(args₂) ≤T Π (x : A₂'), B₂'
  (théoriquement il peut y avoir plus d'une η-expansion ici)
  ```
  (se clot par non-confusion des constructeurs de type)

- ι / ηproj
  ```
  (case (C(args₀) : Ind p₀) return P₀ with brs₀ ≡>ι (brs₁.[C] [Γbrs₁.[i] := (args₁ : Γbrs₁.[i])] : P[ind := p₁, C(args₁)]))
  ⇓ηproj
  case (C'(p₂', proji{Ind' p₂'} C(args₂)) : Ind p₂) return P₂ with brs₂
  Γ ⊢ typeof C(args₀) ≤T Ind p₀
  Γ ⊢ typeof C(args₁) ≤T Ind p₁
  Γ ⊢ Ind' p₀' ≤T Ind p₀
  Γ ⊢ typeof C(args₀) ≤T Ind p₀'
  Γ ⊢ Ind p₂' ≤T Ind p₂
  Γ ⊢ typeof C(args₂) ≤T Ind p₂'
  (théoriquement il peut y avoir plus d'une η-expansion ici)
  ```
  (se clot par non-confusion des constructeurs de type)
- proj / η :
  ```
  (proji{Ind p₀'} C(p₀, args₀) ≡>proj (args₁.[i] : Γind.[i]{p₁'}))
  ⇓η
  proji{Ind p₂'} (λ (x : A₂), C(↑p₂, ↑args₂){Π (x : A₂), B₂} x)
  Γ ⊢ Ind p₀ ≤T Ind p₀'
  Γ ⊢ Ind p₁ ≤T Ind p₁'
  Γ ⊢ Π (x : A₀), B₀ ≤T Ind p₀'
  Γ ⊢ Ind p₀ ≤T Π (x : A₀), B₀
  Γ ⊢ Π (x : A₂), B₂ ≤T Ind p₂'
  Γ ⊢ Ind p₂ ≤T Π (x : A₂'), B₂'
  (théoriquement il peut y avoir plus d'une η-expansion ici)
  ```
  (se clot par non-confusion des constructeurs de type)

- proj / ηproj
  ```
  (proji{Ind p₀'} C(p₀, args₀) ≡>proj (args₁.[i] : Γind.[i]{p₁'}))
  ⇓ηproj
  proji{Ind p₂'} C'(p₂''.., proji{Ind' p₂''} C(args₂))
  Γ ⊢ Ind p₀ ≤T Ind p₀'
  Γ ⊢ Ind p₁ ≤T Ind p₁'
  Γ ⊢ Ind' p₀'' ≤T Ind p₀'
  Γ ⊢ Ind p₀ ≤T Ind' p₀''
  Γ ⊢ Ind' p₂'' ≤T Ind p₂
  Γ ⊢ Ind p₂ ≤T Ind' p₂''
  (théoriquement il peut y avoir plus d'une η-expansion ici)
  ```
  (si Ind = Ind', se clot sans souci présenté comme ça, sinon, se clot par non-confusion des constructeurs de type)

- η / η
  ```
  With tᵢ ▹ Tᵢ₀
  t₀ ≡>η λ (x : A₁), ((↑t₁){Π (x : A₁), B₁} x : B₁) : T₀ | T₁
  ⇓η
  λ (x : A₂), ((↑t₂){Π (x : A₂), B₂} x : B₂) : T₀ | T₂
  Γ ⊢ T₀₀ ≤T Π (x : A₀), B₀ ≤T T₀
  Γ ⊢ T₀₀ ≤T Π (x : A₀'), B₀' ≤T T₀
  Γ ⊢ T₁₀ ≤T Π (x : A₁), B₁ ≤T T₁
  Γ ⊢ T₂₀ ≤T Π (x : A₂), B₂ ≤T T₂
  ```
  (plus facile à résoudre sans cumulativité, où on peut directement réappliquer η de chaque côté avec les annotations de l'autre réduction)
  (avec cumulativité, besoin de passer par ≡α qui compare de manière relachée les annotations)

- ηproj / ηproj
  ```
  With tᵢ ▹ Tᵢ₀
  t₀ ≡>ηproj C (p₁, proji{Ind p₁} t₁) : T₀ | T₁
  ⇓ηproj
  C (p₂, proji{Ind' p₂} t₂) : T₀ | T₂
  Γ ⊢ T₀₀ ≤T Ind p₀ ≤T T₀
  Γ ⊢ T₀₀ ≤T Ind' p₀' ≤T T₀
  Γ ⊢ T₁₀ ≤T Ind p₁ ≤T T₁
  Γ ⊢ T₂₀ ≤T Ind' p₂ ≤T T₂
  ```
  (si Ind ≠ Ind', clore par non-confusion des constructeurs de types, formulation indirecte)
  (plus facile à résoudre sans cumulativité, où on peut directement réappliquer η de chaque côté avec les annotations de l'autre réduction)
  (avec cumulativité, besoin de passer par ≡α qui compare de manière relachée les annotations)
