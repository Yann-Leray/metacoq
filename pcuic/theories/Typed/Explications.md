# Objectif final : Typechecking décidable

On veut décider de ≅ qui a :
- congruence syntaxique (inclus : univers, effacement des cast)
- règles de réduction et η
- réflexif (sur les biens-typés)
- symétrique
- transitif
- conversion sur les types = lui-même

Pour cela, on veut utiliser la méthode faite par un compilateur, mais en l'autorisant à arrêter les réductions (pour ne pas dépendre de la terminaison du système)

On appelle cette relation ≡ :
- stable par anti-réduction de chaque côté
- stable par anti-η-expansion de chaque côté
- congruence syntaxique (inclus : univers, effacement des cast) (donc réflexivité sur les biens-typés)
- conversion sur les types = lui-même


La correction de cette méthode est évidente (toutes les règles sont admissibles), il ne reste à montrer que la complétude.

Claim : seule la transitivité pose un vrai problème


# Nouvel objectif principal : prouver la transitivité de ≡

Pour ça, on utilise la seule technique connue efficace : le passage à la réduction parallèle.

D'abord, pour la modularité, on paramètre dorénavant toutes les relations par une conversion de type abstraite ≤T, pour la modularité au moins.

Ensuite, on définit ≡> la réduction parallèle (1 étape) qui contient :
- règles de réduction
- congruence syntaxique (pure) (donc réflexivité sur les biens-typés)

l'η-expansion parallèle ≡>η qui contient :
- η-expansion
- congruence syntaxique (pure) (donc réflexivité sur les biens-typés)

l'égalité syntaxique ⩵ qui contient :
- effacement des casts
- comparaison d'univers (dirigé)
- ignorement des annotations de types (sauf à garantir le typage)
- congruence syntaxique (donc réflexivité sur les biens-typés)


la comparaison par joignabilité ≣ qui contient :
- stable par anti-réduction ≡> de chaque côté
- stable par anti-η-expansion ≡>η de chaque côté
- inclut ⩵


Lemmes d'inclusion :
- ≡ -> ≣ : Grâce à la transitivité de ≣
- ≣ -> ≡ : Par standardisation de la réduction ≡> / ≡>η [Claim : plus facile que la transitivité]



Encore une fois, on se ramène à une preuve de transitivité

# Nouvel objectif principal : prouver la transitivité de ≣

Ici, on peut découper les étapes de façon claire :
- (1) Confluence (forte) de ≡> (avec diagonale)
- (2) Bisimulation (forte) entre ≡> et ≡>η
- (3) Confluence (forte) de ≡>η modulo ⩵ (avec diagonales)
- (4) Transitivité de ⩵
- (5) Bisimulation (forte) entre ≡> et ⩵
- (6) Bisimulation (forte) entre ≡>η et ⩵


## (1) Confluence de ≡>

Il se passe déjà beaucoup de choses ici:

On découpe l'opération en trois étapes : gluement des deux réductions en un seul inductif, construction du terme qui clos le diamant et construction des dérivations vers ce terme

Déjà, on n'a pas d'autre possibilité que de préserver l'égalité des types (sans quoi je ne sais pas quoi donner comme types aux réductions construites). Donc, on a besoin d'un typage avec principalité du type. (C'est la seule difficulté pour le gluement)

La construction du terme (et éventuellement du type) est facile, fonction des deux dérivations de départ (gluées).

La principale difficulté réside dans la construction des dérivations de réductions :
- pour les rédexes, la réduction doit être substitutive (`Γ , A ⊢ t ≡> t'  &  Γ ⊢ u ≡> u' : A  ->  Γ ⊢ t { u } ≡> t' { u' }`) avec `u ≡> u'` qui checke (potentiellement) contre `A`. Par projection à gauche ça implique notamment que le typage soit lui aussi substitutif avec des substitutions qui checkent.
- pour la projection à droite, il faut se demander à quel point les types sont préservés par la réduction
    + Préservation de tous les types principaux : impossible avec un seul type (ex: `tCast c ty ≡> tCast c' ty'`, type principal `ty` puis `ty'`)
    + Préservation des types checks : la conversion de type est stable par réduction et antiréduction à droite (cf. ex. `tCast`, `c' : ty : ty' : ty` (1)IH (2)Hyp rtypage (3)Préservation), stable par réduction à gauche (chgmnt de contexte dans un `tLambda` notamment), et aussi stable par réduction dans les domains (`ΠA, B ≤T ΠA', B'`, presque de l'antiréduction à droite)
    + Aucune préservation des types : quels types donner aux réductions construites


Examinons maintenant nos possibilités sur les dérivations de typage, qui vont imposer d'autres propriétés à la conversion de type.
- Dérivation bidirectionnelle : principalité facile, mais substitutivité uniquement par des trucs qui infèrent le bon type par défaut. Pour substituer des trucs qui checkent, on atterit aussi en mode check et on a besoin de plus de propriétés de la conversion de type : construction de conversion de produits, transitivité, inversion forte sur les constructeurs de types
- Dérivation normale : On peut obtenir la principalité par annotation des termes qui ne semblent pas poser de problème théorique outre mesure; substitutivité facile (gratuit pour les trucs qui infèrent, perd quand même la pricipalité pour les trucs qui checkent); on se retrouve à travailler avec la clotûre réflexive transitive de la conversion de type lors d'inversions, d'où la dérivation suivante
- Dérivation contrainte : Même que ci-dessus, mais on force les sous-termes à avoir exactement une conversion de types. On prend la clotûre réflexive transitive de ci-dessus. La substitutivité est gratuite pour les trucs qui infèrent, mais requiert maintenant réflexivité et transitivité de la conversion de types en perdant toujours la principalité pour le check.


On a parlé de termes annotés, il faut observer la chose suivante :
- pour la projection à droite des rédexes, quand les termes sont annotés, on se retrouve avec un `ΠA₀, B₀ ≤T ΠA₁, B₁` (ou similaire pour iota) qui doit être inversé. Deux possibilités :
    + on peut toujours inverser les produits (injection sur les constructeurs de types)
    + on suppose localement que le produit est inversible. Dans ce cas, l'hypothèse locale doit pouvoir être transportée le long de la deuxième réduction, donc la conversion de type est stable par réduction des deux côtés


On se retrouve avec plusieurs propriétés souhaitées pour la conversion de type :
- Réflexivité
- Transitivité
- Congruence syntaxique sur les constructeurs de type (inclut la substitution)
- Stabilité par réduction et/ou antiréduction
- Injectivité sur les constructeurs de type


Cependant, il n'est pas envisageable de supposer l'existence d'une conversion de type ayant toutes ces propriétés, vu que c'est ce que l'on cherche déjà à construire (par exemple, ≅ ne vérifie pas l'injectivité sur les constructeurs de type et ≡ pas la transitivité).
Même à faire une récurrence, vu qu'on a besoin d'utiliser toutes les propriétés de manière répétée et arbitraire, je ne vois pas comment ça passe.

Il faut maintenant sacrifier l'une de ces propriétés au moins :
- Réflexivité : impossible de faire des substitutions en mode check
- Transitivité : impossible de faire des substitutions en mode check. Impossible de faire la substitution pour le beta redex (sauf à ...)
- Congruence syntaxique sur les constructeurs de type : impossible de faire des substitutions en mode check pour les dérivations bidirectionnelles
- Stabilité par réduction et/ou antiréduction : Impossible de faire des changements de type ou de contexte motivés par la réduction
- Injectivité sur les constructeurs de type : Doit annoter les betas et transporter ces annotations. La version faible (non-confusion) est absolument requise pour la bisimulation ≡> / ≡>η









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
