module data-model where

  record DataModel : Set₁ where
  
    field Value : Set
    field Register : Set
    field Expression : Set
    field Formula : Set
    field Address : Set

    field _⊨_ : Formula → Formula → Set

    field _∨_ : Formula → Formula → Formula

    

