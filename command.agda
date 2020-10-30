open import prelude
open import data-model using ( DataModel )

module command (DM : DataModel) where

  open DataModel DM

  data Command : Set where

    skip : Command
    _∙_ : Command → Command → Command
    if_then_ : Formula → Command → Command
    [_]:=_ : Address → Expression → Command
    _:=[_] : Register → Address → Command
    _:=_ : Register → Expression → Command
    
