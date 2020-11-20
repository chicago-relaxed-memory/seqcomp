open import prelude
open import data-model using ( DataModel )

module command (DM : DataModel) where

  infixr 10 _∙_ _∥_
  
  open DataModel DM

  data Command : Set
  data ThreadGroup : Set

  data Command where

    skip : Command
    _∙_ : Command → Command → Command
    if_then_else_ : Formula → Command → Command → Command
    [_]:=_ : Address → Expression → Command
    _:=[_] : Register → Address → Command
    _:=_ : Register → Expression → Command
    fork_join : ThreadGroup → Command
    
  data ThreadGroup where

    nil : ThreadGroup
    thread : Command → ThreadGroup
    _∥_ : ThreadGroup → ThreadGroup → ThreadGroup
