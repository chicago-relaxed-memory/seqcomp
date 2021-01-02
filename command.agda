open import prelude
open import data-model using (MemoryModel)

module command (Event : Set) (MM : MemoryModel(Event)) where

  infixr 10 _∙_ _∥_
  
  open MemoryModel MM
  open data-model(Event)

  data Command : Set
  data ThreadGroup : Set

  data Command where

    skip : Command
    _∙_ : Command → Command → Command
    if_then_else_ : Formula → Command → Command → Command
    [_]^_:=_ : Expression → AccessMode → Expression → Command
    _:=[_]^_ : Register → Expression → AccessMode → Command
    _:=_ : Register → Expression → Command
    fork : ThreadGroup → Command
    
  data ThreadGroup where

    nil : ThreadGroup
    thread : Command → ThreadGroup
    _∥_ : ThreadGroup → ThreadGroup → ThreadGroup
