# Contents

* **Wna.Primitive** -- Agda.Primitive with renaming 
* **Wna.Prelude(.\*)** -- reexported frequently used definitions from this library and stdlib.
* **Wna.Monad.\*** -- concrete monads.
* **Wna.Class.\*** -- classes for use with instance arguments.
* **Wna.Foreign.Haskell.\*** -- ffi with haskell.

# Dependencies

* Agda 2.6.2.1
* standard-library-2.0

# Naming

## Classes

Bundles are named according to their type, camelCase (ex. ```rawIMonad```, ```imonad```); or prefixed with typename-dash to avoid name collisions.

## Monads

Indexed monads are prefixed with ```I``` (ex. ```IState```), like in standard library.

Type of transformer -- ```MonT```.
Proof that for any ```Monad M```, ```MonT M``` is also a ```Monad``` -- ```MonadT```.
Transformer from monad to indexed monad (transformer's monad is indexed, transformed monad is not) -- ```MonTI``` (```MonadTI```, ```RawMonadTI```).
Transformer from indexed monad to indexed monad (transformed is indexed, transformer's is not) -- ```MonIT``` (```MonadIT```, ```RawMonadIT```).

```IReaderT``` from standard library is from indexed to indexed; ```IStateT``` is from non-indexed to indexed.
In this library corresponding transformers are named ```ReaderIT``` and ```StateTI```.
```StateIT``` is a transformer from indexed monad to indexed monad.

# Notes
