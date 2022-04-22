# Contents

* **Wna.Primitive** -- Agda.Primitive with renaming 
* **Wna.Monad.\*** -- concrete monads.
* **Wna.Class.\*** -- classes for use with instance arguments.

Modules with paths coinciding with standard library ones contain additional related definitions.

# Dependencies

* Agda 2.6.2.1
* standard-library-2.0

# Naming

## Monads

Indexed monads are prefixed with ```I``` (ex. ```IState```), like in standard library.
Instances of records are named according to their type, camelCase (ex. ```rawIMonad```, ```imonad```).
Level polymorphic variants are suffixed with ```′```.

Type of transformer -- ```MonT```.
Proof that for any ```Monad M```, ```MonT M``` is also a ```Monad``` -- ```MonadT```.
Transformer from monad to indexed monad (transformer's monad is indexed, transformed monad is not) -- ```MonTI``` (```MonadTI```, ```RawMonadTI```).
Transformer from indexed monad to indexed monad (transformed is indexed, transformer's is not) -- ```MonIT``` (```MonadIT```, ```RawMonadIT```).

```IReaderT``` from standard library is from indexed to indexed; ```IStateT``` is from non-indexed to indexed.
In this library corresponding transformers are named ```ReaderIT``` and ```StateTI```.
```StateIT``` is a transformer from indexed monad to indexed monad.

# Notes

Default implementations of raws' functions are in ```MakeRaw*``` modules.
Passing F ((I)Fun, the functor itself) explicitly to ```MakeRaw*```'s functions may help Agda to infer indices (?).
