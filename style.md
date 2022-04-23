something here

# Typeclasses

* Records are PascalCase, instances are of the same name but camelCase
* **\*.Instances** modules for instance declarations, **\*.Instanced** for opened (with {{...}}) records (if needed)

# Imports

* Sort ascending
* Always open (?)
* Line up usings, sort identifiers (upper case > lower case > symbols)
* Write explicit usings up to four elements instead of fully opening a module (exceptions: modules designed to be fully opened, ex. Wna.Primitive)
* as -> public -> using -> renaming -> hiding
* Publicly opened modules should go after all the others so they are easily seen