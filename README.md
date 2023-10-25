# LogicLang
Lean 4 project by Matthew Richards

## Build instructions

Opening the root folder of the project, `lake build` should build the binaries at `./build/bin/logiclang`. 

The application can then be run on a specific file by using `./build/bin/logiclang`; for example, `./build/bin/logiclang ./Examples/valid_example1.logic` runs the program against one of the example files. 

## The language 

The language consists of three types of expressions: type definitions, function definitions, and assertions/constraints.

A type definition follows the grammar
```
enum <name> = <value> (| <value>)*;
```

A function definition follows the grammar
```
modifier := injective | ε
function := <modifier> fn <name> :: <domain> -> <range>;
```

where the domain and range of a function should be types as defined above.

Finally, assertions can be of any of the following formats:

```
value := <fnName>(<value>) | <literal>
logicalConnective := '∨' | '∧' | '->'
operator := '=' | '!='
assertion := ¬<assertion>; | <value> <operator> <value>; | <assertion> <logicalConnective> <assertion>;
```

Furthermore, comments can be written by beginning a line with `--`.

Examples can be found in the `./Examples` folder.

## Notes on the language 

- The `injective` function modifier ensures that the generated solution does not assign the same value twice in one function, that is, for any value in the range of a function, it only appears up to once in the solution table for that function. 

- The precendence of operators goes `->`, then `∨`, then `∧` is the weakest.