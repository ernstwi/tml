# tml

Requirements:
- [Miking](https://github.com/miking-lang/miking/tree/develop) built with Python integration

Usage:
- `mi main.mc -- [--quiet | --write] <tests>`
    - `--quiet`: Suppress test output
    - `--write`: Write test output to reference file

Shortcuts:
- `make`: Run all functional tests
- `make quiet`: Run tests, suppress compiler output
- `make utest`: Run unit tests

## Language definition

EBNF variant: <https://www.w3.org/TR/REC-xml/#sec-notation>

```
Program         ::= (location | edge | default)*

location        ::= "init"? id property*
edge            ::= id "->" id property*
default         ::= locationDefault | edgeDefault

locationDefault ::= "default" "location" property*
edgeDefault     ::= "default" "edge" property*

property        ::= invar | guard | sync | reset

invar           ::= "invar {" invarExpr "}"
guard           ::= "guard {" guardExpr "}"
sync            ::= "sync {" action "}"
reset           ::= "reset {" clocks "}"

invarExpr       ::= invarConjunct ("&" invarConjunct)*
invarConjunct   ::= id ("<=" | "<") nat

guardExpr       ::= guardConjunct ("&" guardConjunct)*
guardConjunct   ::= (id op nat) | (id "-" id op nat)
op              ::= "<=" | "<" | "==" | ">" | ">="

action          ::= id /* To be extended for communication */

clocks          ::= id ("," id)*

id              ::= (letter | "_") (letter | "_" | digit)*
letter          ::= [a-zA-Z]
digit           ::= [0-9]
nat             ::= [1-9] digit*
```

Validity constraints:
- Exactly one initial location
- Properties on a location (or location default) must be invar
- Properties on an edge (or edge default) must be guard, sync, or reset

Semantic rules:
- Local properties have precedence over defaults
- If there is a repeated property, properties defined later have precedence
