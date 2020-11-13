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

location        ::= "init"? id invar?

invar           ::= "invar {" invarExpr "}"
invarExpr       ::= invarConjunct ("&" invarConjunct)*
invarConjunct   ::= id ("<=" | "<") nat

edge            ::= id "->" id (guard | sync | reset)*

guard           ::= "guard {" guardExpr "}"
guardExpr       ::= guardConjunct ("&" guardConjunct)*
guardConjunct   ::= (id op nat) | (id "-" id op nat)
op              ::= "<=" | "<" | "==" | ">" | ">="

sync            ::= "sync {" action "}"
action          ::= id /* To be extended for communication */

reset           ::= "reset {" clocks "}"
clocks          ::= id ("," id)*

default         ::= locationDefault | edgeDefault
locationDefault ::= "default" "location" invar
edgeDefault     ::= "default" "edge" (guard | sync | reset)*

id              ::= (letter | "_") (letter | "_" | digit)*
letter          ::= [a-zA-Z]
digit           ::= [0-9]
nat             ::= [1-9] digit*
```

Semantic rules:
- Exactly one initial location
- At most one of each property per edge/edge default (guard, sync, reset)
- At most one default
- Local properties have precedence over defaults
- (todo): If there is a repeated location / edge definition, properties defined later have precedence
