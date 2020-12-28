# tml

Requirements:
- [Miking](https://github.com/miking-lang/miking/tree/develop) built with Python integration

Usage:
- `run/test (TSA|SYNC|CTRL|CTRL_SYNC) [--quiet | --write] <tests>`
- `run/test-all [--quiet | --write]`

Options:
- `--quiet`: Suppress test output
- `--write`: Write test output to reference file

# Language definition

EBNF variant: <https://www.w3.org/TR/REC-xml/#sec-notation>

## Shared base

```
Program          ::= statement*

statement        ::= location | edge | default

location         ::= "init"? locationSelector property*
default          ::= locationDefault | edgeDefault

locationSelector ::= id | "[" id ("," id)* "]"

locationDefault  ::= "default" "location" property*
edgeDefault      ::= "default" "edge" property*

property         ::= invar | guard | action | reset

invar            ::= "invar" ("!" | "{" invarExpr "}")
guard            ::= "guard" ("!" | "{" guardExpr "}")
reset            ::= "reset" ("!" | "{" clocks "}")

invarExpr        ::= invarConjunct ("&" invarConjunct)*
invarConjunct    ::= id ("<=" | "<") nat

guardExpr        ::= guardConjunct ("&" guardConjunct)*
guardConjunct    ::= (id op nat) | (id "-" id op nat)
op               ::= "<=" | "<" | "==" | ">" | ">="

clocks           ::= id ("," id)*

id               ::= (letter | "_") (letter | "_" | digit)*
letter           ::= [a-zA-Z]
digit            ::= [0-9]
nat              ::= [1-9] digit*
```

Validity constraints:
- Exactly one initial location.
- Properties on a location (or location default) must be invar.
- Properties on an edge (or edge default) must be guard, action, or reset.
- A statement has at most one of each type of property.

Evaluation rules:
- Default statements define properties which apply to all following location/edge statements.
- Properties defined in location/edge statements have precedence over defaults.
- Multiple statements `s1`, `s2`, ... `sn` referencing the same location/edge are allowed. For every `sx`, `sy` where `y > x`, properites in `sy` have precedence over properties in `sx`.
    - This also applies to default statements.

## TSA, SYNC

```
edge ::= locationSelector ("->" locationSelector)+ property*
```

## CTRL

```
edge ::= locationSelector (("->" | ">>") locationSelector)+ property*
```

## TSA, CTRL

```
action ::= "action" ("!" | "{" id "}")
```

## SYNC, CTRL_SYNC

```
action ::= "sync" ("!" | "{" id ("!" | "?") "}")
```
