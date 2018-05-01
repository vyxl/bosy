Notes on BoSy
Brian Heim
2018-04-26

made with `make all`

in main directory:
use `./bosh.sh --synthesize Samples/simple_arbiter.bosy`

XXX
.bosy but is really .json

---

get options with --help
`./bosy.sh --synthesize --target verilog Samples/simple_arbiter.bosy`
`./bosy.sh --synthesize --target verilog --backend smt --solver z3 Samples/simple_arbiter.bosy`

output:

.build/x86_64-apple-macosx10.10/release/BoSy [options] instance

 options:
   --help		show this help and exit
   --verbose		show verbose output
   --synthesize		construct AIGER solution after realizability
   --statistics		display solving statistics
   --strategy linear|exponential
   --player both|system|environment
   --backend explicit|input-symbolic|state-symbolic|symbolic|smt
   --semantics mealy|moore
   --automaton-tool ltl3ba|spot
   --target aiger|dot|dot-topology|smv|verilog|all
   --solver picosat|cryptominisat|rareqs|depqbf|cadet|caqe|quabs|idq|hqs|eprover|vampire|z3|cvc4
   --qbf-certifier cadet|caqe|quabs
   --syntcomp2017-rules	 disable construction of environment counter-strategies

---

solvers: found in Sources/Logic/Solver.swift
picosat - doesn't appear to support bounded synthesis
cryptominisat - in Sources/BoundedSynthesis/SolutionSearch.swift
rareqs - is for qbf
depqbf - for qbf
cadet - qbf
caqe - qbf
quabs - qbf
idq - dqbf
hqs - ??
eprover - theorem prover - more info? - FOL
vampire
z3 - from MSFT, looks p good
cvc4 - smt solver

---

Sources/Logic/Solver is gud

SmtSolver
GenericSmtSolver (line 764) is class of interest
solve() func (line 791)

---

Sources/BoundedSynthesis/SolutionSearch
hasSolution - increases bound until solution is found
getSolution - calls extractSolution

these are called from main!

extractSolution => calls backend
i want the smt backend so go to BoundedSynthesis/SmtEncoding
which then calls solver.getValue (GenericSmtSolver)

can find all models
https://stackoverflow.com/questions/13395391/z3-finding-all-satisfying-models
https://stackoverflow.com/questions/11867611/z3py-checking-all-solutions-for-equation
https://stackoverflow.com/questions/33738333/how-to-retrieve-all-satisfying-assignments-in-smtlib2

---

I was going to
( get z3 via clone, build with python bindings )
but then i realized I could

download release
`cp *.dylib /usr/local/lib`
now works with p3

---

z3py example:

```
from z3 import *

x = Int('x')
y = Int('y')
s = Solver()
s.add(x + y > 5, x + y < 10, x > 1, y > 1)
print(s.check())
m = s.model()
print(m)

def do_block(m):
    block = []
    for d in m:
        c = d()
        block.append(c != m[d])
    s.add(Or(block))
    print(s.check())
    return s

while s.check() == sat:
    m = s.model()
    print(m)
    s = do_block(m)
```

---

how to get a thing for a raw smt2 string:

```
from z3 import *

result = parse_smt2_string(
'''
<string>
'''
)
print(result)
s = Solver()
s.add(result)
print(s.check())
print(s.model())
```

---
but it's hard to negate things, sometimes
Mark said this was hard for him because it works like sets
interactive session with z3 showing how to do simple negation:

```
(declare-fun f (Bool) Bool)
(assert (f true))
(check-sat)
sat
(get-model)
(model
  (define-fun f ((x!0 Bool)) Bool
    (ite (= x!0 true) true
      true))
)
(assert (or (not (f true)) (not (f false))))
(check-sat)
sat
(get-model)
(model
  (define-fun f ((x!0 Bool)) Bool
    (ite (= x!0 true) true
    (ite (= x!0 false) false
      true)))
)
```

---

SolverFor!

---

once you have the model, an example model looks like this:

```
lambda_S4 = [else -> lambda_S4!276(k!268(Var(0)))]

>>> m[m[3]]
[else -> lambda_S4!276(k!268(Var(0)))]
>>> fi = m[m[3]]

>>> fi.num_entries()
0
>>> fi.else_value()
lambda_S4!276(k!268(Var(0)))
>>> type(fi.else_value())
<class 'z3.z3.BoolRef'>
>>> br = fi.else_value()
>>> br
lambda_S4!276(k!268(Var(0)))

>>> br.decl()
lambda_S4!276

>>> m[br.decl()]
[s0 -> False, else -> True]
>>> f2 = m[br.decl()]
>>> f2.entry(0)
[s0, False]
>>> type(f2.entry(0))
<class 'z3.z3.FuncEntry'>
>>> f2.entry(0).arg_value(0)
s0
>>> a2 = f2.entry(0).arg_value(0)
>>> type(a2)
<class 'z3.z3.DatatypeRef'>

>>> a2.sort()
S
>>> type(a2.sort())
<class 'z3.z3.DatatypeSortRef'>
>>> srt = a2.sort()
>>> srt.num_constructors()
4
>>> srt.constructor(0)
s0
>>> srt.constructor(0)().get_id() == a2.get_id()
True
>>> srt.constructor(1)().get_id() == a2.get_id()
False
```

---

sketch for algorithm to provide model negation:

real func = one without a name with a !

- for each real func
    - either consists of actual interpretations
    - or forwards to other function (o.w. failure)
    - get forwarded-to function
- types used in function must be
    - bool or datatype with no-arg constructors
- enumerate all possibilities and negate function results
- OR everything together and add to model

---

bosy outputs a counterexample model in the case of failure
with bad inputs

---

added an option --encoding-only to produce just the smt encoding

came up with a script to run bosy and then run my script to extract models
added a max number of models to produce

added robustness for checking that the thing was realizable

seems that checking player == .system doesn't mean it's unrealizable necessarily
not sure why.

fixed - check after getting solution

added debug ability to python script, shell script
