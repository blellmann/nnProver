# nnProver

nnProver is a prototype implementation of proof search and countermodel construction for basic non-normal modal logics in the nested sequent framework.

The prover is based on the article [Combining monotone and normal modal logic in nested sequents -- with countermodels](https://mimamsa.logic.at/files/2019TABLEAUXNS4BiM.pdf) (published in TABLEAUX 2019).

You can also run the prover using a [web interface](http://subsell.logic.at/bprover/nnProver/).


## Usage

Formulae are built from the grammar

  Phi ::= atom | false | true | neg Phi | Phi and Phi | Phi or Phi | Phi -> Phi | ea Phi | aa Phi

where atom is any Prolog atom, e.g., p,q,r,...,a1,a2,a3,... The usual conventions about binding strength of the connectives apply, i.e., the unary connetives bind stronger than the binary ones, 'and' binds stronger than 'or' binds stronger than '->'.

To use the prover, make sure you have Prolog installed (e.g., [SWIPL](https://www.swi-prolog.org/)), then load nnprover.pl and run the prover with the command

  ?- prv( Formula, Axioms).

where Formula is a formula, e.g., p -> q or s, and Axioms is a list of additional axioms. So far these are:
- nea: neg ea false (equivalent to dea: neg(ea p and aa neg p))
- dae: aa p -> ea p
- daa: neg(aa p and aa neg p)

To see the output as a pdf, run latex or pdflatex on the file output.tex and view the resulting file in your favorite viewer (you might need to zoom in quite a bit for large derivations).

NOTE: In some cases the derivations might become too large for TeX to handle (if they are more than about 19 feet). In this case you might need to split the derivation produced in derivation.tex manually.

